import V185TrunkScan21Chunk123

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1509956 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 5]
def baseStart_1509956 : Nat := 118140960795 + 1509956 * 2 ^ 59
def prefixEnd_1509956 : Nat := 4983230072969 + 3 ^ 40 * 1509956 * 2
def baseEnd_1509956 : Nat := 344592531173510899513709

theorem tailTrace_1509956 : CollatzResearch.WordTrace tailWord_1509956 prefixEnd_1509956 344592531173510899513709 := by
  unfold tailWord_1509956
  simp only [CollatzResearch.WordTrace]
  refine ⟨27536309858847383399518861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36715079811796511199358481 27536309858847383399518861)
  ·
    refine ⟨10326116197067768774819573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27536309858847383399518861 10326116197067768774819573)
    ·
      refine ⟨968073393475103322639335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10326116197067768774819573 968073393475103322639335)
      ·
        refine ⟨1452110090212654983959003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968073393475103322639335 1452110090212654983959003)
        ·
          refine ⟨2178165135318982475938505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452110090212654983959003 2178165135318982475938505)
          ·
            refine ⟨1633623851489236856953879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2178165135318982475938505 1633623851489236856953879)
            ·
              refine ⟨2450435777233855285430819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633623851489236856953879 2450435777233855285430819)
              ·
                refine ⟨3675653665850782928146229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450435777233855285430819 3675653665850782928146229)
                ·
                  refine ⟨344592531173510899513709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3675653665850782928146229 344592531173510899513709)
                  ·
                    rfl

theorem cell21_1509956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_1509956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1509956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1509956 prefixEnd_1509956 := by exact prefixLift 1509956
  have htrace : WordTrace (prefixWord ++ tailWord_1509956) baseStart_1509956 baseEnd_1509956 := by
    simpa [prefixWord, tailWord_1509956, baseEnd_1509956] using wordTrace_append hprefix tailTrace_1509956
  have hstable : (prefixWord ++ tailWord_1509956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509956).length < 2 ^ (prefixWord ++ tailWord_1509956).sum := by decide
  have hdescent : baseEnd_1509956 < baseStart_1509956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510018 : List Nat := [3, 4, 3, 1, 2, 1, 1, 6]
def baseStart_1510018 : Nat := 118140960795 + 1510018 * 2 ^ 59
def prefixEnd_1510018 : Nat := 4983230072969 + 3 ^ 40 * 1510018 * 2
def baseEnd_1510018 : Nat := 114868893472737523160083

theorem tailTrace_1510018 : CollatzResearch.WordTrace tailWord_1510018 prefixEnd_1510018 114868893472737523160083 := by
  unfold tailWord_1510018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13768720260867537846948677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36716587362313434258529805 13768720260867537846948677)
  ·
    refine ⟨2581635048912663346302877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13768720260867537846948677 2581635048912663346302877)
    ·
      refine ⟨968113143342248754863579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2581635048912663346302877 968113143342248754863579)
      ·
        refine ⟨1452169715013373132295369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968113143342248754863579 1452169715013373132295369)
        ·
          refine ⟨1089127286260029849221527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1452169715013373132295369 1089127286260029849221527)
          ·
            refine ⟨1633690929390044773832291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089127286260029849221527 1633690929390044773832291)
            ·
              refine ⟨2450536394085067160748437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633690929390044773832291 2450536394085067160748437)
              ·
                refine ⟨114868893472737523160083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2450536394085067160748437 114868893472737523160083)
                ·
                  rfl

theorem cell21_1510018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_1510018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510018 prefixEnd_1510018 := by exact prefixLift 1510018
  have htrace : WordTrace (prefixWord ++ tailWord_1510018) baseStart_1510018 baseEnd_1510018 := by
    simpa [prefixWord, tailWord_1510018, baseEnd_1510018] using wordTrace_append hprefix tailTrace_1510018
  have hstable : (prefixWord ++ tailWord_1510018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510018).length < 2 ^ (prefixWord ++ tailWord_1510018).sum := by decide
  have hdescent : baseEnd_1510018 < baseStart_1510018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510040 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_1510040 : Nat := 118140960795 + 1510040 * 2 ^ 59
def prefixEnd_1510040 : Nat := 4983230072969 + 3 ^ 40 * 1510040 * 2
def baseEnd_1510040 : Nat := 344611701117945420113537

theorem tailTrace_1510040 : CollatzResearch.WordTrace tailWord_1510040 prefixEnd_1510040 344611701117945420113537 := by
  unfold tailWord_1510040
  simp only [CollatzResearch.WordTrace]
  refine ⟨27537841724695224572547787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36717122299593632763397049 27537841724695224572547787)
  ·
    refine ⟨41306762587042836858821681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27537841724695224572547787 41306762587042836858821681)
    ·
      refine ⟨30980071940282127644116261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41306762587042836858821681 30980071940282127644116261)
      ·
        refine ⟨5808763488802898933271799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30980071940282127644116261 5808763488802898933271799)
        ·
          refine ⟨8713145233204348399907699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5808763488802898933271799 8713145233204348399907699)
          ·
            refine ⟨13069717849806522599861549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8713145233204348399907699 13069717849806522599861549)
            ·
              refine ⟨4901144193677445974948081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13069717849806522599861549 4901144193677445974948081)
              ·
                refine ⟨3675858145258084481211061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901144193677445974948081 3675858145258084481211061)
                ·
                  refine ⟨344611701117945420113537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3675858145258084481211061 344611701117945420113537)
                  ·
                    rfl

theorem cell21_1510040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_1510040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510040 prefixEnd_1510040 := by exact prefixLift 1510040
  have htrace : WordTrace (prefixWord ++ tailWord_1510040) baseStart_1510040 baseEnd_1510040 := by
    simpa [prefixWord, tailWord_1510040, baseEnd_1510040] using wordTrace_append hprefix tailTrace_1510040
  have hstable : (prefixWord ++ tailWord_1510040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510040).length < 2 ^ (prefixWord ++ tailWord_1510040).sum := by decide
  have hdescent : baseEnd_1510040 < baseStart_1510040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510071 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 6]
def baseStart_1510071 : Nat := 118140960795 + 1510071 * 2 ^ 59
def prefixEnd_1510071 : Nat := 4983230072969 + 3 ^ 40 * 1510071 * 2
def baseEnd_1510071 : Nat := 344618775740296255096807

theorem tailTrace_1510071 : CollatzResearch.WordTrace tailWord_1510071 prefixEnd_1510071 344618775740296255096807 := by
  unfold tailWord_1510071
  simp only [CollatzResearch.WordTrace]
  refine ⟨55076814112278141439474067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36717876074852094292982711 55076814112278141439474067)
  ·
    refine ⟨82615221168417212159211101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55076814112278141439474067 82615221168417212159211101)
    ·
      refine ⟨30980707938156454559704163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82615221168417212159211101 30980707938156454559704163)
      ·
        refine ⟨46471061907234681839556245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30980707938156454559704163 46471061907234681839556245)
        ·
          refine ⟨2178331026901625711229199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46471061907234681839556245 2178331026901625711229199)
          ·
            refine ⟨3267496540352438566843799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178331026901625711229199 3267496540352438566843799)
            ·
              refine ⟨4901244810528657850265699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267496540352438566843799 4901244810528657850265699)
              ·
                refine ⟨7351867215792986775398549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901244810528657850265699 7351867215792986775398549)
                ·
                  refine ⟨344618775740296255096807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7351867215792986775398549 344618775740296255096807)
                  ·
                    rfl

theorem cell21_1510071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_1510071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510071 prefixEnd_1510071 := by exact prefixLift 1510071
  have htrace : WordTrace (prefixWord ++ tailWord_1510071) baseStart_1510071 baseEnd_1510071 := by
    simpa [prefixWord, tailWord_1510071, baseEnd_1510071] using wordTrace_append hprefix tailTrace_1510071
  have hstable : (prefixWord ++ tailWord_1510071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510071).length < 2 ^ (prefixWord ++ tailWord_1510071).sum := by decide
  have hdescent : baseEnd_1510071 < baseStart_1510071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510088 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_1510088 : Nat := 118140960795 + 1510088 * 2 ^ 59
def prefixEnd_1510088 : Nat := 4983230072969 + 3 ^ 40 * 1510088 * 2
def baseEnd_1510088 : Nat := 344622655371908003313439

theorem tailTrace_1510088 : CollatzResearch.WordTrace tailWord_1510088 prefixEnd_1510088 344622655371908003313439 := by
  unfold tailWord_1510088
  simp only [CollatzResearch.WordTrace]
  refine ⟨27538717076608276671421459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36718289435477702228561945 27538717076608276671421459)
  ·
    refine ⟨41308075614912415007132189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27538717076608276671421459 41308075614912415007132189)
    ·
      refine ⟨15490528355592155627674571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41308075614912415007132189 15490528355592155627674571)
      ·
        refine ⟨23235792533388233441511857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15490528355592155627674571 23235792533388233441511857)
        ·
          refine ⟨17426844400041175081133893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23235792533388233441511857 17426844400041175081133893)
          ·
            refine ⟨3267533325007720327712605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17426844400041175081133893 3267533325007720327712605)
            ·
              refine ⟨1225324996877895122892227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3267533325007720327712605 1225324996877895122892227)
              ·
                refine ⟨1837987495316842684338341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225324996877895122892227 1837987495316842684338341)
                ·
                  refine ⟨344622655371908003313439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837987495316842684338341 344622655371908003313439)
                  ·
                    rfl

theorem cell21_1510088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_1510088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510088 prefixEnd_1510088 := by exact prefixLift 1510088
  have htrace : WordTrace (prefixWord ++ tailWord_1510088) baseStart_1510088 baseEnd_1510088 := by
    simpa [prefixWord, tailWord_1510088, baseEnd_1510088] using wordTrace_append hprefix tailTrace_1510088
  have hstable : (prefixWord ++ tailWord_1510088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510088).length < 2 ^ (prefixWord ++ tailWord_1510088).sum := by decide
  have hdescent : baseEnd_1510088 < baseStart_1510088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510212 : List Nat := [2, 3, 4, 2, 1, 1, 3, 5]
def baseStart_1510212 : Nat := 118140960795 + 1510212 * 2 ^ 59
def prefixEnd_1510212 : Nat := 4983230072969 + 3 ^ 40 * 1510212 * 2
def baseEnd_1510212 : Nat := 114883651287103781082173

theorem tailTrace_1510212 : CollatzResearch.WordTrace tailWord_1510212 prefixEnd_1510212 114883651287103781082173 := by
  unfold tailWord_1510212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27540978402383661260178445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36721304536511548346904593 27540978402383661260178445)
  ·
    refine ⟨10327866900893872972566917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27540978402383661260178445 10327866900893872972566917)
    ·
      refine ⟨1936475043917601182356297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10327866900893872972566917 1936475043917601182356297)
      ·
        refine ⟨1452356282938200886767223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1936475043917601182356297 1452356282938200886767223)
        ·
          refine ⟨2178534424407301330150835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452356282938200886767223 2178534424407301330150835)
          ·
            refine ⟨3267801636610951995226253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178534424407301330150835 3267801636610951995226253)
            ·
              refine ⟨1225425613729106998209845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3267801636610951995226253 1225425613729106998209845)
              ·
                refine ⟨114883651287103781082173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1225425613729106998209845 114883651287103781082173)
                ·
                  rfl

theorem cell21_1510212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_1510212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510212 prefixEnd_1510212 := by exact prefixLift 1510212
  have htrace : WordTrace (prefixWord ++ tailWord_1510212) baseStart_1510212 baseEnd_1510212 := by
    simpa [prefixWord, tailWord_1510212, baseEnd_1510212] using wordTrace_append hprefix tailTrace_1510212
  have hstable : (prefixWord ++ tailWord_1510212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510212).length < 2 ^ (prefixWord ++ tailWord_1510212).sum := by decide
  have hdescent : baseEnd_1510212 < baseStart_1510212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510251 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 5]
def baseStart_1510251 : Nat := 118140960795 + 1510251 * 2 ^ 59
def prefixEnd_1510251 : Nat := 4983230072969 + 3 ^ 40 * 1510251 * 2
def baseEnd_1510251 : Nat := 344659854192655942096439

theorem tailTrace_1510251 : CollatzResearch.WordTrace tailWord_1510251 prefixEnd_1510251 344659854192655942096439 := by
  unfold tailWord_1510251
  simp only [CollatzResearch.WordTrace]
  refine ⟨55083379251626032181026607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36722252834417354787351071 55083379251626032181026607)
  ·
    refine ⟨82625068877439048271539911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55083379251626032181026607 82625068877439048271539911)
    ·
      refine ⟨123937603316158572407309867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82625068877439048271539911 123937603316158572407309867)
      ·
        refine ⟨185906404974237858610964801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123937603316158572407309867 185906404974237858610964801)
        ·
          refine ⟨139429803730678393958223601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185906404974237858610964801 139429803730678393958223601)
          ·
            refine ⟨104572352798008795468667701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139429803730678393958223601 104572352798008795468667701)
            ·
              refine ⟨9803658074813324575187597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104572352798008795468667701 9803658074813324575187597)
              ·
                refine ⟨3676371778054996715695349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9803658074813324575187597 3676371778054996715695349)
                ·
                  refine ⟨344659854192655942096439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3676371778054996715695349 344659854192655942096439)
                  ·
                    rfl

theorem cell21_1510251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_1510251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510251 prefixEnd_1510251 := by exact prefixLift 1510251
  have htrace : WordTrace (prefixWord ++ tailWord_1510251) baseStart_1510251 baseEnd_1510251 := by
    simpa [prefixWord, tailWord_1510251, baseEnd_1510251] using wordTrace_append hprefix tailTrace_1510251
  have hstable : (prefixWord ++ tailWord_1510251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510251).length < 2 ^ (prefixWord ++ tailWord_1510251).sum := by decide
  have hdescent : baseEnd_1510251 < baseStart_1510251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510327 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 5]
def baseStart_1510327 : Nat := 118140960795 + 1510327 * 2 ^ 59
def prefixEnd_1510327 : Nat := 4983230072969 + 3 ^ 40 * 1510327 * 2
def baseEnd_1510327 : Nat := 344677198428096698829617

theorem tailTrace_1510327 : CollatzResearch.WordTrace tailWord_1510327 prefixEnd_1510327 344677198428096698829617 := by
  unfold tailWord_1510327
  simp only [CollatzResearch.WordTrace]
  refine ⟨55086151199350697160793235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36724100799567131440528823 55086151199350697160793235)
  ·
    refine ⟨82629226799026045741189853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55086151199350697160793235 82629226799026045741189853)
    ·
      refine ⟨30985960049634767152946195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82629226799026045741189853 30985960049634767152946195)
      ·
        refine ⟨46478940074452150729419293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30985960049634767152946195 46478940074452150729419293)
        ·
          refine ⟨17429602527919556523532235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46478940074452150729419293 17429602527919556523532235)
          ·
            refine ⟨26144403791879334785298353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17429602527919556523532235 26144403791879334785298353)
            ·
              refine ⟨19608302843909501088973765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26144403791879334785298353 19608302843909501088973765)
              ·
                refine ⟨3676556783233031454182581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19608302843909501088973765 3676556783233031454182581)
                ·
                  refine ⟨344677198428096698829617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3676556783233031454182581 344677198428096698829617)
                  ·
                    rfl

theorem cell21_1510327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_1510327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510327 prefixEnd_1510327 := by exact prefixLift 1510327
  have htrace : WordTrace (prefixWord ++ tailWord_1510327) baseStart_1510327 baseEnd_1510327 := by
    simpa [prefixWord, tailWord_1510327, baseEnd_1510327] using wordTrace_append hprefix tailTrace_1510327
  have hstable : (prefixWord ++ tailWord_1510327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510327).length < 2 ^ (prefixWord ++ tailWord_1510327).sum := by decide
  have hdescent : baseEnd_1510327 < baseStart_1510327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510361 : List Nat := [1, 2, 1, 2, 5, 2, 1, 4, 3]
def baseStart_1510361 : Nat := 118140960795 + 1510361 * 2 ^ 59
def prefixEnd_1510361 : Nat := 4983230072969 + 3 ^ 40 * 1510361 * 2
def baseEnd_1510361 : Nat := 344684957691320195262881

theorem tailTrace_1510361 : CollatzResearch.WordTrace tailWord_1510361 prefixEnd_1510361 344684957691320195262881 := by
  unfold tailWord_1510361
  simp only [CollatzResearch.WordTrace]
  refine ⟨55087391281227520967530937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36724927520818347311687291 55087391281227520967530937)
  ·
    refine ⟨41315543460920640725648203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55087391281227520967530937 41315543460920640725648203)
    ·
      refine ⟨61973315191380961088472305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41315543460920640725648203 61973315191380961088472305)
      ·
        refine ⟨46479986393535720816354229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61973315191380961088472305 46479986393535720816354229)
        ·
          refine ⟨4357498724393973826533209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46479986393535720816354229 4357498724393973826533209)
          ·
            refine ⟨3268124043295480369899907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4357498724393973826533209 3268124043295480369899907)
            ·
              refine ⟨4902186064943220554849861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268124043295480369899907 4902186064943220554849861)
              ·
                refine ⟨919159887176853854034349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4902186064943220554849861 919159887176853854034349)
                ·
                  refine ⟨344684957691320195262881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919159887176853854034349 344684957691320195262881)
                  ·
                    rfl

theorem cell21_1510361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_1510361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510361 prefixEnd_1510361 := by exact prefixLift 1510361
  have htrace : WordTrace (prefixWord ++ tailWord_1510361) baseStart_1510361 baseEnd_1510361 := by
    simpa [prefixWord, tailWord_1510361, baseEnd_1510361] using wordTrace_append hprefix tailTrace_1510361
  have hstable : (prefixWord ++ tailWord_1510361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510361).length < 2 ^ (prefixWord ++ tailWord_1510361).sum := by decide
  have hdescent : baseEnd_1510361 < baseStart_1510361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510372 : List Nat := [2, 3, 1, 1, 1, 1, 2, 10]
def baseStart_1510372 : Nat := 118140960795 + 1510372 * 2 ^ 59
def prefixEnd_1510372 : Nat := 4983230072969 + 3 ^ 40 * 1510372 * 2
def baseEnd_1510372 : Nat := 114895822680395540193175

theorem tailTrace_1510372 : CollatzResearch.WordTrace tailWord_1510372 prefixEnd_1510372 114895822680395540193175 := by
  unfold tailWord_1510372
  simp only [CollatzResearch.WordTrace]
  refine ⟨27543896242093834923090685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36725194989458446564120913 27543896242093834923090685)
  ·
    refine ⟨10328961090785188096159007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27543896242093834923090685 10328961090785188096159007)
    ·
      refine ⟨15493441636177782144238511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10328961090785188096159007 15493441636177782144238511)
      ·
        refine ⟨23240162454266673216357767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15493441636177782144238511 23240162454266673216357767)
        ·
          refine ⟨34860243681400009824536651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23240162454266673216357767 34860243681400009824536651)
          ·
            refine ⟨52290365522100014736804977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34860243681400009824536651 52290365522100014736804977)
            ·
              refine ⟨39217774141575011052603733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52290365522100014736804977 39217774141575011052603733)
              ·
                refine ⟨114895822680395540193175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39217774141575011052603733 114895822680395540193175)
                ·
                  rfl

theorem cell21_1510372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_1510372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510372 prefixEnd_1510372 := by exact prefixLift 1510372
  have htrace : WordTrace (prefixWord ++ tailWord_1510372) baseStart_1510372 baseEnd_1510372 := by
    simpa [prefixWord, tailWord_1510372, baseEnd_1510372] using wordTrace_append hprefix tailTrace_1510372
  have hstable : (prefixWord ++ tailWord_1510372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510372).length < 2 ^ (prefixWord ++ tailWord_1510372).sum := by decide
  have hdescent : baseEnd_1510372 < baseStart_1510372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510375 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 4]
def baseStart_1510375 : Nat := 118140960795 + 1510375 * 2 ^ 59
def prefixEnd_1510375 : Nat := 4983230072969 + 3 ^ 40 * 1510375 * 2
def baseEnd_1510375 : Nat := 344688152682059282029519

theorem tailTrace_1510375 : CollatzResearch.WordTrace tailWord_1510375 prefixEnd_1510375 344688152682059282029519 := by
  unfold tailWord_1510375
  simp only [CollatzResearch.WordTrace]
  refine ⟨55087901903176801358540579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36725267935451200905693719 55087901903176801358540579)
  ·
    refine ⟨82631852854765202037810869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55087901903176801358540579 82631852854765202037810869)
    ·
      refine ⟨7746736205134237691044769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82631852854765202037810869 7746736205134237691044769)
      ·
        refine ⟨5810052153850678268283577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7746736205134237691044769 5810052153850678268283577)
        ·
          refine ⟨4357539115388008701212683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5810052153850678268283577 4357539115388008701212683)
          ·
            refine ⟨6536308673082013051819025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357539115388008701212683 6536308673082013051819025)
            ·
              refine ⟨4902231504811509788864269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6536308673082013051819025 4902231504811509788864269)
              ·
                refine ⟨1838336814304316170824101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4902231504811509788864269 1838336814304316170824101)
                ·
                  refine ⟨344688152682059282029519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1838336814304316170824101 344688152682059282029519)
                  ·
                    rfl

theorem cell21_1510375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 4].length) (baseStart_1510375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510375 prefixEnd_1510375 := by exact prefixLift 1510375
  have htrace : WordTrace (prefixWord ++ tailWord_1510375) baseStart_1510375 baseEnd_1510375 := by
    simpa [prefixWord, tailWord_1510375, baseEnd_1510375] using wordTrace_append hprefix tailTrace_1510375
  have hstable : (prefixWord ++ tailWord_1510375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510375).length < 2 ^ (prefixWord ++ tailWord_1510375).sum := by decide
  have hdescent : baseEnd_1510375 < baseStart_1510375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510448 : List Nat := [2, 1, 1, 1, 2, 4, 3, 7]
def baseStart_1510448 : Nat := 118140960795 + 1510448 * 2 ^ 59
def prefixEnd_1510448 : Nat := 4983230072969 + 3 ^ 40 * 1510448 * 2
def baseEnd_1510448 : Nat := 114901604092209125770901

theorem tailTrace_1510448 : CollatzResearch.WordTrace tailWord_1510448 prefixEnd_1510448 114901604092209125770901 := by
  unfold tailWord_1510448
  simp only [CollatzResearch.WordTrace]
  refine ⟨27545282215956167412973999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36727042954608223217298665 27545282215956167412973999)
  ·
    refine ⟨41317923323934251119460999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27545282215956167412973999 41317923323934251119460999)
    ·
      refine ⟨61976884985901376679191499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41317923323934251119460999 61976884985901376679191499)
      ·
        refine ⟨92965327478852065018787249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61976884985901376679191499 92965327478852065018787249)
        ·
          refine ⟨69723995609139048764090437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92965327478852065018787249 69723995609139048764090437)
          ·
            refine ⟨13073249176713571643266957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69723995609139048764090437 13073249176713571643266957)
            ·
              refine ⟨4902468441267589366225109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13073249176713571643266957 4902468441267589366225109)
              ·
                refine ⟨114901604092209125770901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4902468441267589366225109 114901604092209125770901)
                ·
                  rfl

theorem cell21_1510448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_1510448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510448 prefixEnd_1510448 := by exact prefixLift 1510448
  have htrace : WordTrace (prefixWord ++ tailWord_1510448) baseStart_1510448 baseEnd_1510448 := by
    simpa [prefixWord, tailWord_1510448, baseEnd_1510448] using wordTrace_append hprefix tailTrace_1510448
  have hstable : (prefixWord ++ tailWord_1510448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510448).length < 2 ^ (prefixWord ++ tailWord_1510448).sum := by decide
  have hdescent : baseEnd_1510448 < baseStart_1510448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510454 : List Nat := [5, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1510454 : Nat := 118140960795 + 1510454 * 2 ^ 59
def prefixEnd_1510454 : Nat := 4983230072969 + 3 ^ 40 * 1510454 * 2
def baseEnd_1510454 : Nat := 344706181558372700212691

theorem tailTrace_1510454 : CollatzResearch.WordTrace tailWord_1510454 prefixEnd_1510454 344706181558372700212691 := by
  unfold tailWord_1510454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443173954368162365666651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36727188846593731900444277 3443173954368162365666651)
  ·
    refine ⟨5164760931552243548499977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3443173954368162365666651 5164760931552243548499977)
    ·
      refine ⟨3873570698664182661374983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5164760931552243548499977 3873570698664182661374983)
      ·
        refine ⟨5810356047996273992062475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873570698664182661374983 5810356047996273992062475)
        ·
          refine ⟨8715534071994410988093713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5810356047996273992062475 8715534071994410988093713)
          ·
            refine ⟨6536650553995808241070285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8715534071994410988093713 6536650553995808241070285)
            ·
              refine ⟨2451243957748428090401357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6536650553995808241070285 2451243957748428090401357)
              ·
                refine ⟨919216484155660533900509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2451243957748428090401357 919216484155660533900509)
                ·
                  refine ⟨344706181558372700212691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919216484155660533900509 344706181558372700212691)
                  ·
                    rfl

theorem cell21_1510454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1510454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510454 prefixEnd_1510454 := by exact prefixLift 1510454
  have htrace : WordTrace (prefixWord ++ tailWord_1510454) baseStart_1510454 baseEnd_1510454 := by
    simpa [prefixWord, tailWord_1510454, baseEnd_1510454] using wordTrace_append hprefix tailTrace_1510454
  have hstable : (prefixWord ++ tailWord_1510454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510454).length < 2 ^ (prefixWord ++ tailWord_1510454).sum := by decide
  have hdescent : baseEnd_1510454 < baseStart_1510454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510724 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_1510724 : Nat := 118140960795 + 1510724 * 2 ^ 59
def prefixEnd_1510724 : Nat := 4983230072969 + 3 ^ 40 * 1510724 * 2
def baseEnd_1510724 : Nat := 344767799236912230712139

theorem tailTrace_1510724 : CollatzResearch.WordTrace tailWord_1510724 prefixEnd_1510724 344767799236912230712139 := by
  unfold tailWord_1510724
  simp only [CollatzResearch.WordTrace]
  refine ⟨27550315489456216981497613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36733753985941622641996817 27550315489456216981497613)
  ·
    refine ⟨10331368308546081368061605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27550315489456216981497613 10331368308546081368061605)
    ·
      refine ⟨1937131557852390256511551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10331368308546081368061605 1937131557852390256511551)
      ·
        refine ⟨2905697336778585384767327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937131557852390256511551 2905697336778585384767327)
        ·
          refine ⟨4358546005167878077150991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905697336778585384767327 4358546005167878077150991)
          ·
            refine ⟨6537819007751817115726487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358546005167878077150991 6537819007751817115726487)
            ·
              refine ⟨9806728511627725673589731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6537819007751817115726487 9806728511627725673589731)
              ·
                refine ⟨14710092767441588510384597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806728511627725673589731 14710092767441588510384597)
                ·
                  refine ⟨344767799236912230712139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14710092767441588510384597 344767799236912230712139)
                  ·
                    rfl

theorem cell21_1510724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_1510724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510724 prefixEnd_1510724 := by exact prefixLift 1510724
  have htrace : WordTrace (prefixWord ++ tailWord_1510724) baseStart_1510724 baseEnd_1510724 := by
    simpa [prefixWord, tailWord_1510724, baseEnd_1510724] using wordTrace_append hprefix tailTrace_1510724
  have hstable : (prefixWord ++ tailWord_1510724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510724).length < 2 ^ (prefixWord ++ tailWord_1510724).sum := by decide
  have hdescent : baseEnd_1510724 < baseStart_1510724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510741 : List Nat := [1, 3, 2, 2, 3, 2, 2, 3, 3]
def baseStart_1510741 : Nat := 118140960795 + 1510741 * 2 ^ 59
def prefixEnd_1510741 : Nat := 4983230072969 + 3 ^ 40 * 1510741 * 2
def baseEnd_1510741 : Nat := 344771678868523978928771

theorem tailTrace_1510741 : CollatzResearch.WordTrace tailWord_1510741 prefixEnd_1510741 344771678868523978928771 := by
  unfold tailWord_1510741
  simp only [CollatzResearch.WordTrace]
  refine ⟨55101251019850845866364077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36734167346567230577576051 55101251019850845866364077)
  ·
    refine ⟨20662969132444067199886529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55101251019850845866364077 20662969132444067199886529)
    ·
      refine ⟨15497226849333050399914897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20662969132444067199886529 15497226849333050399914897)
      ·
        refine ⟨11622920136999787799936173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15497226849333050399914897 11622920136999787799936173)
        ·
          refine ⟨4358595051374920424976065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11622920136999787799936173 4358595051374920424976065)
          ·
            refine ⟨3268946288531190318732049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358595051374920424976065 3268946288531190318732049)
            ·
              refine ⟨2451709716398392739049037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3268946288531190318732049 2451709716398392739049037)
              ·
                refine ⟨919391143649397277143389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2451709716398392739049037 919391143649397277143389)
                ·
                  refine ⟨344771678868523978928771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919391143649397277143389 344771678868523978928771)
                  ·
                    rfl

theorem cell21_1510741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_1510741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510741 prefixEnd_1510741 := by exact prefixLift 1510741
  have htrace : WordTrace (prefixWord ++ tailWord_1510741) baseStart_1510741 baseEnd_1510741 := by
    simpa [prefixWord, tailWord_1510741, baseEnd_1510741] using wordTrace_append hprefix tailTrace_1510741
  have hstable : (prefixWord ++ tailWord_1510741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510741).length < 2 ^ (prefixWord ++ tailWord_1510741).sum := by decide
  have hdescent : baseEnd_1510741 < baseStart_1510741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510752 : List Nat := [2, 1, 1, 3, 4, 2, 8]
def baseStart_1510752 : Nat := 118140960795 + 1510752 * 2 ^ 59
def prefixEnd_1510752 : Nat := 4983230072969 + 3 ^ 40 * 1510752 * 2
def baseEnd_1510752 : Nat := 38308243246487822693935

theorem tailTrace_1510752 : CollatzResearch.WordTrace tailWord_1510752 prefixEnd_1510752 38308243246487822693935 := by
  unfold tailWord_1510752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27550826111405497372507255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36734434815207329830009673 27550826111405497372507255)
  ·
    refine ⟨41326239167108246058760883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27550826111405497372507255 41326239167108246058760883)
    ·
      refine ⟨61989358750662369088141325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41326239167108246058760883 61989358750662369088141325)
      ·
        refine ⟨23246009531498388408052997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61989358750662369088141325 23246009531498388408052997)
        ·
          refine ⟨4358626787155947826509937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23246009531498388408052997 4358626787155947826509937)
          ·
            refine ⟨3268970090366960869882453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358626787155947826509937 3268970090366960869882453)
            ·
              refine ⟨38308243246487822693935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3268970090366960869882453 38308243246487822693935)
              ·
                rfl

theorem cell21_1510752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 8].length) (baseStart_1510752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510752 prefixEnd_1510752 := by exact prefixLift 1510752
  have htrace : WordTrace (prefixWord ++ tailWord_1510752) baseStart_1510752 baseEnd_1510752 := by
    simpa [prefixWord, tailWord_1510752, baseEnd_1510752] using wordTrace_append hprefix tailTrace_1510752
  have hstable : (prefixWord ++ tailWord_1510752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510752).length < 2 ^ (prefixWord ++ tailWord_1510752).sum := by decide
  have hdescent : baseEnd_1510752 < baseStart_1510752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510755 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 4]
def baseStart_1510755 : Nat := 118140960795 + 1510755 * 2 ^ 59
def prefixEnd_1510755 : Nat := 4983230072969 + 3 ^ 40 * 1510755 * 2
def baseEnd_1510755 : Nat := 344774873859263065695409

theorem tailTrace_1510755 : CollatzResearch.WordTrace tailWord_1510755 prefixEnd_1510755 344774873859263065695409 := by
  unfold tailWord_1510755
  simp only [CollatzResearch.WordTrace]
  refine ⟨55101761641800126257373719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36734507761200084171582479 55101761641800126257373719)
  ·
    refine ⟨82652642462700189386060579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55101761641800126257373719 82652642462700189386060579)
    ·
      refine ⟨123978963694050284079090869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82652642462700189386060579 123978963694050284079090869)
      ·
        refine ⟨11623027846317214132414769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123978963694050284079090869 11623027846317214132414769)
        ·
          refine ⟨8717270884737910599311077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11623027846317214132414769 8717270884737910599311077)
          ·
            refine ⟨1634488290888358237370827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8717270884737910599311077 1634488290888358237370827)
            ·
              refine ⟨2451732436332537356056241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634488290888358237370827 2451732436332537356056241)
              ·
                refine ⟨1838799327249403017042181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451732436332537356056241 1838799327249403017042181)
                ·
                  refine ⟨344774873859263065695409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1838799327249403017042181 344774873859263065695409)
                  ·
                    rfl

theorem cell21_1510755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 4].length) (baseStart_1510755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510755 prefixEnd_1510755 := by exact prefixLift 1510755
  have htrace : WordTrace (prefixWord ++ tailWord_1510755) baseStart_1510755 baseEnd_1510755 := by
    simpa [prefixWord, tailWord_1510755, baseEnd_1510755] using wordTrace_append hprefix tailTrace_1510755
  have hstable : (prefixWord ++ tailWord_1510755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510755).length < 2 ^ (prefixWord ++ tailWord_1510755).sum := by decide
  have hdescent : baseEnd_1510755 < baseStart_1510755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510786 : List Nat := [3, 4, 2, 1, 1, 2, 1, 7]
def baseStart_1510786 : Nat := 118140960795 + 1510786 * 2 ^ 59
def prefixEnd_1510786 : Nat := 4983230072969 + 3 ^ 40 * 1510786 * 2
def baseEnd_1510786 : Nat := 114927316160537966892893

theorem tailTrace_1510786 : CollatzResearch.WordTrace tailWord_1510786 prefixEnd_1510786 114927316160537966892893 := by
  unfold tailWord_1510786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775723076171954637938053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36735261536458545701168141 13775723076171954637938053)
  ·
    refine ⟨2582948076782241494613385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13775723076171954637938053 2582948076782241494613385)
    ·
      refine ⟨1937211057586681120960039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2582948076782241494613385 1937211057586681120960039)
      ·
        refine ⟨2905816586380021681440059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937211057586681120960039 2905816586380021681440059)
        ·
          refine ⟨4358724879570032522160089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905816586380021681440059 4358724879570032522160089)
          ·
            refine ⟨3269043659677524391620067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358724879570032522160089 3269043659677524391620067)
            ·
              refine ⟨4903565489516286587430101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269043659677524391620067 4903565489516286587430101)
              ·
                refine ⟨114927316160537966892893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4903565489516286587430101 114927316160537966892893)
                ·
                  rfl

theorem cell21_1510786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_1510786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510786 prefixEnd_1510786 := by exact prefixLift 1510786
  have htrace : WordTrace (prefixWord ++ tailWord_1510786) baseStart_1510786 baseEnd_1510786 := by
    simpa [prefixWord, tailWord_1510786, baseEnd_1510786] using wordTrace_append hprefix tailTrace_1510786
  have hstable : (prefixWord ++ tailWord_1510786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510786).length < 2 ^ (prefixWord ++ tailWord_1510786).sum := by decide
  have hdescent : baseEnd_1510786 < baseStart_1510786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510924 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 4]
def baseStart_1510924 : Nat := 118140960795 + 1510924 * 2 ^ 59
def prefixEnd_1510924 : Nat := 4983230072969 + 3 ^ 40 * 1510924 * 2
def baseEnd_1510924 : Nat := 344813441961756327378397

theorem tailTrace_1510924 : CollatzResearch.WordTrace tailWord_1510924 prefixEnd_1510924 344813441961756327378397 := by
  unfold tailWord_1510924
  simp only [CollatzResearch.WordTrace]
  refine ⟨27553962789093934060137913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36738617052125245413517217 27553962789093934060137913)
  ·
    refine ⟨20665472091820450545103435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27553962789093934060137913 20665472091820450545103435)
    ·
      refine ⟨30998208137730675817655153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20665472091820450545103435 30998208137730675817655153)
      ·
        refine ⟨23248656103298006863241365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30998208137730675817655153 23248656103298006863241365)
        ·
          refine ⟨1089780754842094071714439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23248656103298006863241365 1089780754842094071714439)
          ·
            refine ⟨1634671132263141107571659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089780754842094071714439 1634671132263141107571659)
            ·
              refine ⟨2452006698394711661357489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634671132263141107571659 2452006698394711661357489)
              ·
                refine ⟨1839005023796033746018117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452006698394711661357489 1839005023796033746018117)
                ·
                  refine ⟨344813441961756327378397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1839005023796033746018117 344813441961756327378397)
                  ·
                    rfl

theorem cell21_1510924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_1510924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510924 prefixEnd_1510924 := by exact prefixLift 1510924
  have htrace : WordTrace (prefixWord ++ tailWord_1510924) baseStart_1510924 baseEnd_1510924 := by
    simpa [prefixWord, tailWord_1510924, baseEnd_1510924] using wordTrace_append hprefix tailTrace_1510924
  have hstable : (prefixWord ++ tailWord_1510924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510924).length < 2 ^ (prefixWord ++ tailWord_1510924).sum := by decide
  have hdescent : baseEnd_1510924 < baseStart_1510924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510969 : List Nat := [1, 2, 1, 5, 1, 4, 1, 3, 3]
def baseStart_1510969 : Nat := 118140960795 + 1510969 * 2 ^ 59
def prefixEnd_1510969 : Nat := 4983230072969 + 3 ^ 40 * 1510969 * 2
def baseEnd_1510969 : Nat := 344823711574846249128305

theorem tailTrace_1510969 : CollatzResearch.WordTrace tailWord_1510969 prefixEnd_1510969 344823711574846249128305 := by
  unfold tailWord_1510969
  simp only [CollatzResearch.WordTrace]
  refine ⟨55109566863024840805663961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36739711242016560537109307 55109566863024840805663961)
  ·
    refine ⟨41332175147268630604247971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55109566863024840805663961 41332175147268630604247971)
    ·
      refine ⟨61998262720902945906371957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41332175147268630604247971 61998262720902945906371957)
      ·
        refine ⟨5812337130084651178722371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61998262720902945906371957 5812337130084651178722371)
        ·
          refine ⟨8718505695126976768083557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5812337130084651178722371 8718505695126976768083557)
          ·
            refine ⟨1634719817836308144015667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8718505695126976768083557 1634719817836308144015667)
            ·
              refine ⟨2452079726754462216023501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634719817836308144015667 2452079726754462216023501)
              ·
                refine ⟨919529897532923331008813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2452079726754462216023501 919529897532923331008813)
                ·
                  refine ⟨344823711574846249128305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919529897532923331008813 344823711574846249128305)
                  ·
                    rfl

theorem cell21_1510969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_1510969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1510969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1510969 prefixEnd_1510969 := by exact prefixLift 1510969
  have htrace : WordTrace (prefixWord ++ tailWord_1510969) baseStart_1510969 baseEnd_1510969 := by
    simpa [prefixWord, tailWord_1510969, baseEnd_1510969] using wordTrace_append hprefix tailTrace_1510969
  have hstable : (prefixWord ++ tailWord_1510969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510969).length < 2 ^ (prefixWord ++ tailWord_1510969).sum := by decide
  have hdescent : baseEnd_1510969 < baseStart_1510969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511073 : List Nat := [1, 2, 3, 3, 2, 2, 3, 5]
def baseStart_1511073 : Nat := 118140960795 + 1511073 * 2 ^ 59
def prefixEnd_1511073 : Nat := 4983230072969 + 3 ^ 40 * 1511073 * 2
def baseEnd_1511073 : Nat := 114949148597255059798253

theorem tailTrace_1511073 : CollatzResearch.WordTrace tailWord_1511073 prefixEnd_1511073 114949148597255059798253 := by
  unfold tailWord_1511073
  simp only [CollatzResearch.WordTrace]
  refine ⟨55113360054648066567449873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36742240036432044378299915 55113360054648066567449873)
  ·
    refine ⟨41335020040986049925587405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55113360054648066567449873 41335020040986049925587405)
    ·
      refine ⟨15500632515369768722095277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41335020040986049925587405 15500632515369768722095277)
      ·
        refine ⟨5812737193263663270785729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15500632515369768722095277 5812737193263663270785729)
        ·
          refine ⟨4359552894947747453089297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5812737193263663270785729 4359552894947747453089297)
          ·
            refine ⟨3269664671210810589816973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4359552894947747453089297 3269664671210810589816973)
            ·
              refine ⟨1226124251704053971181365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3269664671210810589816973 1226124251704053971181365)
              ·
                refine ⟨114949148597255059798253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1226124251704053971181365 114949148597255059798253)
                ·
                  rfl

theorem cell21_1511073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 5].length) (baseStart_1511073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511073 prefixEnd_1511073 := by exact prefixLift 1511073
  have htrace : WordTrace (prefixWord ++ tailWord_1511073) baseStart_1511073 baseEnd_1511073 := by
    simpa [prefixWord, tailWord_1511073, baseEnd_1511073] using wordTrace_append hprefix tailTrace_1511073
  have hstable : (prefixWord ++ tailWord_1511073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511073).length < 2 ^ (prefixWord ++ tailWord_1511073).sum := by decide
  have hdescent : baseEnd_1511073 < baseStart_1511073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511101 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 6]
def baseStart_1511101 : Nat := 118140960795 + 1511101 * 2 ^ 59
def prefixEnd_1511101 : Nat := 4983230072969 + 3 ^ 40 * 1511101 * 2
def baseEnd_1511101 : Nat := 344853835773243352928035

theorem tailTrace_1511101 : CollatzResearch.WordTrace tailWord_1511101 prefixEnd_1511101 344853835773243352928035 := by
  unfold tailWord_1511101
  simp only [CollatzResearch.WordTrace]
  refine ⟨55114381298546627349469157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36742920865697751566312771 55114381298546627349469157)
  ·
    refine ⟨10333946493477492628025467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55114381298546627349469157 10333946493477492628025467)
    ·
      refine ⟨15500919740216238942038201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10333946493477492628025467 15500919740216238942038201)
      ·
        refine ⟨11625689805162179206528651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15500919740216238942038201 11625689805162179206528651)
        ·
          refine ⟨17438534707743268809792977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11625689805162179206528651 17438534707743268809792977)
          ·
            refine ⟨13078901030807451607344733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17438534707743268809792977 13078901030807451607344733)
            ·
              refine ⟨4904587886552794352754275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13078901030807451607344733 4904587886552794352754275)
              ·
                refine ⟨7356881829829191529131413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4904587886552794352754275 7356881829829191529131413)
                ·
                  refine ⟨344853835773243352928035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7356881829829191529131413 344853835773243352928035)
                  ·
                    rfl

theorem cell21_1511101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_1511101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511101 prefixEnd_1511101 := by exact prefixLift 1511101
  have htrace : WordTrace (prefixWord ++ tailWord_1511101) baseStart_1511101 baseEnd_1511101 := by
    simpa [prefixWord, tailWord_1511101, baseEnd_1511101] using wordTrace_append hprefix tailTrace_1511101
  have hstable : (prefixWord ++ tailWord_1511101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511101).length < 2 ^ (prefixWord ++ tailWord_1511101).sum := by decide
  have hdescent : baseEnd_1511101 < baseStart_1511101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511146 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1511146 : Nat := 118140960795 + 1511146 * 2 ^ 59
def prefixEnd_1511146 : Nat := 4983230072969 + 3 ^ 40 * 1511146 * 2
def baseEnd_1511146 : Nat := 344864105386333274677943

theorem tailTrace_1511146 : CollatzResearch.WordTrace tailWord_1511146 prefixEnd_1511146 344864105386333274677943 := by
  unfold tailWord_1511146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13779005645845900008714323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36744015055589066689904861 13779005645845900008714323)
  ·
    refine ⟨20668508468768850013071485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13779005645845900008714323 20668508468768850013071485)
    ·
      refine ⟨7750690675788318754901807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20668508468768850013071485 7750690675788318754901807)
      ·
        refine ⟨11626036013682478132352711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7750690675788318754901807 11626036013682478132352711)
        ·
          refine ⟨17439054020523717198529067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11626036013682478132352711 17439054020523717198529067)
          ·
            refine ⟨26158581030785575797793601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17439054020523717198529067 26158581030785575797793601)
            ·
              refine ⟨19618935773089181848345201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26158581030785575797793601 19618935773089181848345201)
              ·
                refine ⟨14714201829816886386258901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19618935773089181848345201 14714201829816886386258901)
                ·
                  refine ⟨344864105386333274677943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14714201829816886386258901 344864105386333274677943)
                  ·
                    rfl

theorem cell21_1511146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1511146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511146 prefixEnd_1511146 := by exact prefixLift 1511146
  have htrace : WordTrace (prefixWord ++ tailWord_1511146) baseStart_1511146 baseEnd_1511146 := by
    simpa [prefixWord, tailWord_1511146, baseEnd_1511146] using wordTrace_append hprefix tailTrace_1511146
  have hstable : (prefixWord ++ tailWord_1511146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511146).length < 2 ^ (prefixWord ++ tailWord_1511146).sum := by decide
  have hdescent : baseEnd_1511146 < baseStart_1511146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511312 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_1511312 : Nat := 118140960795 + 1511312 * 2 ^ 59
def prefixEnd_1511312 : Nat := 4983230072969 + 3 ^ 40 * 1511312 * 2
def baseEnd_1511312 : Nat := 344901988847953874910937

theorem tailTrace_1511312 : CollatzResearch.WordTrace tailWord_1511312 prefixEnd_1511312 344901988847953874910937 := by
  unfold tailWord_1511312
  simp only [CollatzResearch.WordTrace]
  refine ⟨27561038550391105192700095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36748051400521473590266793 27561038550391105192700095)
  ·
    refine ⟨41341557825586657789050143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27561038550391105192700095 41341557825586657789050143)
    ·
      refine ⟨62012336738379986683575215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41341557825586657789050143 62012336738379986683575215)
      ·
        refine ⟨93018505107569980025362823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62012336738379986683575215 93018505107569980025362823)
        ·
          refine ⟨139527757661354970038044235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93018505107569980025362823 139527757661354970038044235)
          ·
            refine ⟨209291636492032455057066353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139527757661354970038044235 209291636492032455057066353)
            ·
              refine ⟨156968727369024341292799765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209291636492032455057066353 156968727369024341292799765)
              ·
                refine ⟨7357909095423015998099989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156968727369024341292799765 7357909095423015998099989)
                ·
                  refine ⟨344901988847953874910937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7357909095423015998099989 344901988847953874910937)
                  ·
                    rfl

theorem cell21_1511312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_1511312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511312 prefixEnd_1511312 := by exact prefixLift 1511312
  have htrace : WordTrace (prefixWord ++ tailWord_1511312) baseStart_1511312 baseEnd_1511312 := by
    simpa [prefixWord, tailWord_1511312, baseEnd_1511312] using wordTrace_append hprefix tailTrace_1511312
  have hstable : (prefixWord ++ tailWord_1511312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511312).length < 2 ^ (prefixWord ++ tailWord_1511312).sum := by decide
  have hdescent : baseEnd_1511312 < baseStart_1511312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511343 : List Nat := [1, 1, 2, 1, 2, 2, 6, 6]
def baseStart_1511343 : Nat := 118140960795 + 1511343 * 2 ^ 59
def prefixEnd_1511343 : Nat := 4983230072969 + 3 ^ 40 * 1511343 * 2
def baseEnd_1511343 : Nat := 114969687823434903298069

theorem tailTrace_1511343 : CollatzResearch.WordTrace tailWord_1511343 prefixEnd_1511343 114969687823434903298069 := by
  unfold tailWord_1511343
  simp only [CollatzResearch.WordTrace]
  refine ⟨55123207763669902679778683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36748805175779935119852455 55123207763669902679778683)
  ·
    refine ⟨82684811645504854019668025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55123207763669902679778683 82684811645504854019668025)
    ·
      refine ⟨62013608734128640514751019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82684811645504854019668025 62013608734128640514751019)
      ·
        refine ⟨93020413101192960772126529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62013608734128640514751019 93020413101192960772126529)
        ·
          refine ⟨69765309825894720579094897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93020413101192960772126529 69765309825894720579094897)
          ·
            refine ⟨52323982369421040434321173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69765309825894720579094897 52323982369421040434321173)
            ·
              refine ⟨2452686673566611270358805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52323982369421040434321173 2452686673566611270358805)
              ·
                refine ⟨114969687823434903298069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2452686673566611270358805 114969687823434903298069)
                ·
                  rfl

theorem cell21_1511343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 6].length) (baseStart_1511343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511343 prefixEnd_1511343 := by exact prefixLift 1511343
  have htrace : WordTrace (prefixWord ++ tailWord_1511343) baseStart_1511343 baseEnd_1511343 := by
    simpa [prefixWord, tailWord_1511343, baseEnd_1511343] using wordTrace_append hprefix tailTrace_1511343
  have hstable : (prefixWord ++ tailWord_1511343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511343).length < 2 ^ (prefixWord ++ tailWord_1511343).sum := by decide
  have hdescent : baseEnd_1511343 < baseStart_1511343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511394 : List Nat := [3, 3, 3, 1, 2, 2, 1, 6]
def baseStart_1511394 : Nat := 118140960795 + 1511394 * 2 ^ 59
def prefixEnd_1511394 : Nat := 4983230072969 + 3 ^ 40 * 1511394 * 2
def baseEnd_1511394 : Nat := 114973567455046651514701

theorem tailTrace_1511394 : CollatzResearch.WordTrace tailWord_1511394 prefixEnd_1511394 114973567455046651514701 := by
  unfold tailWord_1511394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781266971621284597471309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36750045257656758926590157 13781266971621284597471309)
  ·
    refine ⟨5167975114357981724051741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13781266971621284597471309 5167975114357981724051741)
    ·
      refine ⟨1937990667884243146519403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5167975114357981724051741 1937990667884243146519403)
      ·
        refine ⟨2906986001826364719779105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937990667884243146519403 2906986001826364719779105)
        ·
          refine ⟨2180239501369773539834329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2906986001826364719779105 2180239501369773539834329)
          ·
            refine ⟨1635179626027330154875747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2180239501369773539834329 1635179626027330154875747)
            ·
              refine ⟨2452769439040995232313621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635179626027330154875747 2452769439040995232313621)
              ·
                refine ⟨114973567455046651514701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2452769439040995232313621 114973567455046651514701)
                ·
                  rfl

theorem cell21_1511394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_1511394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511394 prefixEnd_1511394 := by exact prefixLift 1511394
  have htrace : WordTrace (prefixWord ++ tailWord_1511394) baseStart_1511394 baseEnd_1511394 := by
    simpa [prefixWord, tailWord_1511394, baseEnd_1511394] using wordTrace_append hprefix tailTrace_1511394
  have hstable : (prefixWord ++ tailWord_1511394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511394).length < 2 ^ (prefixWord ++ tailWord_1511394).sum := by decide
  have hdescent : baseEnd_1511394 < baseStart_1511394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511450 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_1511450 : Nat := 118140960795 + 1511450 * 2 ^ 59
def prefixEnd_1511450 : Nat := 4983230072969 + 3 ^ 40 * 1511450 * 2
def baseEnd_1511450 : Nat := 344933482328096301610655

theorem tailTrace_1511450 : CollatzResearch.WordTrace tailWord_1511450 prefixEnd_1511450 344933482328096301610655 := by
  unfold tailWord_1511450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781777593570564988480951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36751406916188173302615869 13781777593570564988480951)
  ·
    refine ⟨20672666390355847482721427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13781777593570564988480951 20672666390355847482721427)
    ·
      refine ⟨31008999585533771224082141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20672666390355847482721427 31008999585533771224082141)
      ·
        refine ⟨11628374844575164209030803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31008999585533771224082141 11628374844575164209030803)
        ·
          refine ⟨17442562266862746313546205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11628374844575164209030803 17442562266862746313546205)
          ·
            refine ⟨6540960850073529867579827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17442562266862746313546205 6540960850073529867579827)
            ·
              refine ⟨9811441275110294801369741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6540960850073529867579827 9811441275110294801369741)
              ·
                refine ⟨3679290478166360550513653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9811441275110294801369741 3679290478166360550513653)
                ·
                  refine ⟨344933482328096301610655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3679290478166360550513653 344933482328096301610655)
                  ·
                    rfl

theorem cell21_1511450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_1511450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511450 prefixEnd_1511450 := by exact prefixLift 1511450
  have htrace : WordTrace (prefixWord ++ tailWord_1511450) baseStart_1511450 baseEnd_1511450 := by
    simpa [prefixWord, tailWord_1511450, baseEnd_1511450] using wordTrace_append hprefix tailTrace_1511450
  have hstable : (prefixWord ++ tailWord_1511450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511450).length < 2 ^ (prefixWord ++ tailWord_1511450).sum := by decide
  have hdescent : baseEnd_1511450 < baseStart_1511450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511501 : List Nat := [1, 6, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1511501 : Nat := 118140960795 + 1511501 * 2 ^ 59
def prefixEnd_1511501 : Nat := 4983230072969 + 3 ^ 40 * 1511501 * 2
def baseEnd_1511501 : Nat := 344945121222931546260551

theorem tailTrace_1511501 : CollatzResearch.WordTrace tailWord_1511501 prefixEnd_1511501 344945121222931546260551 := by
  unfold tailWord_1511501
  simp only [CollatzResearch.WordTrace]
  refine ⟨55128970497097495664030357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36752646998064997109353571 55128970497097495664030357)
  ·
    refine ⟨2584170492051445109251423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55128970497097495664030357 2584170492051445109251423)
    ·
      refine ⟨3876255738077167663877135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584170492051445109251423 3876255738077167663877135)
      ·
        refine ⟨5814383607115751495815703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876255738077167663877135 5814383607115751495815703)
        ·
          refine ⟨8721575410673627243723555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5814383607115751495815703 8721575410673627243723555)
          ·
            refine ⟨13082363116010440865585333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8721575410673627243723555 13082363116010440865585333)
            ·
              refine ⟨1226471542125978831148625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13082363116010440865585333 1226471542125978831148625)
              ·
                refine ⟨919853656594484123361469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226471542125978831148625 919853656594484123361469)
                ·
                  refine ⟨344945121222931546260551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919853656594484123361469 344945121222931546260551)
                  ·
                    rfl

theorem cell21_1511501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1511501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511501 prefixEnd_1511501 := by exact prefixLift 1511501
  have htrace : WordTrace (prefixWord ++ tailWord_1511501) baseStart_1511501 baseEnd_1511501 := by
    simpa [prefixWord, tailWord_1511501, baseEnd_1511501] using wordTrace_append hprefix tailTrace_1511501
  have hstable : (prefixWord ++ tailWord_1511501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511501).length < 2 ^ (prefixWord ++ tailWord_1511501).sum := by decide
  have hdescent : baseEnd_1511501 < baseStart_1511501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511557 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 4]
def baseStart_1511557 : Nat := 118140960795 + 1511557 * 2 ^ 59
def prefixEnd_1511557 : Nat := 4983230072969 + 3 ^ 40 * 1511557 * 2
def baseEnd_1511557 : Nat := 344957901185887893327103

theorem tailTrace_1511557 : CollatzResearch.WordTrace tailWord_1511557 prefixEnd_1511557 344957901185887893327103 := by
  unfold tailWord_1511557
  simp only [CollatzResearch.WordTrace]
  refine ⟨55131012984894617228068925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36754008656596411485379283 55131012984894617228068925)
  ·
    refine ⟨20674129869335481460525847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55131012984894617228068925 20674129869335481460525847)
    ·
      refine ⟨31011194804003222190788771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20674129869335481460525847 31011194804003222190788771)
      ·
        refine ⟨46516792206004833286183157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31011194804003222190788771 46516792206004833286183157)
        ·
          refine ⟨4360949269312953120579671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46516792206004833286183157 4360949269312953120579671)
          ·
            refine ⟨6541423903969429680869507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360949269312953120579671 6541423903969429680869507)
            ·
              refine ⟨9812135855954144521304261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6541423903969429680869507 9812135855954144521304261)
              ·
                refine ⟨1839775472991402097744549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9812135855954144521304261 1839775472991402097744549)
                ·
                  refine ⟨344957901185887893327103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1839775472991402097744549 344957901185887893327103)
                  ·
                    rfl

theorem cell21_1511557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_1511557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511557 prefixEnd_1511557 := by exact prefixLift 1511557
  have htrace : WordTrace (prefixWord ++ tailWord_1511557) baseStart_1511557 baseEnd_1511557 := by
    simpa [prefixWord, tailWord_1511557, baseEnd_1511557] using wordTrace_append hprefix tailTrace_1511557
  have hstable : (prefixWord ++ tailWord_1511557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511557).length < 2 ^ (prefixWord ++ tailWord_1511557).sum := by decide
  have hdescent : baseEnd_1511557 < baseStart_1511557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511560 : List Nat := [2, 1, 3, 4, 1, 2, 1, 4, 3]
def baseStart_1511560 : Nat := 118140960795 + 1511560 * 2 ^ 59
def prefixEnd_1511560 : Nat := 4983230072969 + 3 ^ 40 * 1511560 * 2
def baseEnd_1511560 : Nat := 344958585826760554777097

theorem tailTrace_1511560 : CollatzResearch.WordTrace tailWord_1511560 prefixEnd_1511560 344958585826760554777097 := by
  unfold tailWord_1511560
  simp only [CollatzResearch.WordTrace]
  refine ⟨27565561201941874370214067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36754081602589165826952089 27565561201941874370214067)
  ·
    refine ⟨41348341802912811555321101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27565561201941874370214067 41348341802912811555321101)
    ·
      refine ⟨15505628176092304333245413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41348341802912811555321101 15505628176092304333245413)
      ·
        refine ⟨2907305283017307062483515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15505628176092304333245413 2907305283017307062483515)
        ·
          refine ⟨4360957924525960593725273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907305283017307062483515 4360957924525960593725273)
          ·
            refine ⟨3270718443394470445293955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360957924525960593725273 3270718443394470445293955)
            ·
              refine ⟨4906077665091705667940933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270718443394470445293955 4906077665091705667940933)
              ·
                refine ⟨919889562204694812738925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4906077665091705667940933 919889562204694812738925)
                ·
                  refine ⟨344958585826760554777097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919889562204694812738925 344958585826760554777097)
                  ·
                    rfl

theorem cell21_1511560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_1511560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511560 prefixEnd_1511560 := by exact prefixLift 1511560
  have htrace : WordTrace (prefixWord ++ tailWord_1511560) baseStart_1511560 baseEnd_1511560 := by
    simpa [prefixWord, tailWord_1511560, baseEnd_1511560] using wordTrace_append hprefix tailTrace_1511560
  have hstable : (prefixWord ++ tailWord_1511560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511560).length < 2 ^ (prefixWord ++ tailWord_1511560).sum := by decide
  have hdescent : baseEnd_1511560 < baseStart_1511560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511684 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 4]
def baseStart_1511684 : Nat := 118140960795 + 1511684 * 2 ^ 59
def prefixEnd_1511684 : Nat := 4983230072969 + 3 ^ 40 * 1511684 * 2
def baseEnd_1511684 : Nat := 344986884316163894710177

theorem tailTrace_1511684 : CollatzResearch.WordTrace tailWord_1511684 prefixEnd_1511684 344986884316163894710177 := by
  unfold tailWord_1511684
  simp only [CollatzResearch.WordTrace]
  refine ⟨27567822527717258958971053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36757096703623011945294737 27567822527717258958971053)
  ·
    refine ⟨10337933447893972109614145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27567822527717258958971053 10337933447893972109614145)
    ·
      refine ⟨7753450085920479082210609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10337933447893972109614145 7753450085920479082210609)
      ·
        refine ⟨5815087564440359311657957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7753450085920479082210609 5815087564440359311657957)
        ·
          refine ⟨1090328918332567370935867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5815087564440359311657957 1090328918332567370935867)
          ·
            refine ⟨1635493377498851056403801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090328918332567370935867 1635493377498851056403801)
            ·
              refine ⟨1226620033124138292302851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635493377498851056403801 1226620033124138292302851)
              ·
                refine ⟨1839930049686207438454277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226620033124138292302851 1839930049686207438454277)
                ·
                  refine ⟨344986884316163894710177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1839930049686207438454277 344986884316163894710177)
                  ·
                    rfl

theorem cell21_1511684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_1511684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511684 prefixEnd_1511684 := by exact prefixLift 1511684
  have htrace : WordTrace (prefixWord ++ tailWord_1511684) baseStart_1511684 baseEnd_1511684 := by
    simpa [prefixWord, tailWord_1511684, baseEnd_1511684] using wordTrace_append hprefix tailTrace_1511684
  have hstable : (prefixWord ++ tailWord_1511684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511684).length < 2 ^ (prefixWord ++ tailWord_1511684).sum := by decide
  have hdescent : baseEnd_1511684 < baseStart_1511684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511729 : List Nat := [1, 2, 2, 3, 4, 2, 2, 2, 3]
def baseStart_1511729 : Nat := 118140960795 + 1511729 * 2 ^ 59
def prefixEnd_1511729 : Nat := 4983230072969 + 3 ^ 40 * 1511729 * 2
def baseEnd_1511729 : Nat := 344997153929253816460085

theorem tailTrace_1511729 : CollatzResearch.WordTrace tailWord_1511729 prefixEnd_1511729 344997153929253816460085 := by
  unfold tailWord_1511729
  simp only [CollatzResearch.WordTrace]
  refine ⟨55137286340271490603330241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36758190893514327068886827 55137286340271490603330241)
  ·
    refine ⟨41352964755203617952497681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55137286340271490603330241 41352964755203617952497681)
    ·
      refine ⟨31014723566402713464373261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41352964755203617952497681 31014723566402713464373261)
      ·
        refine ⟨11630521337401017549139973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31014723566402713464373261 11630521337401017549139973)
        ·
          refine ⟨2180722750762690790463745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11630521337401017549139973 2180722750762690790463745)
          ·
            refine ⟨1635542063072018092847809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2180722750762690790463745 1635542063072018092847809)
            ·
              refine ⟨1226656547304013569635857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635542063072018092847809 1226656547304013569635857)
              ·
                refine ⟨919992410478010177226893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226656547304013569635857 919992410478010177226893)
                ·
                  refine ⟨344997153929253816460085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919992410478010177226893 344997153929253816460085)
                  ·
                    rfl

theorem cell21_1511729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_1511729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511729 prefixEnd_1511729 := by exact prefixLift 1511729
  have htrace : WordTrace (prefixWord ++ tailWord_1511729) baseStart_1511729 baseEnd_1511729 := by
    simpa [prefixWord, tailWord_1511729, baseEnd_1511729] using wordTrace_append hprefix tailTrace_1511729
  have hstable : (prefixWord ++ tailWord_1511729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511729).length < 2 ^ (prefixWord ++ tailWord_1511729).sum := by decide
  have hdescent : baseEnd_1511729 < baseStart_1511729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511844 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1511844 : Nat := 118140960795 + 1511844 * 2 ^ 59
def prefixEnd_1511844 : Nat := 4983230072969 + 3 ^ 40 * 1511844 * 2
def baseEnd_1511844 : Nat := 345023398496039172043183

theorem tailTrace_1511844 : CollatzResearch.WordTrace tailWord_1511844 prefixEnd_1511844 345023398496039172043183 := by
  unfold tailWord_1511844
  simp only [CollatzResearch.WordTrace]
  refine ⟨27570740367427432621883293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36760987156569910162511057 27570740367427432621883293)
  ·
    refine ⟨10339027637785287233206235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27570740367427432621883293 10339027637785287233206235)
    ·
      refine ⟨15508541456677930849809353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10339027637785287233206235 15508541456677930849809353)
      ·
        refine ⟨11631406092508448137357015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15508541456677930849809353 11631406092508448137357015)
        ·
          refine ⟨17447109138762672206035523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11631406092508448137357015 17447109138762672206035523)
          ·
            refine ⟨26170663708144008309053285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17447109138762672206035523 26170663708144008309053285)
            ·
              refine ⟨4906999445277001557947491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26170663708144008309053285 4906999445277001557947491)
              ·
                refine ⟨7360499167915502336921237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906999445277001557947491 7360499167915502336921237)
                ·
                  refine ⟨345023398496039172043183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7360499167915502336921237 345023398496039172043183)
                  ·
                    rfl

theorem cell21_1511844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1511844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511844 prefixEnd_1511844 := by exact prefixLift 1511844
  have htrace : WordTrace (prefixWord ++ tailWord_1511844) baseStart_1511844 baseEnd_1511844 := by
    simpa [prefixWord, tailWord_1511844, baseEnd_1511844] using wordTrace_append hprefix tailTrace_1511844
  have hstable : (prefixWord ++ tailWord_1511844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511844).length < 2 ^ (prefixWord ++ tailWord_1511844).sum := by decide
  have hdescent : baseEnd_1511844 < baseStart_1511844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511847 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 5]
def baseStart_1511847 : Nat := 118140960795 + 1511847 * 2 ^ 59
def prefixEnd_1511847 : Nat := 4983230072969 + 3 ^ 40 * 1511847 * 2
def baseEnd_1511847 : Nat := 345024083136911833493177

theorem tailTrace_1511847 : CollatzResearch.WordTrace tailWord_1511847 prefixEnd_1511847 345024083136911833493177 := by
  unfold tailWord_1511847
  simp only [CollatzResearch.WordTrace]
  refine ⟨55141590153843996756125795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36761060102562664504083863 55141590153843996756125795)
  ·
    refine ⟨82712385230765995134188693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55141590153843996756125795 82712385230765995134188693)
    ·
      refine ⟨3877143057692156021915095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82712385230765995134188693 3877143057692156021915095)
      ·
        refine ⟨5815714586538234032872643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877143057692156021915095 5815714586538234032872643)
        ·
          refine ⟨8723571879807351049308965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5815714586538234032872643 8723571879807351049308965)
          ·
            refine ⟨1635669727463878321745431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8723571879807351049308965 1635669727463878321745431)
            ·
              refine ⟨2453504591195817482618147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635669727463878321745431 2453504591195817482618147)
              ·
                refine ⟨3680256886793726223927221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453504591195817482618147 3680256886793726223927221)
                ·
                  refine ⟨345024083136911833493177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3680256886793726223927221 345024083136911833493177)
                  ·
                    rfl

theorem cell21_1511847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 5].length) (baseStart_1511847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511847 prefixEnd_1511847 := by exact prefixLift 1511847
  have htrace : WordTrace (prefixWord ++ tailWord_1511847) baseStart_1511847 baseEnd_1511847 := by
    simpa [prefixWord, tailWord_1511847, baseEnd_1511847] using wordTrace_append hprefix tailTrace_1511847
  have hstable : (prefixWord ++ tailWord_1511847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511847).length < 2 ^ (prefixWord ++ tailWord_1511847).sum := by decide
  have hdescent : baseEnd_1511847 < baseStart_1511847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511850 : List Nat := [3, 1, 6, 1, 1, 1, 2, 6]
def baseStart_1511850 : Nat := 118140960795 + 1511850 * 2 ^ 59
def prefixEnd_1511850 : Nat := 4983230072969 + 3 ^ 40 * 1511850 * 2
def baseEnd_1511850 : Nat := 115008255925928164981057

theorem tailTrace_1511850 : CollatzResearch.WordTrace tailWord_1511850 prefixEnd_1511850 115008255925928164981057 := by
  unfold tailWord_1511850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13785424893208282067121251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36761133048555418845656669 13785424893208282067121251)
  ·
    refine ⟨20678137339812423100681877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13785424893208282067121251 20678137339812423100681877)
    ·
      refine ⟨969287687803707332844463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20678137339812423100681877 969287687803707332844463)
      ·
        refine ⟨1453931531705560999266695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969287687803707332844463 1453931531705560999266695)
        ·
          refine ⟨2180897297558341498900043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453931531705560999266695 2180897297558341498900043)
          ·
            refine ⟨3271345946337512248350065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180897297558341498900043 3271345946337512248350065)
            ·
              refine ⟨2453509459753134186262549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271345946337512248350065 2453509459753134186262549)
              ·
                refine ⟨115008255925928164981057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2453509459753134186262549 115008255925928164981057)
                ·
                  rfl

theorem cell21_1511850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_1511850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511850 prefixEnd_1511850 := by exact prefixLift 1511850
  have htrace : WordTrace (prefixWord ++ tailWord_1511850) baseStart_1511850 baseEnd_1511850 := by
    simpa [prefixWord, tailWord_1511850, baseEnd_1511850] using wordTrace_append hprefix tailTrace_1511850
  have hstable : (prefixWord ++ tailWord_1511850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511850).length < 2 ^ (prefixWord ++ tailWord_1511850).sum := by decide
  have hdescent : baseEnd_1511850 < baseStart_1511850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511909 : List Nat := [1, 3, 1, 5, 3, 1, 1, 6]
def baseStart_1511909 : Nat := 118140960795 + 1511909 * 2 ^ 59
def prefixEnd_1511909 : Nat := 4983230072969 + 3 ^ 40 * 1511909 * 2
def baseEnd_1511909 : Nat := 115012744127204501153239

theorem tailTrace_1511909 : CollatzResearch.WordTrace tailWord_1511909 prefixEnd_1511909 115012744127204501153239 := by
  unfold tailWord_1511909
  simp only [CollatzResearch.WordTrace]
  refine ⟨55143851479619381344882781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36762567653079587563255187 55143851479619381344882781)
  ·
    refine ⟨20678944304857268004331043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55143851479619381344882781 20678944304857268004331043)
    ·
      refine ⟨31018416457285902006496565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20678944304857268004331043 31018416457285902006496565)
      ·
        refine ⟨2907976542870553313109053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31018416457285902006496565 2907976542870553313109053)
        ·
          refine ⟨1090491203576457492415895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2907976542870553313109053 1090491203576457492415895)
          ·
            refine ⟨1635736805364686238623843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090491203576457492415895 1635736805364686238623843)
            ·
              refine ⟨2453605208047029357935765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635736805364686238623843 2453605208047029357935765)
              ·
                refine ⟨115012744127204501153239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2453605208047029357935765 115012744127204501153239)
                ·
                  rfl

theorem cell21_1511909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 6].length) (baseStart_1511909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511909 prefixEnd_1511909 := by exact prefixLift 1511909
  have htrace : WordTrace (prefixWord ++ tailWord_1511909) baseStart_1511909 baseEnd_1511909 := by
    simpa [prefixWord, tailWord_1511909, baseEnd_1511909] using wordTrace_append hprefix tailTrace_1511909
  have hstable : (prefixWord ++ tailWord_1511909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511909).length < 2 ^ (prefixWord ++ tailWord_1511909).sum := by decide
  have hdescent : baseEnd_1511909 < baseStart_1511909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511920 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_1511920 : Nat := 118140960795 + 1511920 * 2 ^ 59
def prefixEnd_1511920 : Nat := 4983230072969 + 3 ^ 40 * 1511920 * 2
def baseEnd_1511920 : Nat := 345040742731479928776361

theorem tailTrace_1511920 : CollatzResearch.WordTrace tailWord_1511920 prefixEnd_1511920 345040742731479928776361 := by
  unfold tailWord_1511920
  simp only [CollatzResearch.WordTrace]
  refine ⟨27572126341289765111766607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36762835121719686815688809 27572126341289765111766607)
  ·
    refine ⟨41358189511934647667649911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27572126341289765111766607 41358189511934647667649911)
    ·
      refine ⟨62037284267901971501474867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41358189511934647667649911 62037284267901971501474867)
      ·
        refine ⟨93055926401852957252212301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62037284267901971501474867 93055926401852957252212301)
        ·
          refine ⟨34895972400694858969579613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93055926401852957252212301 34895972400694858969579613)
          ·
            refine ⟨13085989650260572113592355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34895972400694858969579613 13085989650260572113592355)
            ·
              refine ⟨19628984475390858170388533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13085989650260572113592355 19628984475390858170388533)
              ·
                refine ⟨1840217294567892953473925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19628984475390858170388533 1840217294567892953473925)
                ·
                  refine ⟨345040742731479928776361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840217294567892953473925 345040742731479928776361)
                  ·
                    rfl

theorem cell21_1511920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_1511920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511920 prefixEnd_1511920 := by exact prefixLift 1511920
  have htrace : WordTrace (prefixWord ++ tailWord_1511920) baseStart_1511920 baseEnd_1511920 := by
    simpa [prefixWord, tailWord_1511920, baseEnd_1511920] using wordTrace_append hprefix tailTrace_1511920
  have hstable : (prefixWord ++ tailWord_1511920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511920).length < 2 ^ (prefixWord ++ tailWord_1511920).sum := by decide
  have hdescent : baseEnd_1511920 < baseStart_1511920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511940 : List Nat := [2, 3, 2, 3, 1, 2, 2, 3, 3]
def baseStart_1511940 : Nat := 118140960795 + 1511940 * 2 ^ 59
def prefixEnd_1511940 : Nat := 4983230072969 + 3 ^ 40 * 1511940 * 2
def baseEnd_1511940 : Nat := 345045307003964338442987

theorem tailTrace_1511940 : CollatzResearch.WordTrace tailWord_1511940 prefixEnd_1511940 345045307003964338442987 := by
  unfold tailWord_1511940
  simp only [CollatzResearch.WordTrace]
  refine ⟨27572491071253536819630637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36763321428338049092840849 27572491071253536819630637)
  ·
    refine ⟨10339684151720076307361489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27572491071253536819630637 10339684151720076307361489)
    ·
      refine ⟨7754763113790057230521117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10339684151720076307361489 7754763113790057230521117)
      ·
        refine ⟨2908036167671271461445419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7754763113790057230521117 2908036167671271461445419)
        ·
          refine ⟨4362054251506907192168129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908036167671271461445419 4362054251506907192168129)
          ·
            refine ⟨3271540688630180394126097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4362054251506907192168129 3271540688630180394126097)
            ·
              refine ⟨2453655516472635295594573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271540688630180394126097 2453655516472635295594573)
              ·
                refine ⟨920120818677238235847965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2453655516472635295594573 920120818677238235847965)
                ·
                  refine ⟨345045307003964338442987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920120818677238235847965 345045307003964338442987)
                  ·
                    rfl

theorem cell21_1511940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_1511940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511940 prefixEnd_1511940 := by exact prefixLift 1511940
  have htrace : WordTrace (prefixWord ++ tailWord_1511940) baseStart_1511940 baseEnd_1511940 := by
    simpa [prefixWord, tailWord_1511940, baseEnd_1511940] using wordTrace_append hprefix tailTrace_1511940
  have hstable : (prefixWord ++ tailWord_1511940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511940).length < 2 ^ (prefixWord ++ tailWord_1511940).sum := by decide
  have hdescent : baseEnd_1511940 < baseStart_1511940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511996 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_1511996 : Nat := 118140960795 + 1511996 * 2 ^ 59
def prefixEnd_1511996 : Nat := 4983230072969 + 3 ^ 40 * 1511996 * 2
def baseEnd_1511996 : Nat := 345058086966920685509539

theorem tailTrace_1511996 : CollatzResearch.WordTrace tailWord_1511996 prefixEnd_1511996 345058086966920685509539 := by
  unfold tailWord_1511996
  simp only [CollatzResearch.WordTrace]
  refine ⟨27573512315152097601649921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36764683086869463468866561 27573512315152097601649921)
  ·
    refine ⟨20680134236364073201237441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27573512315152097601649921 20680134236364073201237441)
    ·
      refine ⟨15510100677273054900928081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20680134236364073201237441 15510100677273054900928081)
      ·
        refine ⟨11632575507954791175696061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15510100677273054900928081 11632575507954791175696061)
        ·
          refine ⟨4362215815483046690886023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11632575507954791175696061 4362215815483046690886023)
          ·
            refine ⟨6543323723224570036329035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362215815483046690886023 6543323723224570036329035)
            ·
              refine ⟨9814985584836855054493553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6543323723224570036329035 9814985584836855054493553)
              ·
                refine ⟨7361239188627641290870165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9814985584836855054493553 7361239188627641290870165)
                ·
                  refine ⟨345058086966920685509539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7361239188627641290870165 345058086966920685509539)
                  ·
                    rfl

theorem cell21_1511996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_1511996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1511996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1511996 prefixEnd_1511996 := by exact prefixLift 1511996
  have htrace : WordTrace (prefixWord ++ tailWord_1511996) baseStart_1511996 baseEnd_1511996 := by
    simpa [prefixWord, tailWord_1511996, baseEnd_1511996] using wordTrace_append hprefix tailTrace_1511996
  have hstable : (prefixWord ++ tailWord_1511996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511996).length < 2 ^ (prefixWord ++ tailWord_1511996).sum := by decide
  have hdescent : baseEnd_1511996 < baseStart_1511996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512010 : List Nat := [3, 1, 2, 1, 1, 4, 9]
def baseStart_1512010 : Nat := 118140960795 + 1512010 * 2 ^ 59
def prefixEnd_1512010 : Nat := 4983230072969 + 3 ^ 40 * 1512010 * 2
def baseEnd_1512010 : Nat := 38340142439739974697353

theorem tailTrace_1512010 : CollatzResearch.WordTrace tailWord_1512010 prefixEnd_1512010 38340142439739974697353 := by
  unfold tailWord_1512010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13786883813063368898577371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36765023501502317062872989 13786883813063368898577371)
  ·
    refine ⟨20680325719595053347866057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13786883813063368898577371 20680325719595053347866057)
    ·
      refine ⟨15510244289696290010899543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20680325719595053347866057 15510244289696290010899543)
      ·
        refine ⟨23265366434544435016349315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15510244289696290010899543 23265366434544435016349315)
        ·
          refine ⟨34898049651816652524523973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23265366434544435016349315 34898049651816652524523973)
          ·
            refine ⟨6543384309715622348348245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34898049651816652524523973 6543384309715622348348245)
            ·
              refine ⟨38340142439739974697353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6543384309715622348348245 38340142439739974697353)
              ·
                rfl

theorem cell21_1512010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 9].length) (baseStart_1512010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512010 prefixEnd_1512010 := by exact prefixLift 1512010
  have htrace : WordTrace (prefixWord ++ tailWord_1512010) baseStart_1512010 baseEnd_1512010 := by
    simpa [prefixWord, tailWord_1512010, baseEnd_1512010] using wordTrace_append hprefix tailTrace_1512010
  have hstable : (prefixWord ++ tailWord_1512010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512010).length < 2 ^ (prefixWord ++ tailWord_1512010).sum := by decide
  have hdescent : baseEnd_1512010 < baseStart_1512010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512013 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1512013 : Nat := 118140960795 + 1512013 * 2 ^ 59
def prefixEnd_1512013 : Nat := 4983230072969 + 3 ^ 40 * 1512013 * 2
def baseEnd_1512013 : Nat := 345061966598532433726171

theorem tailTrace_1512013 : CollatzResearch.WordTrace tailWord_1512013 prefixEnd_1512013 345061966598532433726171 := by
  unfold tailWord_1512013
  simp only [CollatzResearch.WordTrace]
  refine ⟨55147644671242607106668693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36765096447495071404445795 55147644671242607106668693)
  ·
    refine ⟨2585045843964497208125095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55147644671242607106668693 2585045843964497208125095)
    ·
      refine ⟨3877568765946745812187643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585045843964497208125095 3877568765946745812187643)
      ·
        refine ⟨5816353148920118718281465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877568765946745812187643 5816353148920118718281465)
        ·
          refine ⟨4362264861690089038711099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5816353148920118718281465 4362264861690089038711099)
          ·
            refine ⟨6543397292535133558066649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362264861690089038711099 6543397292535133558066649)
            ·
              refine ⟨4907547969401350168549987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6543397292535133558066649 4907547969401350168549987)
              ·
                refine ⟨7361321954102025252824981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907547969401350168549987 7361321954102025252824981)
                ·
                  refine ⟨345061966598532433726171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7361321954102025252824981 345061966598532433726171)
                  ·
                    rfl

theorem cell21_1512013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1512013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512013 prefixEnd_1512013 := by exact prefixLift 1512013
  have htrace : WordTrace (prefixWord ++ tailWord_1512013) baseStart_1512013 baseEnd_1512013 := by
    simpa [prefixWord, tailWord_1512013, baseEnd_1512013] using wordTrace_append hprefix tailTrace_1512013
  have hstable : (prefixWord ++ tailWord_1512013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512013).length < 2 ^ (prefixWord ++ tailWord_1512013).sum := by decide
  have hdescent : baseEnd_1512013 < baseStart_1512013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512055 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 8]
def baseStart_1512055 : Nat := 118140960795 + 1512055 * 2 ^ 59
def prefixEnd_1512055 : Nat := 4983230072969 + 3 ^ 40 * 1512055 * 2
def baseEnd_1512055 : Nat := 345071551570749694026085

theorem tailTrace_1512055 : CollatzResearch.WordTrace tailWord_1512055 prefixEnd_1512055 345071551570749694026085 := by
  unfold tailWord_1512055
  simp only [CollatzResearch.WordTrace]
  refine ⟨55149176537090448279697619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36766117691393632186465079 55149176537090448279697619)
  ·
    refine ⟨82723764805635672419546429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55149176537090448279697619 82723764805635672419546429)
    ·
      refine ⟨31021411802113377157329911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82723764805635672419546429 31021411802113377157329911)
      ·
        refine ⟨46532117703170065735994867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31021411802113377157329911 46532117703170065735994867)
        ·
          refine ⟨69798176554755098603992301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46532117703170065735994867 69798176554755098603992301)
          ·
            refine ⟨26174316208033161976497113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69798176554755098603992301 26174316208033161976497113)
            ·
              refine ⟨19630737156024871482372835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26174316208033161976497113 19630737156024871482372835)
              ·
                refine ⟨29446105734037307223559253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19630737156024871482372835 29446105734037307223559253)
                ·
                  refine ⟨345071551570749694026085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29446105734037307223559253 345071551570749694026085)
                  ·
                    rfl

theorem cell21_1512055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_1512055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512055 prefixEnd_1512055 := by exact prefixLift 1512055
  have htrace : WordTrace (prefixWord ++ tailWord_1512055) baseStart_1512055 baseEnd_1512055 := by
    simpa [prefixWord, tailWord_1512055, baseEnd_1512055] using wordTrace_append hprefix tailTrace_1512055
  have hstable : (prefixWord ++ tailWord_1512055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512055).length < 2 ^ (prefixWord ++ tailWord_1512055).sum := by decide
  have hdescent : baseEnd_1512055 < baseStart_1512055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512168 : List Nat := [2, 1, 4, 1, 4, 2, 1, 3, 3]
def baseStart_1512168 : Nat := 118140960795 + 1512168 * 2 ^ 59
def prefixEnd_1512168 : Nat := 4983230072969 + 3 ^ 40 * 1512168 * 2
def baseEnd_1512168 : Nat := 345097339710286608642521

theorem tailTrace_1512168 : CollatzResearch.WordTrace tailWord_1512168 prefixEnd_1512168 345097339710286608642521 := by
  unfold tailWord_1512168
  simp only [CollatzResearch.WordTrace]
  refine ⟨27576648992840534289280579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36768865323787379052374105 27576648992840534289280579)
  ·
    refine ⟨41364973489260801433920869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27576648992840534289280579 41364973489260801433920869)
    ·
      refine ⟨7755932529236400268860163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41364973489260801433920869 7755932529236400268860163)
      ·
        refine ⟨11633898793854600403290245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7755932529236400268860163 11633898793854600403290245)
        ·
          refine ⟨2181356023847737575616921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11633898793854600403290245 2181356023847737575616921)
          ·
            refine ⟨1636017017885803181712691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2181356023847737575616921 1636017017885803181712691)
            ·
              refine ⟨2454025526828704772569037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636017017885803181712691 2454025526828704772569037)
              ·
                refine ⟨920259572560764289713389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2454025526828704772569037 920259572560764289713389)
                ·
                  refine ⟨345097339710286608642521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920259572560764289713389 345097339710286608642521)
                  ·
                    rfl

theorem cell21_1512168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_1512168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512168 prefixEnd_1512168 := by exact prefixLift 1512168
  have htrace : WordTrace (prefixWord ++ tailWord_1512168) baseStart_1512168 baseEnd_1512168 := by
    simpa [prefixWord, tailWord_1512168, baseEnd_1512168] using wordTrace_append hprefix tailTrace_1512168
  have hstable : (prefixWord ++ tailWord_1512168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512168).length < 2 ^ (prefixWord ++ tailWord_1512168).sum := by decide
  have hdescent : baseEnd_1512168 < baseStart_1512168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512244 : List Nat := [2, 5, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1512244 : Nat := 118140960795 + 1512244 * 2 ^ 59
def prefixEnd_1512244 : Nat := 4983230072969 + 3 ^ 40 * 1512244 * 2
def baseEnd_1512244 : Nat := 345114683945727365375699

theorem tailTrace_1512244 : CollatzResearch.WordTrace tailWord_1512244 prefixEnd_1512244 345114683945727365375699 := by
  unfold tailWord_1512244
  simp only [CollatzResearch.WordTrace]
  refine ⟨27578034966702866779163893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36770713288937155705551857 27578034966702866779163893)
  ·
    refine ⟨2585440778128393760546615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27578034966702866779163893 2585440778128393760546615)
    ·
      refine ⟨3878161167192590640819923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585440778128393760546615 3878161167192590640819923)
      ·
        refine ⟨5817241750788885961229885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878161167192590640819923 5817241750788885961229885)
        ·
          refine ⟨2181465656545832235461207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5817241750788885961229885 2181465656545832235461207)
          ·
            refine ⟨3272198484818748353191811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181465656545832235461207 3272198484818748353191811)
            ·
              refine ⟨4908297727228122529787717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272198484818748353191811 4908297727228122529787717)
              ·
                refine ⟨920305823855272974335197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4908297727228122529787717 920305823855272974335197)
                ·
                  refine ⟨345114683945727365375699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920305823855272974335197 345114683945727365375699)
                  ·
                    rfl

theorem cell21_1512244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1512244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512244 prefixEnd_1512244 := by exact prefixLift 1512244
  have htrace : WordTrace (prefixWord ++ tailWord_1512244) baseStart_1512244 baseEnd_1512244 := by
    simpa [prefixWord, tailWord_1512244, baseEnd_1512244] using wordTrace_append hprefix tailTrace_1512244
  have hstable : (prefixWord ++ tailWord_1512244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512244).length < 2 ^ (prefixWord ++ tailWord_1512244).sum := by decide
  have hdescent : baseEnd_1512244 < baseStart_1512244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512255 : List Nat := [1, 1, 2, 2, 5, 3, 1, 6]
def baseStart_1512255 : Nat := 118140960795 + 1512255 * 2 ^ 59
def prefixEnd_1512255 : Nat := 4983230072969 + 3 ^ 40 * 1512255 * 2
def baseEnd_1512255 : Nat := 115039064765197930230781

theorem tailTrace_1512255 : CollatzResearch.WordTrace tailWord_1512255 prefixEnd_1512255 115039064765197930230781 := by
  unfold tailWord_1512255
  simp only [CollatzResearch.WordTrace]
  refine ⟨55156471136365882436978219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36770980757577254957985479 55156471136365882436978219)
  ·
    refine ⟨82734706704548823655467329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55156471136365882436978219 82734706704548823655467329)
    ·
      refine ⟨62051030028411617741600497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82734706704548823655467329 62051030028411617741600497)
      ·
        refine ⟨46538272521308713306200373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62051030028411617741600497 46538272521308713306200373)
        ·
          refine ⟨4362963048872691872456285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46538272521308713306200373 4362963048872691872456285)
          ·
            refine ⟨1636111143327259452171107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4362963048872691872456285 1636111143327259452171107)
            ·
              refine ⟨2454166714990889178256661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636111143327259452171107 2454166714990889178256661)
              ·
                refine ⟨115039064765197930230781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2454166714990889178256661 115039064765197930230781)
                ·
                  rfl

theorem cell21_1512255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 6].length) (baseStart_1512255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512255 prefixEnd_1512255 := by exact prefixLift 1512255
  have htrace : WordTrace (prefixWord ++ tailWord_1512255) baseStart_1512255 baseEnd_1512255 := by
    simpa [prefixWord, tailWord_1512255, baseEnd_1512255] using wordTrace_append hprefix tailTrace_1512255
  have hstable : (prefixWord ++ tailWord_1512255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512255).length < 2 ^ (prefixWord ++ tailWord_1512255).sum := by decide
  have hdescent : baseEnd_1512255 < baseStart_1512255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512348 : List Nat := [2, 2, 3, 3, 3, 1, 7]
def baseStart_1512348 : Nat := 118140960795 + 1512348 * 2 ^ 59
def prefixEnd_1512348 : Nat := 4983230072969 + 3 ^ 40 * 1512348 * 2
def baseEnd_1512348 : Nat := 38348713129182921738017

theorem tailTrace_1512348 : CollatzResearch.WordTrace tailWord_1512348 prefixEnd_1512348 38348713129182921738017 := by
  unfold tailWord_1512348
  simp only [CollatzResearch.WordTrace]
  refine ⟨27579931562514479660056849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36773242083352639546742465 27579931562514479660056849)
  ·
    refine ⟨20684948671885859745042637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27579931562514479660056849 20684948671885859745042637)
    ·
      refine ⟨7756855751957197404390989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20684948671885859745042637 7756855751957197404390989)
      ·
        refine ⟨2908820906983949026646621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7756855751957197404390989 2908820906983949026646621)
        ·
          refine ⟨1090807840118980884992483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2908820906983949026646621 1090807840118980884992483)
          ·
            refine ⟨1636211760178471327488725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090807840118980884992483 1636211760178471327488725)
            ·
              refine ⟨38348713129182921738017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1636211760178471327488725 38348713129182921738017)
              ·
                rfl

theorem cell21_1512348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 7].length) (baseStart_1512348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512348 prefixEnd_1512348 := by exact prefixLift 1512348
  have htrace : WordTrace (prefixWord ++ tailWord_1512348) baseStart_1512348 baseEnd_1512348 := by
    simpa [prefixWord, tailWord_1512348, baseEnd_1512348] using wordTrace_append hprefix tailTrace_1512348
  have hstable : (prefixWord ++ tailWord_1512348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512348).length < 2 ^ (prefixWord ++ tailWord_1512348).sum := by decide
  have hdescent : baseEnd_1512348 < baseStart_1512348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512376 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_1512376 : Nat := 118140960795 + 1512376 * 2 ^ 59
def prefixEnd_1512376 : Nat := 4983230072969 + 3 ^ 40 * 1512376 * 2
def baseEnd_1512376 : Nat := 345144808144124469175429

theorem tailTrace_1512376 : CollatzResearch.WordTrace tailWord_1512376 prefixEnd_1512376 345144808144124469175429 := by
  unfold tailWord_1512376
  simp only [CollatzResearch.WordTrace]
  refine ⟨27580442184463760051066491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36773922912618346734755321 27580442184463760051066491)
  ·
    refine ⟨41370663276695640076599737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27580442184463760051066491 41370663276695640076599737)
    ·
      refine ⟨31027997457521730057449803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41370663276695640076599737 31027997457521730057449803)
      ·
        refine ⟨46541996186282595086174705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31027997457521730057449803 46541996186282595086174705)
        ·
          refine ⟨34906497139711946314631029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46541996186282595086174705 34906497139711946314631029)
          ·
            refine ⟨3272484106847994966996659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34906497139711946314631029 3272484106847994966996659)
            ·
              refine ⟨4908726160271992450494989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272484106847994966996659 4908726160271992450494989)
              ·
                refine ⟨1840772310101997168935621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4908726160271992450494989 1840772310101997168935621)
                ·
                  refine ⟨345144808144124469175429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840772310101997168935621 345144808144124469175429)
                  ·
                    rfl

theorem cell21_1512376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_1512376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512376 prefixEnd_1512376 := by exact prefixLift 1512376
  have htrace : WordTrace (prefixWord ++ tailWord_1512376) baseStart_1512376 baseEnd_1512376 := by
    simpa [prefixWord, tailWord_1512376, baseEnd_1512376] using wordTrace_append hprefix tailTrace_1512376
  have hstable : (prefixWord ++ tailWord_1512376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512376).length < 2 ^ (prefixWord ++ tailWord_1512376).sum := by decide
  have hdescent : baseEnd_1512376 < baseStart_1512376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512438 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1512438 : Nat := 118140960795 + 1512438 * 2 ^ 59
def prefixEnd_1512438 : Nat := 4983230072969 + 3 ^ 40 * 1512438 * 2
def baseEnd_1512438 : Nat := 345158957388826139141969

theorem tailTrace_1512438 : CollatzResearch.WordTrace tailWord_1512438 prefixEnd_1512438 345158957388826139141969 := by
  unfold tailWord_1512438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447696605918931543180623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36775430463135269793926645 3447696605918931543180623)
  ·
    refine ⟨5171544908878397314770935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3447696605918931543180623 5171544908878397314770935)
    ·
      refine ⟨7757317363317595972156403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171544908878397314770935 7757317363317595972156403)
      ·
        refine ⟨11635976044976393958234605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7757317363317595972156403 11635976044976393958234605)
        ·
          refine ⟨4363491016866147734337977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11635976044976393958234605 4363491016866147734337977)
          ·
            refine ⟨3272618262649610800753483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4363491016866147734337977 3272618262649610800753483)
            ·
              refine ⟨4908927393974416201130225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272618262649610800753483 4908927393974416201130225)
              ·
                refine ⟨3681695545480812150847669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4908927393974416201130225 3681695545480812150847669)
                ·
                  refine ⟨345158957388826139141969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3681695545480812150847669 345158957388826139141969)
                  ·
                    rfl

theorem cell21_1512438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1512438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512438 prefixEnd_1512438 := by exact prefixLift 1512438
  have htrace : WordTrace (prefixWord ++ tailWord_1512438) baseStart_1512438 baseEnd_1512438 := by
    simpa [prefixWord, tailWord_1512438, baseEnd_1512438] using wordTrace_append hprefix tailTrace_1512438
  have hstable : (prefixWord ++ tailWord_1512438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512438).length < 2 ^ (prefixWord ++ tailWord_1512438).sum := by decide
  have hdescent : baseEnd_1512438 < baseStart_1512438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512469 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 4]
def baseStart_1512469 : Nat := 118140960795 + 1512469 * 2 ^ 59
def prefixEnd_1512469 : Nat := 4983230072969 + 3 ^ 40 * 1512469 * 2
def baseEnd_1512469 : Nat := 345166032011176974125239

theorem tailTrace_1512469 : CollatzResearch.WordTrace tailWord_1512469 prefixEnd_1512469 345166032011176974125239 := by
  unfold tailWord_1512469
  simp only [CollatzResearch.WordTrace]
  refine ⟨55164276357590596985268461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36776184238393731323512307 55164276357590596985268461)
  ·
    refine ⟨20686603634096473869475673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55164276357590596985268461 20686603634096473869475673)
    ·
      refine ⟨15514952725572355402106755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20686603634096473869475673 15514952725572355402106755)
      ·
        refine ⟨23272429088358533103160133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15514952725572355402106755 23272429088358533103160133)
        ·
          refine ⟨4363580454067224956842525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23272429088358533103160133 4363580454067224956842525)
          ·
            refine ⟨1636342670275209358815947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4363580454067224956842525 1636342670275209358815947)
            ·
              refine ⟨2454514005412814038223921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636342670275209358815947 2454514005412814038223921)
              ·
                refine ⟨1840885504059610528667941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2454514005412814038223921 1840885504059610528667941)
                ·
                  refine ⟨345166032011176974125239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840885504059610528667941 345166032011176974125239)
                  ·
                    rfl

theorem cell21_1512469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_1512469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512469 prefixEnd_1512469 := by exact prefixLift 1512469
  have htrace : WordTrace (prefixWord ++ tailWord_1512469) baseStart_1512469 baseEnd_1512469 := by
    simpa [prefixWord, tailWord_1512469, baseEnd_1512469] using wordTrace_append hprefix tailTrace_1512469
  have hstable : (prefixWord ++ tailWord_1512469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512469).length < 2 ^ (prefixWord ++ tailWord_1512469).sum := by decide
  have hdescent : baseEnd_1512469 < baseStart_1512469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512500 : List Nat := [2, 5, 1, 2, 1, 1, 4, 5]
def baseStart_1512500 : Nat := 118140960795 + 1512500 * 2 ^ 59
def prefixEnd_1512500 : Nat := 4983230072969 + 3 ^ 40 * 1512500 * 2
def baseEnd_1512500 : Nat := 115057702211175936369503

theorem tailTrace_1512500 : CollatzResearch.WordTrace tailWord_1512500 prefixEnd_1512500 115057702211175936369503 := by
  unfold tailWord_1512500
  simp only [CollatzResearch.WordTrace]
  refine ⟨27582703510239144639823477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36776938013652192853097969 27582703510239144639823477)
  ·
    refine ⟨2585878454084919809983451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27582703510239144639823477 2585878454084919809983451)
    ·
      refine ⟨3878817681127379714975177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585878454084919809983451 3878817681127379714975177)
      ·
        refine ⟨2909113260845534786231383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3878817681127379714975177 2909113260845534786231383)
        ·
          refine ⟨4363669891268302179347075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909113260845534786231383 4363669891268302179347075)
          ·
            refine ⟨6545504836902453269020613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363669891268302179347075 6545504836902453269020613)
            ·
              refine ⟨1227282156919209987941365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6545504836902453269020613 1227282156919209987941365)
              ·
                refine ⟨115057702211175936369503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1227282156919209987941365 115057702211175936369503)
                ·
                  rfl

theorem cell21_1512500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_1512500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512500 prefixEnd_1512500 := by exact prefixLift 1512500
  have htrace : WordTrace (prefixWord ++ tailWord_1512500) baseStart_1512500 baseEnd_1512500 := by
    simpa [prefixWord, tailWord_1512500, baseEnd_1512500] using wordTrace_append hprefix tailTrace_1512500
  have hstable : (prefixWord ++ tailWord_1512500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512500).length < 2 ^ (prefixWord ++ tailWord_1512500).sum := by decide
  have hdescent : baseEnd_1512500 < baseStart_1512500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512556 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_1512556 : Nat := 118140960795 + 1512556 * 2 ^ 59
def prefixEnd_1512556 : Nat := 4983230072969 + 3 ^ 40 * 1512556 * 2
def baseEnd_1512556 : Nat := 345185886596484156175061

theorem tailTrace_1512556 : CollatzResearch.WordTrace tailWord_1512556 prefixEnd_1512556 345185886596484156175061 := by
  unfold tailWord_1512556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27583724754137705421842761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36778299672183607229123681 27583724754137705421842761)
  ·
    refine ⟨20687793565603279066382071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27583724754137705421842761 20687793565603279066382071)
    ·
      refine ⟨31031690348404918599573107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20687793565603279066382071 31031690348404918599573107)
      ·
        refine ⟨46547535522607377899359661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31031690348404918599573107 46547535522607377899359661)
        ·
          refine ⟨17455325820977766712259873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46547535522607377899359661 17455325820977766712259873)
          ·
            refine ⟨13091494365733325034194905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17455325820977766712259873 13091494365733325034194905)
            ·
              refine ⟨9818620774299993775646179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13091494365733325034194905 9818620774299993775646179)
              ·
                refine ⟨14727931161449990663469269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9818620774299993775646179 14727931161449990663469269)
                ·
                  refine ⟨345185886596484156175061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14727931161449990663469269 345185886596484156175061)
                  ·
                    rfl

theorem cell21_1512556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_1512556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512556 prefixEnd_1512556 := by exact prefixLift 1512556
  have htrace : WordTrace (prefixWord ++ tailWord_1512556) baseStart_1512556 baseEnd_1512556 := by
    simpa [prefixWord, tailWord_1512556, baseEnd_1512556] using wordTrace_append hprefix tailTrace_1512556
  have hstable : (prefixWord ++ tailWord_1512556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512556).length < 2 ^ (prefixWord ++ tailWord_1512556).sum := by decide
  have hdescent : baseEnd_1512556 < baseStart_1512556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512604 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_1512604 : Nat := 118140960795 + 1512604 * 2 ^ 59
def prefixEnd_1512604 : Nat := 4983230072969 + 3 ^ 40 * 1512604 * 2
def baseEnd_1512604 : Nat := 345196840850446739374963

theorem tailTrace_1512604 : CollatzResearch.WordTrace tailWord_1512604 prefixEnd_1512604 345196840850446739374963 := by
  unfold tailWord_1512604
  simp only [CollatzResearch.WordTrace]
  refine ⟨27584600106050757520716433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36779466808067676694288577 27584600106050757520716433)
  ·
    refine ⟨20688450079538068140537325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27584600106050757520716433 20688450079538068140537325)
    ·
      refine ⟨7758168779826775552701497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20688450079538068140537325 7758168779826775552701497)
      ·
        refine ⟨5818626584870081664526123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7758168779826775552701497 5818626584870081664526123)
        ·
          refine ⟨8727939877305122496789185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5818626584870081664526123 8727939877305122496789185)
          ·
            refine ⟨6545954907978841872591889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8727939877305122496789185 6545954907978841872591889)
            ·
              refine ⟨4909466180984131404443917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6545954907978841872591889 4909466180984131404443917)
              ·
                refine ⟨1841049817869049276666469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4909466180984131404443917 1841049817869049276666469)
                ·
                  refine ⟨345196840850446739374963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841049817869049276666469 345196840850446739374963)
                  ·
                    rfl

theorem cell21_1512604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_1512604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512604 prefixEnd_1512604 := by exact prefixLift 1512604
  have htrace : WordTrace (prefixWord ++ tailWord_1512604) baseStart_1512604 baseEnd_1512604 := by
    simpa [prefixWord, tailWord_1512604, baseEnd_1512604] using wordTrace_append hprefix tailTrace_1512604
  have hstable : (prefixWord ++ tailWord_1512604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512604).length < 2 ^ (prefixWord ++ tailWord_1512604).sum := by decide
  have hdescent : baseEnd_1512604 < baseStart_1512604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512663 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 4]
def baseStart_1512663 : Nat := 118140960795 + 1512663 * 2 ^ 59
def prefixEnd_1512663 : Nat := 4983230072969 + 3 ^ 40 * 1512663 * 2
def baseEnd_1512663 : Nat := 345210305454275747891509

theorem tailTrace_1512663 : CollatzResearch.WordTrace tailWord_1512663 prefixEnd_1512663 345210305454275747891509 := by
  unfold tailWord_1512663
  simp only [CollatzResearch.WordTrace]
  refine ⟨55171352118887768117830643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36780901412591845411887095 55171352118887768117830643)
  ·
    refine ⟨82757028178331652176745965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55171352118887768117830643 82757028178331652176745965)
    ·
      refine ⟨31033885566874369566279737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82757028178331652176745965 31033885566874369566279737)
      ·
        refine ⟨23275414175155777174709803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31033885566874369566279737 23275414175155777174709803)
        ·
          refine ⟨34913121262733665762064705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23275414175155777174709803 34913121262733665762064705)
          ·
            refine ⟨26184840947050249321548529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34913121262733665762064705 26184840947050249321548529)
            ·
              refine ⟨19638630710287686991161397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26184840947050249321548529 19638630710287686991161397)
              ·
                refine ⟨1841121629089470655421381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19638630710287686991161397 1841121629089470655421381)
                ·
                  refine ⟨345210305454275747891509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841121629089470655421381 345210305454275747891509)
                  ·
                    rfl

theorem cell21_1512663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 4].length) (baseStart_1512663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512663 prefixEnd_1512663 := by exact prefixLift 1512663
  have htrace : WordTrace (prefixWord ++ tailWord_1512663) baseStart_1512663 baseEnd_1512663 := by
    simpa [prefixWord, tailWord_1512663, baseEnd_1512663] using wordTrace_append hprefix tailTrace_1512663
  have hstable : (prefixWord ++ tailWord_1512663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512663).length < 2 ^ (prefixWord ++ tailWord_1512663).sum := by decide
  have hdescent : baseEnd_1512663 < baseStart_1512663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512669 : List Nat := [1, 4, 3, 2, 3, 1, 2, 5]
def baseStart_1512669 : Nat := 118140960795 + 1512669 * 2 ^ 59
def prefixEnd_1512669 : Nat := 4983230072969 + 3 ^ 40 * 1512669 * 2
def baseEnd_1512669 : Nat := 115070558245340356930499

theorem tailTrace_1512669 : CollatzResearch.WordTrace tailWord_1512669 prefixEnd_1512669 115070558245340356930499 := by
  unfold tailWord_1512669
  simp only [CollatzResearch.WordTrace]
  refine ⟨55171570956866031142549061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36781047304577354095032707 55171570956866031142549061)
  ·
    refine ⟨10344669554412380839227949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55171570956866031142549061 10344669554412380839227949)
    ·
      refine ⟨3879251082904642814710481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10344669554412380839227949 3879251082904642814710481)
      ·
        refine ⟨2909438312178482111032861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3879251082904642814710481 2909438312178482111032861)
        ·
          refine ⟨1091039367066930791637323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2909438312178482111032861 1091039367066930791637323)
          ·
            refine ⟨1636559050600396187455985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091039367066930791637323 1636559050600396187455985)
            ·
              refine ⟨1227419287950297140591989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636559050600396187455985 1227419287950297140591989)
              ·
                refine ⟨115070558245340356930499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1227419287950297140591989 115070558245340356930499)
                ·
                  rfl

theorem cell21_1512669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 5].length) (baseStart_1512669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512669 prefixEnd_1512669 := by exact prefixLift 1512669
  have htrace : WordTrace (prefixWord ++ tailWord_1512669) baseStart_1512669 baseEnd_1512669 := by
    simpa [prefixWord, tailWord_1512669, baseEnd_1512669] using wordTrace_append hprefix tailTrace_1512669
  have hstable : (prefixWord ++ tailWord_1512669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512669).length < 2 ^ (prefixWord ++ tailWord_1512669).sum := by decide
  have hdescent : baseEnd_1512669 < baseStart_1512669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512753 : List Nat := [1, 2, 2, 3, 3, 10]
def baseStart_1512753 : Nat := 118140960795 + 1512753 * 2 ^ 59
def prefixEnd_1512753 : Nat := 4983230072969 + 3 ^ 40 * 1512753 * 2
def baseEnd_1512753 : Nat := 12786327580757614495975

theorem tailTrace_1512753 : CollatzResearch.WordTrace tailWord_1512753 prefixEnd_1512753 12786327580757614495975 := by
  unfold tailWord_1512753
  simp only [CollatzResearch.WordTrace]
  refine ⟨55174634688561713488606913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36783089792374475659071275 55174634688561713488606913)
  ·
    refine ⟨41380976016421285116455185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55174634688561713488606913 41380976016421285116455185)
    ·
      refine ⟨31035732012315963837341389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41380976016421285116455185 31035732012315963837341389)
      ·
        refine ⟨11638399504618486439003021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31035732012315963837341389 11638399504618486439003021)
        ·
          refine ⟨4364399814231932414626133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11638399504618486439003021 4364399814231932414626133)
          ·
            refine ⟨12786327580757614495975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4364399814231932414626133 12786327580757614495975)
            ·
              rfl

theorem cell21_1512753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 10].length) (baseStart_1512753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512753 prefixEnd_1512753 := by exact prefixLift 1512753
  have htrace : WordTrace (prefixWord ++ tailWord_1512753) baseStart_1512753 baseEnd_1512753 := by
    simpa [prefixWord, tailWord_1512753, baseEnd_1512753] using wordTrace_append hprefix tailTrace_1512753
  have hstable : (prefixWord ++ tailWord_1512753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512753).length < 2 ^ (prefixWord ++ tailWord_1512753).sum := by decide
  have hdescent : baseEnd_1512753 < baseStart_1512753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512784 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_1512784 : Nat := 118140960795 + 1512784 * 2 ^ 59
def prefixEnd_1512784 : Nat := 4983230072969 + 3 ^ 40 * 1512784 * 2
def baseEnd_1512784 : Nat := 345237919302806426374595

theorem tailTrace_1512784 : CollatzResearch.WordTrace tailWord_1512784 prefixEnd_1512784 345237919302806426374595 := by
  unfold tailWord_1512784
  simp only [CollatzResearch.WordTrace]
  refine ⟨27587882675724702891492703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36783843567632937188656937 27587882675724702891492703)
  ·
    refine ⟨41381824013587054337239055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27587882675724702891492703 41381824013587054337239055)
    ·
      refine ⟨62072736020380581505858583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41381824013587054337239055 62072736020380581505858583)
      ·
        refine ⟨93109104030570872258787875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62072736020380581505858583 93109104030570872258787875)
        ·
          refine ⟨139663656045856308388181813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93109104030570872258787875 139663656045856308388181813)
          ·
            refine ⟨13093467754299028911392045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139663656045856308388181813 13093467754299028911392045)
            ·
              refine ⟨4910050407862135841772017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13093467754299028911392045 4910050407862135841772017)
              ·
                refine ⟨3682537805896601881329013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4910050407862135841772017 3682537805896601881329013)
                ·
                  refine ⟨345237919302806426374595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3682537805896601881329013 345237919302806426374595)
                  ·
                    rfl

theorem cell21_1512784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_1512784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512784 prefixEnd_1512784 := by exact prefixLift 1512784
  have htrace : WordTrace (prefixWord ++ tailWord_1512784) baseStart_1512784 baseEnd_1512784 := by
    simpa [prefixWord, tailWord_1512784, baseEnd_1512784] using wordTrace_append hprefix tailTrace_1512784
  have hstable : (prefixWord ++ tailWord_1512784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512784).length < 2 ^ (prefixWord ++ tailWord_1512784).sum := by decide
  have hdescent : baseEnd_1512784 < baseStart_1512784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512829 : List Nat := [1, 4, 1, 1, 2, 2, 2, 8]
def baseStart_1512829 : Nat := 118140960795 + 1512829 * 2 ^ 59
def prefixEnd_1512829 : Nat := 4983230072969 + 3 ^ 40 * 1512829 * 2
def baseEnd_1512829 : Nat := 115082729638632116041501

theorem tailTrace_1512829 : CollatzResearch.WordTrace tailWord_1512829 prefixEnd_1512829 115082729638632116041501 := by
  unfold tailWord_1512829
  simp only [CollatzResearch.WordTrace]
  refine ⟨55177406636286378468373541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36784937757524252312249027 55177406636286378468373541)
  ·
    refine ⟨10345763744303695962820039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55177406636286378468373541 10345763744303695962820039)
    ·
      refine ⟨15518645616455543944230059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10345763744303695962820039 15518645616455543944230059)
      ·
        refine ⟨23277968424683315916345089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15518645616455543944230059 23277968424683315916345089)
        ·
          refine ⟨17458476318512486937258817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23277968424683315916345089 17458476318512486937258817)
          ·
            refine ⟨13093857238884365202944113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17458476318512486937258817 13093857238884365202944113)
            ·
              refine ⟨9820392929163273902208085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13093857238884365202944113 9820392929163273902208085)
              ·
                refine ⟨115082729638632116041501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9820392929163273902208085 115082729638632116041501)
                ·
                  rfl

theorem cell21_1512829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 8].length) (baseStart_1512829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512829 prefixEnd_1512829 := by exact prefixLift 1512829
  have htrace : WordTrace (prefixWord ++ tailWord_1512829) baseStart_1512829 baseEnd_1512829 := by
    simpa [prefixWord, tailWord_1512829, baseEnd_1512829] using wordTrace_append hprefix tailTrace_1512829
  have hstable : (prefixWord ++ tailWord_1512829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512829).length < 2 ^ (prefixWord ++ tailWord_1512829).sum := by decide
  have hdescent : baseEnd_1512829 < baseStart_1512829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512936 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_1512936 : Nat := 118140960795 + 1512936 * 2 ^ 59
def prefixEnd_1512936 : Nat := 4983230072969 + 3 ^ 40 * 1512936 * 2
def baseEnd_1512936 : Nat := 345272607773687939840951

theorem tailTrace_1512936 : CollatzResearch.WordTrace tailWord_1512936 prefixEnd_1512936 345272607773687939840951 := by
  unfold tailWord_1512936
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590654623449367871259331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36787539497932490495012441 27590654623449367871259331)
  ·
    refine ⟨41385981935174051806888997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27590654623449367871259331 41385981935174051806888997)
    ·
      refine ⟨7759871612845134713791687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41385981935174051806888997 7759871612845134713791687)
      ·
        refine ⟨11639807419267702070687531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7759871612845134713791687 11639807419267702070687531)
        ·
          refine ⟨17459711128901553106031297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11639807419267702070687531 17459711128901553106031297)
          ·
            refine ⟨13094783346676164829523473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17459711128901553106031297 13094783346676164829523473)
            ·
              refine ⟨9821087510007123622142605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13094783346676164829523473 9821087510007123622142605)
              ·
                refine ⟨3682907816252671358303477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9821087510007123622142605 3682907816252671358303477)
                ·
                  refine ⟨345272607773687939840951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3682907816252671358303477 345272607773687939840951)
                  ·
                    rfl

theorem cell21_1512936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_1512936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512936 prefixEnd_1512936 := by exact prefixLift 1512936
  have htrace : WordTrace (prefixWord ++ tailWord_1512936) baseStart_1512936 baseEnd_1512936 := by
    simpa [prefixWord, tailWord_1512936, baseEnd_1512936] using wordTrace_append hprefix tailTrace_1512936
  have hstable : (prefixWord ++ tailWord_1512936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512936).length < 2 ^ (prefixWord ++ tailWord_1512936).sum := by decide
  have hdescent : baseEnd_1512936 < baseStart_1512936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512970 : List Nat := [3, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_1512970 : Nat := 118140960795 + 1512970 * 2 ^ 59
def prefixEnd_1512970 : Nat := 4983230072969 + 3 ^ 40 * 1512970 * 2
def baseEnd_1512970 : Nat := 345280367036911436274215

theorem tailTrace_1512970 : CollatzResearch.WordTrace tailWord_1512970 prefixEnd_1512970 345280367036911436274215 := by
  unfold tailWord_1512970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795637332193889887314091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36788366219183706366170909 13795637332193889887314091)
  ·
    refine ⟨20693455998290834830971137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13795637332193889887314091 20693455998290834830971137)
    ·
      refine ⟨15520091998718126123228353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20693455998290834830971137 15520091998718126123228353)
      ·
        refine ⟨11640068999038594592421265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15520091998718126123228353 11640068999038594592421265)
        ·
          refine ⟨8730051749278945944315949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11640068999038594592421265 8730051749278945944315949)
          ·
            refine ⟨3273769405979604729118481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8730051749278945944315949 3273769405979604729118481)
            ·
              refine ⟨2455327054484703546838861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3273769405979604729118481 2455327054484703546838861)
              ·
                refine ⟨920747645431763830064573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2455327054484703546838861 920747645431763830064573)
                ·
                  refine ⟨345280367036911436274215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920747645431763830064573 345280367036911436274215)
                  ·
                    rfl

theorem cell21_1512970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_1512970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512970 prefixEnd_1512970 := by exact prefixLift 1512970
  have htrace : WordTrace (prefixWord ++ tailWord_1512970) baseStart_1512970 baseEnd_1512970 := by
    simpa [prefixWord, tailWord_1512970, baseEnd_1512970] using wordTrace_append hprefix tailTrace_1512970
  have hstable : (prefixWord ++ tailWord_1512970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512970).length < 2 ^ (prefixWord ++ tailWord_1512970).sum := by decide
  have hdescent : baseEnd_1512970 < baseStart_1512970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512981 : List Nat := [1, 3, 2, 1, 3, 3, 8]
def baseStart_1512981 : Nat := 118140960795 + 1512981 * 2 ^ 59
def prefixEnd_1512981 : Nat := 4983230072969 + 3 ^ 40 * 1512981 * 2
def baseEnd_1512981 : Nat := 38364764154086429065651

theorem tailTrace_1512981 : CollatzResearch.WordTrace tailWord_1512981 prefixEnd_1512981 38364764154086429065651 := by
  unfold tailWord_1512981
  simp only [CollatzResearch.WordTrace]
  refine ⟨55182950531735708427906797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36788633687823805618604531 55182950531735708427906797)
  ·
    refine ⟨20693606449400890660465049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55182950531735708427906797 20693606449400890660465049)
    ·
      refine ⟨15520204837050667995348787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20693606449400890660465049 15520204837050667995348787)
      ·
        refine ⟨23280307255576001993023181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15520204837050667995348787 23280307255576001993023181)
        ·
          refine ⟨8730115220841000747383693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23280307255576001993023181 8730115220841000747383693)
          ·
            refine ⟨3273793207815375280268885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8730115220841000747383693 3273793207815375280268885)
            ·
              refine ⟨38364764154086429065651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3273793207815375280268885 38364764154086429065651)
              ·
                rfl

theorem cell21_1512981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 8].length) (baseStart_1512981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1512981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1512981 prefixEnd_1512981 := by exact prefixLift 1512981
  have htrace : WordTrace (prefixWord ++ tailWord_1512981) baseStart_1512981 baseEnd_1512981 := by
    simpa [prefixWord, tailWord_1512981, baseEnd_1512981] using wordTrace_append hprefix tailTrace_1512981
  have hstable : (prefixWord ++ tailWord_1512981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512981).length < 2 ^ (prefixWord ++ tailWord_1512981).sum := by decide
  have hdescent : baseEnd_1512981 < baseStart_1512981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513057 : List Nat := [1, 2, 3, 1, 1, 3, 4, 6]
def baseStart_1513057 : Nat := 118140960795 + 1513057 * 2 ^ 59
def prefixEnd_1513057 : Nat := 4983230072969 + 3 ^ 40 * 1513057 * 2
def baseEnd_1513057 : Nat := 115100073874072872774679

theorem tailTrace_1513057 : CollatzResearch.WordTrace tailWord_1513057 prefixEnd_1513057 115100073874072872774679 := by
  unfold tailWord_1513057
  simp only [CollatzResearch.WordTrace]
  refine ⟨55185722479460373407673425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36790481652973582271782283 55185722479460373407673425)
  ·
    refine ⟨41389291859595280055755069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55185722479460373407673425 41389291859595280055755069)
    ·
      refine ⟨15520984447348230020908151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41389291859595280055755069 15520984447348230020908151)
      ·
        refine ⟨23281476671022345031362227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15520984447348230020908151 23281476671022345031362227)
        ·
          refine ⟨34922215006533517547043341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23281476671022345031362227 34922215006533517547043341)
          ·
            refine ⟨13095830627450069080141253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34922215006533517547043341 13095830627450069080141253)
            ·
              refine ⟨2455468242646887952526485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13095830627450069080141253 2455468242646887952526485)
              ·
                refine ⟨115100073874072872774679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2455468242646887952526485 115100073874072872774679)
                ·
                  rfl

theorem cell21_1513057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 6].length) (baseStart_1513057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513057 prefixEnd_1513057 := by exact prefixLift 1513057
  have htrace : WordTrace (prefixWord ++ tailWord_1513057) baseStart_1513057 baseEnd_1513057 := by
    simpa [prefixWord, tailWord_1513057, baseEnd_1513057] using wordTrace_append hprefix tailTrace_1513057
  have hstable : (prefixWord ++ tailWord_1513057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513057).length < 2 ^ (prefixWord ++ tailWord_1513057).sum := by decide
  have hdescent : baseEnd_1513057 < baseStart_1513057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513060 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_1513060 : Nat := 118140960795 + 1513060 * 2 ^ 59
def prefixEnd_1513060 : Nat := 4983230072969 + 3 ^ 40 * 1513060 * 2
def baseEnd_1513060 : Nat := 345300906263091279774031

theorem tailTrace_1513060 : CollatzResearch.WordTrace tailWord_1513060 prefixEnd_1513060 345300906263091279774031 := by
  unfold tailWord_1513060
  simp only [CollatzResearch.WordTrace]
  refine ⟨27592915949224752460016317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36790554598966336613355089 27592915949224752460016317)
  ·
    refine ⟨10347343480959282172506119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27592915949224752460016317 10347343480959282172506119)
    ·
      refine ⟨15521015221438923258759179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10347343480959282172506119 15521015221438923258759179)
      ·
        refine ⟨23281522832158384888138769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15521015221438923258759179 23281522832158384888138769)
        ·
          refine ⟨17461142124118788666104077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23281522832158384888138769 17461142124118788666104077)
          ·
            refine ⟨6547928296544545749789029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17461142124118788666104077 6547928296544545749789029)
            ·
              refine ⟨1227736555602102328085443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6547928296544545749789029 1227736555602102328085443)
              ·
                refine ⟨1841604833403153492128165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227736555602102328085443 1841604833403153492128165)
                ·
                  refine ⟨345300906263091279774031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841604833403153492128165 345300906263091279774031)
                  ·
                    rfl

theorem cell21_1513060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_1513060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513060 prefixEnd_1513060 := by exact prefixLift 1513060
  have htrace : WordTrace (prefixWord ++ tailWord_1513060) baseStart_1513060 baseEnd_1513060 := by
    simpa [prefixWord, tailWord_1513060, baseEnd_1513060] using wordTrace_append hprefix tailTrace_1513060
  have hstable : (prefixWord ++ tailWord_1513060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513060).length < 2 ^ (prefixWord ++ tailWord_1513060).sum := by decide
  have hdescent : baseEnd_1513060 < baseStart_1513060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513071 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 7]
def baseStart_1513071 : Nat := 118140960795 + 1513071 * 2 ^ 59
def prefixEnd_1513071 : Nat := 4983230072969 + 3 ^ 40 * 1513071 * 2
def baseEnd_1513071 : Nat := 345303416612957705090675

theorem tailTrace_1513071 : CollatzResearch.WordTrace tailWord_1513071 prefixEnd_1513071 345303416612957705090675 := by
  unfold tailWord_1513071
  simp only [CollatzResearch.WordTrace]
  refine ⟨55186233101409653798683067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36790822067606435865788711 55186233101409653798683067)
  ·
    refine ⟨82779349652114480698024601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55186233101409653798683067 82779349652114480698024601)
    ·
      refine ⟨62084512239085860523518451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82779349652114480698024601 62084512239085860523518451)
      ·
        refine ⟨93126768358628790785277677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62084512239085860523518451 93126768358628790785277677)
        ·
          refine ⟨34922538134485796544479129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93126768358628790785277677 34922538134485796544479129)
          ·
            refine ⟨26191903600864347408359347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34922538134485796544479129 26191903600864347408359347)
            ·
              refine ⟨39287855401296521112539021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26191903600864347408359347 39287855401296521112539021)
              ·
                refine ⟨14732945775486195417202133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39287855401296521112539021 14732945775486195417202133)
                ·
                  refine ⟨345303416612957705090675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14732945775486195417202133 345303416612957705090675)
                  ·
                    rfl

theorem cell21_1513071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_1513071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513071 prefixEnd_1513071 := by exact prefixLift 1513071
  have htrace : WordTrace (prefixWord ++ tailWord_1513071) baseStart_1513071 baseEnd_1513071 := by
    simpa [prefixWord, tailWord_1513071, baseEnd_1513071] using wordTrace_append hprefix tailTrace_1513071
  have hstable : (prefixWord ++ tailWord_1513071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513071).length < 2 ^ (prefixWord ++ tailWord_1513071).sum := by decide
  have hdescent : baseEnd_1513071 < baseStart_1513071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513108 : List Nat := [2, 4, 2, 2, 3, 1, 1, 6]
def baseStart_1513108 : Nat := 118140960795 + 1513108 * 2 ^ 59
def prefixEnd_1513108 : Nat := 4983230072969 + 3 ^ 40 * 1513108 * 2
def baseEnd_1513108 : Nat := 115103953505684620991311

theorem tailTrace_1513108 : CollatzResearch.WordTrace tailWord_1513108 prefixEnd_1513108 115103953505684620991311 := by
  unfold tailWord_1513108
  simp only [CollatzResearch.WordTrace]
  refine ⟨27593791301137804558889989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36791721734850406078519985 27593791301137804558889989)
  ·
    refine ⟨5173835868963338354791873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27593791301137804558889989 5173835868963338354791873)
    ·
      refine ⟨3880376901722503766093905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5173835868963338354791873 3880376901722503766093905)
      ·
        refine ⟨2910282676291877824570429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3880376901722503766093905 2910282676291877824570429)
        ·
          refine ⟨1091356003609454184213911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2910282676291877824570429 1091356003609454184213911)
          ·
            refine ⟨1637034005414181276320867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091356003609454184213911 1637034005414181276320867)
            ·
              refine ⟨2455551008121271914481301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637034005414181276320867 2455551008121271914481301)
              ·
                refine ⟨115103953505684620991311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2455551008121271914481301 115103953505684620991311)
                ·
                  rfl

theorem cell21_1513108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_1513108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513108 prefixEnd_1513108 := by exact prefixLift 1513108
  have htrace : WordTrace (prefixWord ++ tailWord_1513108) baseStart_1513108 baseEnd_1513108 := by
    simpa [prefixWord, tailWord_1513108, baseEnd_1513108] using wordTrace_append hprefix tailTrace_1513108
  have hstable : (prefixWord ++ tailWord_1513108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513108).length < 2 ^ (prefixWord ++ tailWord_1513108).sum := by decide
  have hdescent : baseEnd_1513108 < baseStart_1513108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513122 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1513122 : Nat := 118140960795 + 1513122 * 2 ^ 59
def prefixEnd_1513122 : Nat := 4983230072969 + 3 ^ 40 * 1513122 * 2
def baseEnd_1513122 : Nat := 345315055507792949740571

theorem tailTrace_1513122 : CollatzResearch.WordTrace tailWord_1513122 prefixEnd_1513122 345315055507792949740571 := by
  unfold tailWord_1513122
  simp only [CollatzResearch.WordTrace]
  refine ⟨13797023306056222377197405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36792062149483259672526413 13797023306056222377197405)
  ·
    refine ⟨5173883739771083391449027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13797023306056222377197405 5173883739771083391449027)
    ·
      refine ⟨7760825609656625087173541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5173883739771083391449027 7760825609656625087173541)
      ·
        refine ⟨1455154801810617203845039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7760825609656625087173541 1455154801810617203845039)
        ·
          refine ⟨2182732202715925805767559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455154801810617203845039 2182732202715925805767559)
          ·
            refine ⟨3274098304073888708651339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182732202715925805767559 3274098304073888708651339)
            ·
              refine ⟨4911147456110833062977009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274098304073888708651339 4911147456110833062977009)
              ·
                refine ⟨3683360592083124797232757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4911147456110833062977009 3683360592083124797232757)
                ·
                  refine ⟨345315055507792949740571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3683360592083124797232757 345315055507792949740571)
                  ·
                    rfl

theorem cell21_1513122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1513122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513122 prefixEnd_1513122 := by exact prefixLift 1513122
  have htrace : WordTrace (prefixWord ++ tailWord_1513122) baseStart_1513122 baseEnd_1513122 := by
    simpa [prefixWord, tailWord_1513122, baseEnd_1513122] using wordTrace_append hprefix tailTrace_1513122
  have hstable : (prefixWord ++ tailWord_1513122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513122).length < 2 ^ (prefixWord ++ tailWord_1513122).sum := by decide
  have hdescent : baseEnd_1513122 < baseStart_1513122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513274 : List Nat := [3, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_1513274 : Nat := 118140960795 + 1513274 * 2 ^ 59
def prefixEnd_1513274 : Nat := 4983230072969 + 3 ^ 40 * 1513274 * 2
def baseEnd_1513274 : Nat := 345349743978674463206927

theorem tailTrace_1513274 : CollatzResearch.WordTrace tailWord_1513274 prefixEnd_1513274 345349743978674463206927 := by
  unfold tailWord_1513274
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798409279918554867080719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36795758079782812978881917 13798409279918554867080719)
  ·
    refine ⟨20697613919877832300621079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13798409279918554867080719 20697613919877832300621079)
    ·
      refine ⟨31046420879816748450931619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20697613919877832300621079 31046420879816748450931619)
      ·
        refine ⟨46569631319725122676397429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31046420879816748450931619 46569631319725122676397429)
        ·
          refine ⟨4365902936224230250912259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46569631319725122676397429 4365902936224230250912259)
          ·
            refine ⟨6548854404336345376368389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4365902936224230250912259 6548854404336345376368389)
            ·
              refine ⟨1227910200813064758069073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6548854404336345376368389 1227910200813064758069073)
              ·
                refine ⟨920932650609798568551805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227910200813064758069073 920932650609798568551805)
                ·
                  refine ⟨345349743978674463206927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920932650609798568551805 345349743978674463206927)
                  ·
                    rfl

theorem cell21_1513274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_1513274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513274 prefixEnd_1513274 := by exact prefixLift 1513274
  have htrace : WordTrace (prefixWord ++ tailWord_1513274) baseStart_1513274 baseEnd_1513274 := by
    simpa [prefixWord, tailWord_1513274, baseEnd_1513274] using wordTrace_append hprefix tailTrace_1513274
  have hstable : (prefixWord ++ tailWord_1513274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513274).length < 2 ^ (prefixWord ++ tailWord_1513274).sum := by decide
  have hdescent : baseEnd_1513274 < baseStart_1513274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513322 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_1513322 : Nat := 118140960795 + 1513322 * 2 ^ 59
def prefixEnd_1513322 : Nat := 4983230072969 + 3 ^ 40 * 1513322 * 2
def baseEnd_1513322 : Nat := 345360698232637046406829

theorem tailTrace_1513322 : CollatzResearch.WordTrace tailWord_1513322 prefixEnd_1513322 345360698232637046406829 := by
  unfold tailWord_1513322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798846955875080916517555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36796925215666882444046813 13798846955875080916517555)
  ·
    refine ⟨20698270433812621374776333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13798846955875080916517555 20698270433812621374776333)
    ·
      refine ⟨7761851412679733015541125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20698270433812621374776333 7761851412679733015541125)
      ·
        refine ⟨1455347139877449940413961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7761851412679733015541125 1455347139877449940413961)
        ·
          refine ⟨1091510354908087455310471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455347139877449940413961 1091510354908087455310471)
          ·
            refine ⟨1637265532362131182965707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091510354908087455310471 1637265532362131182965707)
            ·
              refine ⟨2455898298543196774448561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637265532362131182965707 2455898298543196774448561)
              ·
                refine ⟨1841923723907397580836421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455898298543196774448561 1841923723907397580836421)
                ·
                  refine ⟨345360698232637046406829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841923723907397580836421 345360698232637046406829)
                  ·
                    rfl

theorem cell21_1513322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_1513322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513322 prefixEnd_1513322 := by exact prefixLift 1513322
  have htrace : WordTrace (prefixWord ++ tailWord_1513322) baseStart_1513322 baseEnd_1513322 := by
    simpa [prefixWord, tailWord_1513322, baseEnd_1513322] using wordTrace_append hprefix tailTrace_1513322
  have hstable : (prefixWord ++ tailWord_1513322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513322).length < 2 ^ (prefixWord ++ tailWord_1513322).sum := by decide
  have hdescent : baseEnd_1513322 < baseStart_1513322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513333 : List Nat := [1, 3, 4, 1, 1, 1, 1, 6, 3]
def baseStart_1513333 : Nat := 118140960795 + 1513333 * 2 ^ 59
def prefixEnd_1513333 : Nat := 4983230072969 + 3 ^ 40 * 1513333 * 2
def baseEnd_1513333 : Nat := 345363208582503471723473

theorem tailTrace_1513333 : CollatzResearch.WordTrace tailWord_1513333 prefixEnd_1513333 345363208582503471723473 := by
  unfold tailWord_1513333
  simp only [CollatzResearch.WordTrace]
  refine ⟨55195789026460472544720653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36797192684306981696480435 55195789026460472544720653)
  ·
    refine ⟨20698420884922677204270245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55195789026460472544720653 20698420884922677204270245)
    ·
      refine ⟨3880953915923001975800671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20698420884922677204270245 3880953915923001975800671)
      ·
        refine ⟨5821430873884502963701007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880953915923001975800671 5821430873884502963701007)
        ·
          refine ⟨8732146310826754445551511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5821430873884502963701007 8732146310826754445551511)
          ·
            refine ⟨13098219466240131668327267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8732146310826754445551511 13098219466240131668327267)
            ·
              refine ⟨19647329199360197502490901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13098219466240131668327267 19647329199360197502490901)
              ·
                refine ⟨920968556220009257929261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19647329199360197502490901 920968556220009257929261)
                ·
                  refine ⟨345363208582503471723473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920968556220009257929261 345363208582503471723473)
                  ·
                    rfl

theorem cell21_1513333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_1513333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513333 prefixEnd_1513333 := by exact prefixLift 1513333
  have htrace : WordTrace (prefixWord ++ tailWord_1513333) baseStart_1513333 baseEnd_1513333 := by
    simpa [prefixWord, tailWord_1513333, baseEnd_1513333] using wordTrace_append hprefix tailTrace_1513333
  have hstable : (prefixWord ++ tailWord_1513333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513333).length < 2 ^ (prefixWord ++ tailWord_1513333).sum := by decide
  have hdescent : baseEnd_1513333 < baseStart_1513333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513344 : List Nat := [2, 1, 1, 2, 1, 2, 4, 8]
def baseStart_1513344 : Nat := 118140960795 + 1513344 * 2 ^ 59
def prefixEnd_1513344 : Nat := 4983230072969 + 3 ^ 40 * 1513344 * 2
def baseEnd_1513344 : Nat := 115121906310789965680039

theorem tailTrace_1513344 : CollatzResearch.WordTrace tailWord_1513344 prefixEnd_1513344 115121906310789965680039 := by
  unfold tailWord_1513344
  simp only [CollatzResearch.WordTrace]
  refine ⟨27598095114710310711685543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36797460152947080948914057 27598095114710310711685543)
  ·
    refine ⟨41397142672065466067528315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27598095114710310711685543 41397142672065466067528315)
    ·
      refine ⟨62095714008098199101292473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41397142672065466067528315 62095714008098199101292473)
      ·
        refine ⟨46571785506073649325969355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62095714008098199101292473 46571785506073649325969355)
        ·
          refine ⟨69857678259110473988954033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46571785506073649325969355 69857678259110473988954033)
          ·
            refine ⟨52393258694332855491715525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69857678259110473988954033 52393258694332855491715525)
            ·
              refine ⟨9823736005187410404696661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52393258694332855491715525 9823736005187410404696661)
              ·
                refine ⟨115121906310789965680039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9823736005187410404696661 115121906310789965680039)
                ·
                  rfl

theorem cell21_1513344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_1513344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513344 prefixEnd_1513344 := by exact prefixLift 1513344
  have htrace : WordTrace (prefixWord ++ tailWord_1513344) baseStart_1513344 baseEnd_1513344 := by
    simpa [prefixWord, tailWord_1513344, baseEnd_1513344] using wordTrace_append hprefix tailTrace_1513344
  have hstable : (prefixWord ++ tailWord_1513344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513344).length < 2 ^ (prefixWord ++ tailWord_1513344).sum := by decide
  have hdescent : baseEnd_1513344 < baseStart_1513344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513361 : List Nat := [1, 2, 2, 1, 1, 1, 8, 5]
def baseStart_1513361 : Nat := 118140960795 + 1513361 * 2 ^ 59
def prefixEnd_1513361 : Nat := 4983230072969 + 3 ^ 40 * 1513361 * 2
def baseEnd_1513361 : Nat := 115123199521327215085583

theorem tailTrace_1513361 : CollatzResearch.WordTrace tailWord_1513361 prefixEnd_1513361 115123199521327215085583 := by
  unfold tailWord_1513361
  simp only [CollatzResearch.WordTrace]
  refine ⟨55196810270359033326739937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36797873513572688884493291 55196810270359033326739937)
  ·
    refine ⟨41397607702769274995054953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55196810270359033326739937 41397607702769274995054953)
    ·
      refine ⟨31048205777076956246291215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41397607702769274995054953 31048205777076956246291215)
      ·
        refine ⟨46572308665615434369436823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31048205777076956246291215 46572308665615434369436823)
        ·
          refine ⟨69858462998423151554155235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46572308665615434369436823 69858462998423151554155235)
          ·
            refine ⟨104787694497634727331232853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69858462998423151554155235 104787694497634727331232853)
            ·
              refine ⟨1227980794894156960912885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 104787694497634727331232853 1227980794894156960912885)
              ·
                refine ⟨115123199521327215085583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1227980794894156960912885 115123199521327215085583)
                ·
                  rfl

theorem cell21_1513361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 5].length) (baseStart_1513361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513361 prefixEnd_1513361 := by exact prefixLift 1513361
  have htrace : WordTrace (prefixWord ++ tailWord_1513361) baseStart_1513361 baseEnd_1513361 := by
    simpa [prefixWord, tailWord_1513361, baseEnd_1513361] using wordTrace_append hprefix tailTrace_1513361
  have hstable : (prefixWord ++ tailWord_1513361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513361).length < 2 ^ (prefixWord ++ tailWord_1513361).sum := by decide
  have hdescent : baseEnd_1513361 < baseStart_1513361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513378 : List Nat := [3, 3, 1, 2, 3, 2, 7]
def baseStart_1513378 : Nat := 118140960795 + 1513378 * 2 ^ 59
def prefixEnd_1513378 : Nat := 4983230072969 + 3 ^ 40 * 1513378 * 2
def baseEnd_1513378 : Nat := 38374830910621488163709

theorem tailTrace_1513378 : CollatzResearch.WordTrace tailWord_1513378 prefixEnd_1513378 38374830910621488163709 := by
  unfold tailWord_1513378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13799357577824361307527197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36798286874198296820072525 13799357577824361307527197)
  ·
    refine ⟨5174759091684135490322699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13799357577824361307527197 5174759091684135490322699)
    ·
      refine ⟨7762138637526203235484049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5174759091684135490322699 7762138637526203235484049)
      ·
        refine ⟨5821603978144652426613037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7762138637526203235484049 5821603978144652426613037)
        ·
          refine ⟨2183101491804244659979889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5821603978144652426613037 2183101491804244659979889)
          ·
            refine ⟨1637326118853183494984917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183101491804244659979889 1637326118853183494984917)
            ·
              refine ⟨38374830910621488163709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1637326118853183494984917 38374830910621488163709)
              ·
                rfl

theorem cell21_1513378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 7].length) (baseStart_1513378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513378 prefixEnd_1513378 := by exact prefixLift 1513378
  have htrace : WordTrace (prefixWord ++ tailWord_1513378) baseStart_1513378 baseEnd_1513378 := by
    simpa [prefixWord, tailWord_1513378, baseEnd_1513378] using wordTrace_append hprefix tailTrace_1513378
  have hstable : (prefixWord ++ tailWord_1513378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513378).length < 2 ^ (prefixWord ++ tailWord_1513378).sum := by decide
  have hdescent : baseEnd_1513378 < baseStart_1513378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513384 : List Nat := [2, 1, 6, 2, 1, 1, 3, 2, 3]
def baseStart_1513384 : Nat := 118140960795 + 1513384 * 2 ^ 59
def prefixEnd_1513384 : Nat := 4983230072969 + 3 ^ 40 * 1513384 * 2
def baseEnd_1513384 : Nat := 345374847477338716373369

theorem tailTrace_1513384 : CollatzResearch.WordTrace tailWord_1513384 prefixEnd_1513384 345374847477338716373369 := by
  unfold tailWord_1513384
  simp only [CollatzResearch.WordTrace]
  refine ⟨27598824574637854127413603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36798432766183805503218137 27598824574637854127413603)
  ·
    refine ⟨41398236861956781191120405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27598824574637854127413603 41398236861956781191120405)
    ·
      refine ⟨1940542352904224118333769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41398236861956781191120405 1940542352904224118333769)
      ·
        refine ⟨1455406764678168088750327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1940542352904224118333769 1455406764678168088750327)
        ·
          refine ⟨2183110147017252133125491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455406764678168088750327 2183110147017252133125491)
          ·
            refine ⟨3274665220525878199688237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183110147017252133125491 3274665220525878199688237)
            ·
              refine ⟨1227999457697204324883089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3274665220525878199688237 1227999457697204324883089)
              ·
                refine ⟨920999593272903243662317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227999457697204324883089 920999593272903243662317)
                ·
                  refine ⟨345374847477338716373369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920999593272903243662317 345374847477338716373369)
                  ·
                    rfl

theorem cell21_1513384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_1513384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513384 prefixEnd_1513384 := by exact prefixLift 1513384
  have htrace : WordTrace (prefixWord ++ tailWord_1513384) baseStart_1513384 baseEnd_1513384 := by
    simpa [prefixWord, tailWord_1513384, baseEnd_1513384] using wordTrace_append hprefix tailTrace_1513384
  have hstable : (prefixWord ++ tailWord_1513384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513384).length < 2 ^ (prefixWord ++ tailWord_1513384).sum := by decide
  have hdescent : baseEnd_1513384 < baseStart_1513384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513437 : List Nat := [1, 4, 3, 1, 3, 9]
def baseStart_1513437 : Nat := 118140960795 + 1513437 * 2 ^ 59
def prefixEnd_1513437 : Nat := 4983230072969 + 3 ^ 40 * 1513437 * 2
def baseEnd_1513437 : Nat := 12792108992571200073701

theorem tailTrace_1513437 : CollatzResearch.WordTrace tailWord_1513437 prefixEnd_1513437 12792108992571200073701 := by
  unfold tailWord_1513437
  simp only [CollatzResearch.WordTrace]
  refine ⟨55199582218083698306506565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36799721478722465537671043 55199582218083698306506565)
  ·
    refine ⟨10349921665890693432469981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55199582218083698306506565 10349921665890693432469981)
    ·
      refine ⟨3881220624709010037176243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10349921665890693432469981 3881220624709010037176243)
      ·
        refine ⟨5821830937063515055764365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3881220624709010037176243 5821830937063515055764365)
        ·
          refine ⟨2183186601398818145911637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5821830937063515055764365 2183186601398818145911637)
          ·
            refine ⟨12792108992571200073701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2183186601398818145911637 12792108992571200073701)
            ·
              rfl

theorem cell21_1513437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 9].length) (baseStart_1513437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513437 prefixEnd_1513437 := by exact prefixLift 1513437
  have htrace : WordTrace (prefixWord ++ tailWord_1513437) baseStart_1513437 baseEnd_1513437 := by
    simpa [prefixWord, tailWord_1513437, baseEnd_1513437] using wordTrace_append hprefix tailTrace_1513437
  have hstable : (prefixWord ++ tailWord_1513437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513437).length < 2 ^ (prefixWord ++ tailWord_1513437).sum := by decide
  have hdescent : baseEnd_1513437 < baseStart_1513437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513454 : List Nat := [4, 1, 2, 1, 3, 3, 1, 6]
def baseStart_1513454 : Nat := 118140960795 + 1513454 * 2 ^ 59
def prefixEnd_1513454 : Nat := 4983230072969 + 3 ^ 40 * 1513454 * 2
def baseEnd_1513454 : Nat := 115130274143678050068853

theorem tailTrace_1513454 : CollatzResearch.WordTrace tailWord_1513454 prefixEnd_1513454 115130274143678050068853 := by
  unfold tailWord_1513454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900025282377763776234427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36800134839348073473250277 6900025282377763776234427)
  ·
    refine ⟨10350037923566645664351641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6900025282377763776234427 10350037923566645664351641)
    ·
      refine ⟨7762528442674984248263731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10350037923566645664351641 7762528442674984248263731)
      ·
        refine ⟨11643792664012476372395597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7762528442674984248263731 11643792664012476372395597)
        ·
          refine ⟨4366422249004678639648349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11643792664012476372395597 4366422249004678639648349)
          ·
            refine ⟨1637408343376754489868131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4366422249004678639648349 1637408343376754489868131)
            ·
              refine ⟨2456112515065131734802197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637408343376754489868131 2456112515065131734802197)
              ·
                refine ⟨115130274143678050068853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2456112515065131734802197 115130274143678050068853)
                ·
                  rfl

theorem cell21_1513454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_1513454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513454 prefixEnd_1513454 := by exact prefixLift 1513454
  have htrace : WordTrace (prefixWord ++ tailWord_1513454) baseStart_1513454 baseEnd_1513454 := by
    simpa [prefixWord, tailWord_1513454, baseEnd_1513454] using wordTrace_append hprefix tailTrace_1513454
  have hstable : (prefixWord ++ tailWord_1513454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513454).length < 2 ^ (prefixWord ++ tailWord_1513454).sum := by decide
  have hdescent : baseEnd_1513454 < baseStart_1513454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513496 : List Nat := [2, 1, 2, 3, 2, 1, 10]
def baseStart_1513496 : Nat := 118140960795 + 1513496 * 2 ^ 59
def prefixEnd_1513496 : Nat := 4983230072969 + 3 ^ 40 * 1513496 * 2
def baseEnd_1513496 : Nat := 38377823044805712278497

theorem tailTrace_1513496 : CollatzResearch.WordTrace tailWord_1513496 prefixEnd_1513496 38377823044805712278497 := by
  unfold tailWord_1513496
  simp only [CollatzResearch.WordTrace]
  refine ⟨27600867062434975691452171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36801156083246634255269561 27600867062434975691452171)
  ·
    refine ⟨41401300593652463537178257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27600867062434975691452171 41401300593652463537178257)
    ·
      refine ⟨31050975445239347652883693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41401300593652463537178257 31050975445239347652883693)
      ·
        refine ⟨11644115791964755369831385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31050975445239347652883693 11644115791964755369831385)
        ·
          refine ⟨8733086843973566527373539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11644115791964755369831385 8733086843973566527373539)
          ·
            refine ⟨13099630265960349791060309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8733086843973566527373539 13099630265960349791060309)
            ·
              refine ⟨38377823044805712278497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13099630265960349791060309 38377823044805712278497)
              ·
                rfl

theorem cell21_1513496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 10].length) (baseStart_1513496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513496 prefixEnd_1513496 := by exact prefixLift 1513496
  have htrace : WordTrace (prefixWord ++ tailWord_1513496) baseStart_1513496 baseEnd_1513496 := by
    simpa [prefixWord, tailWord_1513496, baseEnd_1513496] using wordTrace_append hprefix tailTrace_1513496
  have hstable : (prefixWord ++ tailWord_1513496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513496).length < 2 ^ (prefixWord ++ tailWord_1513496).sum := by decide
  have hdescent : baseEnd_1513496 < baseStart_1513496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513527 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 5]
def baseStart_1513527 : Nat := 118140960795 + 1513527 * 2 ^ 59
def prefixEnd_1513527 : Nat := 4983230072969 + 3 ^ 40 * 1513527 * 2
def baseEnd_1513527 : Nat := 345407482025602245489743

theorem tailTrace_1513527 : CollatzResearch.WordTrace tailWord_1513527 prefixEnd_1513527 345407482025602245489743 := by
  unfold tailWord_1513527
  simp only [CollatzResearch.WordTrace]
  refine ⟨55202864787757643677282835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36801909858505095784855223 55202864787757643677282835)
  ·
    refine ⟨82804297181636465515924253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55202864787757643677282835 82804297181636465515924253)
    ·
      refine ⟨31051611443113674568471595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82804297181636465515924253 31051611443113674568471595)
      ·
        refine ⟨46577417164670511852707393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31051611443113674568471595 46577417164670511852707393)
        ·
          refine ⟨34933062873502883889530545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46577417164670511852707393 34933062873502883889530545)
          ·
            refine ⟨26199797155127162917147909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34933062873502883889530545 26199797155127162917147909)
            ·
              refine ⟨4912461966586343046965233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26199797155127162917147909 4912461966586343046965233)
              ·
                refine ⟨3684346474939757285223925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4912461966586343046965233 3684346474939757285223925)
                ·
                  refine ⟨345407482025602245489743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684346474939757285223925 345407482025602245489743)
                  ·
                    rfl

theorem cell21_1513527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_1513527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513527 prefixEnd_1513527 := by exact prefixLift 1513527
  have htrace : WordTrace (prefixWord ++ tailWord_1513527) baseStart_1513527 baseEnd_1513527 := by
    simpa [prefixWord, tailWord_1513527, baseEnd_1513527] using wordTrace_append hprefix tailTrace_1513527
  have hstable : (prefixWord ++ tailWord_1513527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513527).length < 2 ^ (prefixWord ++ tailWord_1513527).sum := by decide
  have hdescent : baseEnd_1513527 < baseStart_1513527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513544 : List Nat := [2, 1, 3, 1, 1, 1, 2, 7, 3]
def baseStart_1513544 : Nat := 118140960795 + 1513544 * 2 ^ 59
def prefixEnd_1513544 : Nat := 4983230072969 + 3 ^ 40 * 1513544 * 2
def baseEnd_1513544 : Nat := 345411361657213993706375

theorem tailTrace_1513544 : CollatzResearch.WordTrace tailWord_1513544 prefixEnd_1513544 345411361657213993706375 := by
  unfold tailWord_1513544
  simp only [CollatzResearch.WordTrace]
  refine ⟨27601742414348027790325843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36802323219130703720434457 27601742414348027790325843)
  ·
    refine ⟨41402613621522041685488765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27601742414348027790325843 41402613621522041685488765)
    ·
      refine ⟨15525980108070765632058287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41402613621522041685488765 15525980108070765632058287)
      ·
        refine ⟨23288970162106148448087431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15525980108070765632058287 23288970162106148448087431)
        ·
          refine ⟨34933455243159222672131147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23288970162106148448087431 34933455243159222672131147)
          ·
            refine ⟨52400182864738834008196721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34933455243159222672131147 52400182864738834008196721)
            ·
              refine ⟨39300137148554125506147541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52400182864738834008196721 39300137148554125506147541)
              ·
                refine ⟨921096964419237316550333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39300137148554125506147541 921096964419237316550333)
                ·
                  refine ⟨345411361657213993706375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921096964419237316550333 345411361657213993706375)
                  ·
                    rfl

theorem cell21_1513544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_1513544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513544 prefixEnd_1513544 := by exact prefixLift 1513544
  have htrace : WordTrace (prefixWord ++ tailWord_1513544) baseStart_1513544 baseEnd_1513544 := by
    simpa [prefixWord, tailWord_1513544, baseEnd_1513544] using wordTrace_append hprefix tailTrace_1513544
  have hstable : (prefixWord ++ tailWord_1513544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513544).length < 2 ^ (prefixWord ++ tailWord_1513544).sum := by decide
  have hdescent : baseEnd_1513544 < baseStart_1513544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513561 : List Nat := [1, 2, 1, 2, 2, 1, 7, 2, 3]
def baseStart_1513561 : Nat := 118140960795 + 1513561 * 2 ^ 59
def prefixEnd_1513561 : Nat := 4983230072969 + 3 ^ 40 * 1513561 * 2
def baseEnd_1513561 : Nat := 345415241288825741923007

theorem tailTrace_1513561 : CollatzResearch.WordTrace tailWord_1513561 prefixEnd_1513561 345415241288825741923007 := by
  unfold tailWord_1513561
  simp only [CollatzResearch.WordTrace]
  refine ⟨55204104869634467484020537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36802736579756311656013691 55204104869634467484020537)
  ·
    refine ⟨41403078652225850613015403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55204104869634467484020537 41403078652225850613015403)
    ·
      refine ⟨62104617978338775919523105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41403078652225850613015403 62104617978338775919523105)
      ·
        refine ⟨46578463483754081939642329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62104617978338775919523105 46578463483754081939642329)
        ·
          refine ⟨34933847612815561454731747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46578463483754081939642329 34933847612815561454731747)
          ·
            refine ⟨52400771419223342182097621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34933847612815561454731747 52400771419223342182097621)
            ·
              refine ⟨1228143080138047082392913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 52400771419223342182097621 1228143080138047082392913)
              ·
                refine ⟨921107310103535311794685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228143080138047082392913 921107310103535311794685)
                ·
                  refine ⟨345415241288825741923007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921107310103535311794685 345415241288825741923007)
                  ·
                    rfl

theorem cell21_1513561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_1513561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513561 prefixEnd_1513561 := by exact prefixLift 1513561
  have htrace : WordTrace (prefixWord ++ tailWord_1513561) baseStart_1513561 baseEnd_1513561 := by
    simpa [prefixWord, tailWord_1513561, baseEnd_1513561] using wordTrace_append hprefix tailTrace_1513561
  have hstable : (prefixWord ++ tailWord_1513561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513561).length < 2 ^ (prefixWord ++ tailWord_1513561).sum := by decide
  have hdescent : baseEnd_1513561 < baseStart_1513561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513572 : List Nat := [2, 3, 1, 1, 2, 1, 3, 8]
def baseStart_1513572 : Nat := 118140960795 + 1513572 * 2 ^ 59
def prefixEnd_1513572 : Nat := 4983230072969 + 3 ^ 40 * 1513572 * 2
def baseEnd_1513572 : Nat := 115139250546230722413217

theorem tailTrace_1513572 : CollatzResearch.WordTrace tailWord_1513572 prefixEnd_1513572 115139250546230722413217 := by
  unfold tailWord_1513572
  simp only [CollatzResearch.WordTrace]
  refine ⟨27602253036297308181335485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36803004048396410908447313 27602253036297308181335485)
  ·
    refine ⟨10350844888611490568000807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27602253036297308181335485 10350844888611490568000807)
    ·
      refine ⟨15526267332917235852001211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10350844888611490568000807 15526267332917235852001211)
      ·
        refine ⟨23289400999375853778001817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15526267332917235852001211 23289400999375853778001817)
        ·
          refine ⟨17467050749531890333501363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23289400999375853778001817 17467050749531890333501363)
          ·
            refine ⟨26200576124297835500252045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17467050749531890333501363 26200576124297835500252045)
            ·
              refine ⟨9825216046611688312594517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26200576124297835500252045 9825216046611688312594517)
              ·
                refine ⟨115139250546230722413217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9825216046611688312594517 115139250546230722413217)
                ·
                  rfl

theorem cell21_1513572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_1513572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513572 prefixEnd_1513572 := by exact prefixLift 1513572
  have htrace : WordTrace (prefixWord ++ tailWord_1513572) baseStart_1513572 baseEnd_1513572 := by
    simpa [prefixWord, tailWord_1513572, baseEnd_1513572] using wordTrace_append hprefix tailTrace_1513572
  have hstable : (prefixWord ++ tailWord_1513572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513572).length < 2 ^ (prefixWord ++ tailWord_1513572).sum := by decide
  have hdescent : baseEnd_1513572 < baseStart_1513572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513668 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1513668 : Nat := 118140960795 + 1513668 * 2 ^ 59
def prefixEnd_1513668 : Nat := 4983230072969 + 3 ^ 40 * 1513668 * 2
def baseEnd_1513668 : Nat := 345439660146617333639455

theorem tailTrace_1513668 : CollatzResearch.WordTrace tailWord_1513668 prefixEnd_1513668 345439660146617333639455 := by
  unfold tailWord_1513668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27604003740123412379082829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36805338320164549838777105 27604003740123412379082829)
  ·
    refine ⟨10351501402546279642156061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27604003740123412379082829 10351501402546279642156061)
    ·
      refine ⟨3881813025954854865808523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10351501402546279642156061 3881813025954854865808523)
      ·
        refine ⟨5822719538932282298712785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3881813025954854865808523 5822719538932282298712785)
        ·
          refine ⟨4367039654199211724034589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5822719538932282298712785 4367039654199211724034589)
          ·
            refine ⟨1637639870324704396512971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4367039654199211724034589 1637639870324704396512971)
            ·
              refine ⟨2456459805487056594769457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637639870324704396512971 2456459805487056594769457)
              ·
                refine ⟨1842344854115292446077093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456459805487056594769457 1842344854115292446077093)
                ·
                  refine ⟨345439660146617333639455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842344854115292446077093 345439660146617333639455)
                  ·
                    rfl

theorem cell21_1513668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1513668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513668 prefixEnd_1513668 := by exact prefixLift 1513668
  have htrace : WordTrace (prefixWord ++ tailWord_1513668) baseStart_1513668 baseEnd_1513668 := by
    simpa [prefixWord, tailWord_1513668, baseEnd_1513668] using wordTrace_append hprefix tailTrace_1513668
  have hstable : (prefixWord ++ tailWord_1513668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513668).length < 2 ^ (prefixWord ++ tailWord_1513668).sum := by decide
  have hdescent : baseEnd_1513668 < baseStart_1513668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513679 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 5]
def baseStart_1513679 : Nat := 118140960795 + 1513679 * 2 ^ 59
def prefixEnd_1513679 : Nat := 4983230072969 + 3 ^ 40 * 1513679 * 2
def baseEnd_1513679 : Nat := 345442170496483758956099

theorem tailTrace_1513679 : CollatzResearch.WordTrace tailWord_1513679 prefixEnd_1513679 345442170496483758956099 := by
  unfold tailWord_1513679
  simp only [CollatzResearch.WordTrace]
  refine ⟨55208408683206973636816091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36805605788804649091210727 55208408683206973636816091)
  ·
    refine ⟨82812613024810460455224137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55208408683206973636816091 82812613024810460455224137)
    ·
      refine ⟨62109459768607845341418103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82812613024810460455224137 62109459768607845341418103)
      ·
        refine ⟨93164189652911768012127155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62109459768607845341418103 93164189652911768012127155)
        ·
          refine ⟨139746284479367652018190733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93164189652911768012127155 139746284479367652018190733)
          ·
            refine ⟨52404856679762869506821525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139746284479367652018190733 52404856679762869506821525)
            ·
              refine ⟨2456477656863884508132259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52404856679762869506821525 2456477656863884508132259)
              ·
                refine ⟨3684716485295826762198389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456477656863884508132259 3684716485295826762198389)
                ·
                  refine ⟨345442170496483758956099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3684716485295826762198389 345442170496483758956099)
                  ·
                    rfl

theorem cell21_1513679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_1513679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513679 prefixEnd_1513679 := by exact prefixLift 1513679
  have htrace : WordTrace (prefixWord ++ tailWord_1513679) baseStart_1513679 baseEnd_1513679 := by
    simpa [prefixWord, tailWord_1513679, baseEnd_1513679] using wordTrace_append hprefix tailTrace_1513679
  have hstable : (prefixWord ++ tailWord_1513679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513679).length < 2 ^ (prefixWord ++ tailWord_1513679).sum := by decide
  have hdescent : baseEnd_1513679 < baseStart_1513679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513699 : List Nat := [1, 1, 1, 8, 1, 2, 2, 5]
def baseStart_1513699 : Nat := 118140960795 + 1513699 * 2 ^ 59
def prefixEnd_1513699 : Nat := 4983230072969 + 3 ^ 40 * 1513699 * 2
def baseEnd_1513699 : Nat := 115148911589656056207575

theorem tailTrace_1513699 : CollatzResearch.WordTrace tailWord_1513699 prefixEnd_1513699 115148911589656056207575 := by
  unfold tailWord_1513699
  simp only [CollatzResearch.WordTrace]
  refine ⟨55209138143134517052544151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36806092095423011368362767 55209138143134517052544151)
  ·
    refine ⟨82813707214701775578816227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55209138143134517052544151 82813707214701775578816227)
    ·
      refine ⟨124220560822052663368224341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82813707214701775578816227 124220560822052663368224341)
      ·
        refine ⟨1455709697133429648846379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 124220560822052663368224341 1455709697133429648846379)
        ·
          refine ⟨2183564545700144473269569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455709697133429648846379 2183564545700144473269569)
          ·
            refine ⟨1637673409275108354952177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183564545700144473269569 1637673409275108354952177)
            ·
              refine ⟨1228255056956331266214133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637673409275108354952177 1228255056956331266214133)
              ·
                refine ⟨115148911589656056207575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1228255056956331266214133 115148911589656056207575)
                ·
                  rfl

theorem cell21_1513699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 5].length) (baseStart_1513699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513699 prefixEnd_1513699 := by exact prefixLift 1513699
  have htrace : WordTrace (prefixWord ++ tailWord_1513699) baseStart_1513699 baseEnd_1513699 := by
    simpa [prefixWord, tailWord_1513699, baseEnd_1513699] using wordTrace_append hprefix tailTrace_1513699
  have hstable : (prefixWord ++ tailWord_1513699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513699).length < 2 ^ (prefixWord ++ tailWord_1513699).sum := by decide
  have hdescent : baseEnd_1513699 < baseStart_1513699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513724 : List Nat := [2, 2, 2, 1, 4, 1, 9]
def baseStart_1513724 : Nat := 118140960795 + 1513724 * 2 ^ 59
def prefixEnd_1513724 : Nat := 4983230072969 + 3 ^ 40 * 1513724 * 2
def baseEnd_1513724 : Nat := 38383604456619297856223

theorem tailTrace_1513724 : CollatzResearch.WordTrace tailWord_1513724 prefixEnd_1513724 38383604456619297856223 := by
  unfold tailWord_1513724
  simp only [CollatzResearch.WordTrace]
  refine ⟨27605024984021973161102113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36806699978695964214802817 27605024984021973161102113)
  ·
    refine ⟨20703768738016479870826585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27605024984021973161102113 20703768738016479870826585)
    ·
      refine ⟨15527826553512359903119939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20703768738016479870826585 15527826553512359903119939)
      ·
        refine ⟨23291739830268539854679909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15527826553512359903119939 23291739830268539854679909)
        ·
          refine ⟨4367201218175351222752483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23291739830268539854679909 4367201218175351222752483)
          ·
            refine ⟨6550801827263026834128725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367201218175351222752483 6550801827263026834128725)
            ·
              refine ⟨38383604456619297856223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6550801827263026834128725 38383604456619297856223)
              ·
                rfl

theorem cell21_1513724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 9].length) (baseStart_1513724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513724 prefixEnd_1513724 := by exact prefixLift 1513724
  have htrace : WordTrace (prefixWord ++ tailWord_1513724) baseStart_1513724 baseEnd_1513724 := by
    simpa [prefixWord, tailWord_1513724, baseEnd_1513724] using wordTrace_append hprefix tailTrace_1513724
  have hstable : (prefixWord ++ tailWord_1513724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513724).length < 2 ^ (prefixWord ++ tailWord_1513724).sum := by decide
  have hdescent : baseEnd_1513724 < baseStart_1513724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513758 : List Nat := [4, 3, 2, 1, 1, 1, 2, 7]
def baseStart_1513758 : Nat := 118140960795 + 1513758 * 2 ^ 59
def prefixEnd_1513758 : Nat := 4983230072969 + 3 ^ 40 * 1513758 * 2
def baseEnd_1513758 : Nat := 115153399790932392379757

theorem tailTrace_1513758 : CollatzResearch.WordTrace tailWord_1513758 prefixEnd_1513758 115153399790932392379757 := by
  unfold tailWord_1513758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901411256240096266117741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36807526699947180085961285 6901411256240096266117741)
  ·
    refine ⟨2588029221090036099794153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6901411256240096266117741 2588029221090036099794153)
    ·
      refine ⟨1941021915817527074845615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2588029221090036099794153 1941021915817527074845615)
      ·
        refine ⟨2911532873726290612268423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941021915817527074845615 2911532873726290612268423)
        ·
          refine ⟨4367299310589435918402635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911532873726290612268423 4367299310589435918402635)
          ·
            refine ⟨6550948965884153877603953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367299310589435918402635 6550948965884153877603953)
            ·
              refine ⟨4913211724413115408202965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6550948965884153877603953 4913211724413115408202965)
              ·
                refine ⟨115153399790932392379757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4913211724413115408202965 115153399790932392379757)
                ·
                  rfl

theorem cell21_1513758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_1513758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513758 prefixEnd_1513758 := by exact prefixLift 1513758
  have htrace : WordTrace (prefixWord ++ tailWord_1513758) baseStart_1513758 baseEnd_1513758 := by
    simpa [prefixWord, tailWord_1513758, baseEnd_1513758] using wordTrace_append hprefix tailTrace_1513758
  have hstable : (prefixWord ++ tailWord_1513758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513758).length < 2 ^ (prefixWord ++ tailWord_1513758).sum := by decide
  have hdescent : baseEnd_1513758 < baseStart_1513758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513786 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1513786 : Nat := 118140960795 + 1513786 * 2 ^ 59
def prefixEnd_1513786 : Nat := 4983230072969 + 3 ^ 40 * 1513786 * 2
def baseEnd_1513786 : Nat := 345466589354275350672547

theorem tailTrace_1513786 : CollatzResearch.WordTrace tailWord_1513786 prefixEnd_1513786 345466589354275350672547 := by
  unfold tailWord_1513786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803077823454832727740303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36808207529212887273974141 13803077823454832727740303)
  ·
    refine ⟨20704616735182249091610455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13803077823454832727740303 20704616735182249091610455)
    ·
      refine ⟨31056925102773373637415683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20704616735182249091610455 31056925102773373637415683)
      ·
        refine ⟨46585387654160060456123525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31056925102773373637415683 46585387654160060456123525)
        ·
          refine ⟨8734760185155011335523161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46585387654160060456123525 8734760185155011335523161)
          ·
            refine ⟨6551070138866258501642371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8734760185155011335523161 6551070138866258501642371)
            ·
              refine ⟨9826605208299387752463557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6551070138866258501642371 9826605208299387752463557)
              ·
                refine ⟨1842488476556135203586917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9826605208299387752463557 1842488476556135203586917)
                ·
                  refine ⟨345466589354275350672547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842488476556135203586917 345466589354275350672547)
                  ·
                    rfl

theorem cell21_1513786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1513786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513786 prefixEnd_1513786 := by exact prefixLift 1513786
  have htrace : WordTrace (prefixWord ++ tailWord_1513786) baseStart_1513786 baseEnd_1513786 := by
    simpa [prefixWord, tailWord_1513786, baseEnd_1513786] using wordTrace_append hprefix tailTrace_1513786
  have hstable : (prefixWord ++ tailWord_1513786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513786).length < 2 ^ (prefixWord ++ tailWord_1513786).sum := by decide
  have hdescent : baseEnd_1513786 < baseStart_1513786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513800 : List Nat := [2, 1, 3, 1, 1, 2, 5, 6]
def baseStart_1513800 : Nat := 118140960795 + 1513800 * 2 ^ 59
def prefixEnd_1513800 : Nat := 4983230072969 + 3 ^ 40 * 1513800 * 2
def baseEnd_1513800 : Nat := 115156594781671479146395

theorem tailTrace_1513800 : CollatzResearch.WordTrace tailWord_1513800 prefixEnd_1513800 115156594781671479146395 := by
  unfold tailWord_1513800
  simp only [CollatzResearch.WordTrace]
  refine ⟨27606410957884305650985427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36808547943845740867980569 27606410957884305650985427)
  ·
    refine ⟨41409616436826458476478141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27606410957884305650985427 41409616436826458476478141)
    ·
      refine ⟨15528606163809921928679303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41409616436826458476478141 15528606163809921928679303)
      ·
        refine ⟨23292909245714882893018955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15528606163809921928679303 23292909245714882893018955)
        ·
          refine ⟨34939363868572324339528433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23292909245714882893018955 34939363868572324339528433)
          ·
            refine ⟨26204522901429243254646325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34939363868572324339528433 26204522901429243254646325)
            ·
              refine ⟨2456674022008991555123093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26204522901429243254646325 2456674022008991555123093)
              ·
                refine ⟨115156594781671479146395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2456674022008991555123093 115156594781671479146395)
                ·
                  rfl

theorem cell21_1513800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_1513800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513800 prefixEnd_1513800 := by exact prefixLift 1513800
  have htrace : WordTrace (prefixWord ++ tailWord_1513800) baseStart_1513800 baseEnd_1513800 := by
    simpa [prefixWord, tailWord_1513800, baseEnd_1513800] using wordTrace_append hprefix tailTrace_1513800
  have hstable : (prefixWord ++ tailWord_1513800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513800).length < 2 ^ (prefixWord ++ tailWord_1513800).sum := by decide
  have hdescent : baseEnd_1513800 < baseStart_1513800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513955 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 4]
def baseStart_1513955 : Nat := 118140960795 + 1513955 * 2 ^ 59
def prefixEnd_1513955 : Nat := 4983230072969 + 3 ^ 40 * 1513955 * 2
def baseEnd_1513955 : Nat := 345505157456768612355535

theorem tailTrace_1513955 : CollatzResearch.WordTrace tailWord_1513955 prefixEnd_1513955 345505157456768612355535 := by
  unfold tailWord_1513955
  simp only [CollatzResearch.WordTrace]
  refine ⟨55218475230207072773863319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36812316820138048515908879 55218475230207072773863319)
  ·
    refine ⟨82827712845310609160794979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55218475230207072773863319 82827712845310609160794979)
    ·
      refine ⟨124241569267965913741192469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82827712845310609160794979 124241569267965913741192469)
      ·
        refine ⟨5823823559435902206618397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124241569267965913741192469 5823823559435902206618397)
        ·
          refine ⟨2183933834788463327481899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5823823559435902206618397 2183933834788463327481899)
          ·
            refine ⟨3275900752182694991222849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183933834788463327481899 3275900752182694991222849)
            ·
              refine ⟨2456925564137021243417137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3275900752182694991222849 2456925564137021243417137)
              ·
                refine ⟨1842694173102765932562853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456925564137021243417137 1842694173102765932562853)
                ·
                  refine ⟨345505157456768612355535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842694173102765932562853 345505157456768612355535)
                  ·
                    rfl

theorem cell21_1513955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 4].length) (baseStart_1513955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1513955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1513955 prefixEnd_1513955 := by exact prefixLift 1513955
  have htrace : WordTrace (prefixWord ++ tailWord_1513955) baseStart_1513955 baseEnd_1513955 := by
    simpa [prefixWord, tailWord_1513955, baseEnd_1513955] using wordTrace_append hprefix tailTrace_1513955
  have hstable : (prefixWord ++ tailWord_1513955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513955).length < 2 ^ (prefixWord ++ tailWord_1513955).sum := by decide
  have hdescent : baseEnd_1513955 < baseStart_1513955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514045 : List Nat := [1, 4, 1, 3, 2, 1, 4, 5]
def baseStart_1514045 : Nat := 118140960795 + 1514045 * 2 ^ 59
def prefixEnd_1514045 : Nat := 4983230072969 + 3 ^ 40 * 1514045 * 2
def baseEnd_1514045 : Nat := 115175232227649485285117

theorem tailTrace_1514045 : CollatzResearch.WordTrace tailWord_1514045 prefixEnd_1514045 115175232227649485285117 := by
  unfold tailWord_1514045
  simp only [CollatzResearch.WordTrace]
  refine ⟨55221757799881018144639589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36814505199920678763093059 55221757799881018144639589)
  ·
    refine ⟨10354079587477690902119923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55221757799881018144639589 10354079587477690902119923)
    ·
      refine ⟨15531119381216536353179885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10354079587477690902119923 15531119381216536353179885)
      ·
        refine ⟨5824169767956201132442457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15531119381216536353179885 5824169767956201132442457)
        ·
          refine ⟨4368127325967150849331843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5824169767956201132442457 4368127325967150849331843)
          ·
            refine ⟨6552190988950726273997765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368127325967150849331843 6552190988950726273997765)
            ·
              refine ⟨1228535810428261176374581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6552190988950726273997765 1228535810428261176374581)
              ·
                refine ⟨115175232227649485285117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1228535810428261176374581 115175232227649485285117)
                ·
                  rfl

theorem cell21_1514045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 5].length) (baseStart_1514045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514045 prefixEnd_1514045 := by exact prefixLift 1514045
  have htrace : WordTrace (prefixWord ++ tailWord_1514045) baseStart_1514045 baseEnd_1514045 := by
    simpa [prefixWord, tailWord_1514045, baseEnd_1514045] using wordTrace_append hprefix tailTrace_1514045
  have hstable : (prefixWord ++ tailWord_1514045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514045).length < 2 ^ (prefixWord ++ tailWord_1514045).sum := by decide
  have hdescent : baseEnd_1514045 < baseStart_1514045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514082 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1514082 : Nat := 118140960795 + 1514082 * 2 ^ 59
def prefixEnd_1514082 : Nat := 4983230072969 + 3 ^ 40 * 1514082 * 2
def baseEnd_1514082 : Nat := 345534140587044613738609

theorem tailTrace_1514082 : CollatzResearch.WordTrace tailWord_1514082 prefixEnd_1514082 345534140587044613738609 := by
  unfold tailWord_1514082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13805776825186743365934125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36815404867164648975824333 13805776825186743365934125)
  ·
    refine ⟨5177166309445028762225297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13805776825186743365934125 5177166309445028762225297)
    ·
      refine ⟨3882874732083771571668973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5177166309445028762225297 3882874732083771571668973)
      ·
        refine ⟨1456078024531414339375865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3882874732083771571668973 1456078024531414339375865)
        ·
          refine ⟨1092058518398560754531899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456078024531414339375865 1092058518398560754531899)
          ·
            refine ⟨1638087777597841131797849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092058518398560754531899 1638087777597841131797849)
            ·
              refine ⟨1228565833198380848848387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638087777597841131797849 1228565833198380848848387)
              ·
                refine ⟨1842848749797571273272581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228565833198380848848387 1842848749797571273272581)
                ·
                  refine ⟨345534140587044613738609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842848749797571273272581 345534140587044613738609)
                  ·
                    rfl

theorem cell21_1514082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1514082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514082 prefixEnd_1514082 := by exact prefixLift 1514082
  have htrace : WordTrace (prefixWord ++ tailWord_1514082) baseStart_1514082 baseEnd_1514082 := by
    simpa [prefixWord, tailWord_1514082, baseEnd_1514082] using wordTrace_append hprefix tailTrace_1514082
  have hstable : (prefixWord ++ tailWord_1514082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514082).length < 2 ^ (prefixWord ++ tailWord_1514082).sum := by decide
  have hdescent : baseEnd_1514082 < baseStart_1514082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514090 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_1514090 : Nat := 118140960795 + 1514090 * 2 ^ 59
def prefixEnd_1514090 : Nat := 4983230072969 + 3 ^ 40 * 1514090 * 2
def baseEnd_1514090 : Nat := 345535966296038377605259

theorem tailTrace_1514090 : CollatzResearch.WordTrace tailWord_1514090 prefixEnd_1514090 345535966296038377605259 := by
  unfold tailWord_1514090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13805849771179497707506931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36815599389811993886685149 13805849771179497707506931)
  ·
    refine ⟨20708774656769246561260397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13805849771179497707506931 20708774656769246561260397)
    ·
      refine ⟨7765790496288467460472649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20708774656769246561260397 7765790496288467460472649)
      ·
        refine ⟨5824342872216350595354487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7765790496288467460472649 5824342872216350595354487)
        ·
          refine ⟨8736514308324525893031731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824342872216350595354487 8736514308324525893031731)
          ·
            refine ⟨13104771462486788839547597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8736514308324525893031731 13104771462486788839547597)
            ·
              refine ⟨4914289298432545814830349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13104771462486788839547597 4914289298432545814830349)
              ·
                refine ⟨1842858486912204680561381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4914289298432545814830349 1842858486912204680561381)
                ·
                  refine ⟨345535966296038377605259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842858486912204680561381 345535966296038377605259)
                  ·
                    rfl

theorem cell21_1514090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_1514090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514090 prefixEnd_1514090 := by exact prefixLift 1514090
  have htrace : WordTrace (prefixWord ++ tailWord_1514090) baseStart_1514090 baseEnd_1514090 := by
    simpa [prefixWord, tailWord_1514090, baseEnd_1514090] using wordTrace_append hprefix tailTrace_1514090
  have hstable : (prefixWord ++ tailWord_1514090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514090).length < 2 ^ (prefixWord ++ tailWord_1514090).sum := by decide
  have hdescent : baseEnd_1514090 < baseStart_1514090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514138 : List Nat := [3, 1, 1, 6, 1, 2, 1, 6]
def baseStart_1514138 : Nat := 118140960795 + 1514138 * 2 ^ 59
def prefixEnd_1514138 : Nat := 4983230072969 + 3 ^ 40 * 1514138 * 2
def baseEnd_1514138 : Nat := 115182306850000320268387

theorem tailTrace_1514138 : CollatzResearch.WordTrace tailWord_1514138 prefixEnd_1514138 115182306850000320268387 := by
  unfold tailWord_1514138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13806287447136023756943767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36816766525696063351850045 13806287447136023756943767)
  ·
    refine ⟨20709431170704035635415651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13806287447136023756943767 20709431170704035635415651)
    ·
      refine ⟨31064146756056053453123477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20709431170704035635415651 31064146756056053453123477)
      ·
        refine ⟨1456131879190127505615163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31064146756056053453123477 1456131879190127505615163)
        ·
          refine ⟨2184197818785191258422745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456131879190127505615163 2184197818785191258422745)
          ·
            refine ⟨1638148364088893443817059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2184197818785191258422745 1638148364088893443817059)
            ·
              refine ⟨2457222546133340165725589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638148364088893443817059 2457222546133340165725589)
              ·
                refine ⟨115182306850000320268387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2457222546133340165725589 115182306850000320268387)
                ·
                  rfl

theorem cell21_1514138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_1514138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514138 prefixEnd_1514138 := by exact prefixLift 1514138
  have htrace : WordTrace (prefixWord ++ tailWord_1514138) baseStart_1514138 baseEnd_1514138 := by
    simpa [prefixWord, tailWord_1514138, baseEnd_1514138] using wordTrace_append hprefix tailTrace_1514138
  have hstable : (prefixWord ++ tailWord_1514138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514138).length < 2 ^ (prefixWord ++ tailWord_1514138).sum := by decide
  have hdescent : baseEnd_1514138 < baseStart_1514138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514180 : List Nat := [2, 3, 3, 1, 1, 3, 8]
def baseStart_1514180 : Nat := 118140960795 + 1514180 * 2 ^ 59
def prefixEnd_1514180 : Nat := 4983230072969 + 3 ^ 40 * 1514180 * 2
def baseEnd_1514180 : Nat := 38395167280246469011675

theorem tailTrace_1514180 : CollatzResearch.WordTrace tailWord_1514180 prefixEnd_1514180 38395167280246469011675 := by
  unfold tailWord_1514180
  simp only [CollatzResearch.WordTrace]
  refine ⟨27613340827195968100401997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36817787769594624133869329 27613340827195968100401997)
  ·
    refine ⟨10355002810198488037650749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27613340827195968100401997 10355002810198488037650749)
    ·
      refine ⟨3883126053824433014119031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10355002810198488037650749 3883126053824433014119031)
      ·
        refine ⟨5824689080736649521178547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3883126053824433014119031 5824689080736649521178547)
        ·
          refine ⟨8737033621104974281767821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824689080736649521178547 8737033621104974281767821)
          ·
            refine ⟨3276387607914365355662933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8737033621104974281767821 3276387607914365355662933)
            ·
              refine ⟨38395167280246469011675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3276387607914365355662933 38395167280246469011675)
              ·
                rfl

theorem cell21_1514180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 8].length) (baseStart_1514180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514180 prefixEnd_1514180 := by exact prefixLift 1514180
  have htrace : WordTrace (prefixWord ++ tailWord_1514180) baseStart_1514180 baseEnd_1514180 := by
    simpa [prefixWord, tailWord_1514180, baseEnd_1514180] using wordTrace_append hprefix tailTrace_1514180
  have hstable : (prefixWord ++ tailWord_1514180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514180).length < 2 ^ (prefixWord ++ tailWord_1514180).sum := by decide
  have hdescent : baseEnd_1514180 < baseStart_1514180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514211 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 5]
def baseStart_1514211 : Nat := 118140960795 + 1514211 * 2 ^ 59
def prefixEnd_1514211 : Nat := 4983230072969 + 3 ^ 40 * 1514211 * 2
def baseEnd_1514211 : Nat := 345563580144569056088345

theorem tailTrace_1514211 : CollatzResearch.WordTrace tailWord_1514211 prefixEnd_1514211 345563580144569056088345 := by
  unfold tailWord_1514211
  simp only [CollatzResearch.WordTrace]
  refine ⟨55227812317279628495182487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36818541544853085663454991 55227812317279628495182487)
  ·
    refine ⟨82841718475919442742773731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55227812317279628495182487 82841718475919442742773731)
    ·
      refine ⟨124262577713879164114160597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82841718475919442742773731 124262577713879164114160597)
      ·
        refine ⟨2912404165169042908925639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 124262577713879164114160597 2912404165169042908925639)
        ·
          refine ⟨4368606247753564363388459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2912404165169042908925639 4368606247753564363388459)
          ·
            refine ⟨6552909371630346545082689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368606247753564363388459 6552909371630346545082689)
            ·
              refine ⟨4914682028722759908812017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6552909371630346545082689 4914682028722759908812017)
              ·
                refine ⟨3686011521542069931609013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4914682028722759908812017 3686011521542069931609013)
                ·
                  refine ⟨345563580144569056088345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3686011521542069931609013 345563580144569056088345)
                  ·
                    rfl

theorem cell21_1514211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_1514211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514211 prefixEnd_1514211 := by exact prefixLift 1514211
  have htrace : WordTrace (prefixWord ++ tailWord_1514211) baseStart_1514211 baseEnd_1514211 := by
    simpa [prefixWord, tailWord_1514211, baseEnd_1514211] using wordTrace_append hprefix tailTrace_1514211
  have hstable : (prefixWord ++ tailWord_1514211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514211).length < 2 ^ (prefixWord ++ tailWord_1514211).sum := by decide
  have hdescent : baseEnd_1514211 < baseStart_1514211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514242 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1514242 : Nat := 118140960795 + 1514242 * 2 ^ 59
def prefixEnd_1514242 : Nat := 4983230072969 + 3 ^ 40 * 1514242 * 2
def baseEnd_1514242 : Nat := 345570654766919891071615

theorem tailTrace_1514242 : CollatzResearch.WordTrace tailWord_1514242 prefixEnd_1514242 345570654766919891071615 := by
  unfold tailWord_1514242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13807235745041830197390245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36819295320111547193040653 13807235745041830197390245)
  ·
    refine ⟨2588856702195343162010671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13807235745041830197390245 2588856702195343162010671)
    ·
      refine ⟨3883285053293014743016007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588856702195343162010671 3883285053293014743016007)
      ·
        refine ⟨5824927579939522114524011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3883285053293014743016007 5824927579939522114524011)
        ·
          refine ⟨8737391369909283171786017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824927579939522114524011 8737391369909283171786017)
          ·
            refine ⟨6553043527431962378839513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8737391369909283171786017 6553043527431962378839513)
            ·
              refine ⟨4914782645573971784129635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6553043527431962378839513 4914782645573971784129635)
              ·
                refine ⟨7372173968360957676194453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4914782645573971784129635 7372173968360957676194453)
                ·
                  refine ⟨345570654766919891071615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7372173968360957676194453 345570654766919891071615)
                  ·
                    rfl

theorem cell21_1514242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1514242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514242 prefixEnd_1514242 := by exact prefixLift 1514242
  have htrace : WordTrace (prefixWord ++ tailWord_1514242) baseStart_1514242 baseEnd_1514242 := by
    simpa [prefixWord, tailWord_1514242, baseEnd_1514242] using wordTrace_append hprefix tailTrace_1514242
  have hstable : (prefixWord ++ tailWord_1514242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514242).length < 2 ^ (prefixWord ++ tailWord_1514242).sum := by decide
  have hdescent : baseEnd_1514242 < baseStart_1514242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514363 : List Nat := [1, 1, 1, 1, 1, 5, 4, 4, 3]
def baseStart_1514363 : Nat := 118140960795 + 1514363 * 2 ^ 59
def prefixEnd_1514363 : Nat := 4983230072969 + 3 ^ 40 * 1514363 * 2
def baseEnd_1514363 : Nat := 345598268615450569554701

theorem tailTrace_1514363 : CollatzResearch.WordTrace tailWord_1514363 prefixEnd_1514363 345598268615450569554701 := by
  unfold tailWord_1514363
  simp only [CollatzResearch.WordTrace]
  refine ⟨55233356212728958454715743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36822237475152638969810495 55233356212728958454715743)
  ·
    refine ⟨82850034319093437682073615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55233356212728958454715743 82850034319093437682073615)
    ·
      refine ⟨124275051478640156523110423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82850034319093437682073615 124275051478640156523110423)
      ·
        refine ⟨186412577217960234784665635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124275051478640156523110423 186412577217960234784665635)
        ·
          refine ⟨279618865826940352176998453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186412577217960234784665635 279618865826940352176998453)
          ·
            refine ⟨26214268671275658016593605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279618865826940352176998453 26214268671275658016593605)
            ·
              refine ⟨4915175375864185878111301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26214268671275658016593605 4915175375864185878111301)
              ·
                refine ⟨921595382974534852145869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4915175375864185878111301 921595382974534852145869)
                ·
                  refine ⟨345598268615450569554701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921595382974534852145869 345598268615450569554701)
                  ·
                    rfl

theorem cell21_1514363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 3].length) (baseStart_1514363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514363 prefixEnd_1514363 := by exact prefixLift 1514363
  have htrace : WordTrace (prefixWord ++ tailWord_1514363) baseStart_1514363 baseEnd_1514363 := by
    simpa [prefixWord, tailWord_1514363, baseEnd_1514363] using wordTrace_append hprefix tailTrace_1514363
  have hstable : (prefixWord ++ tailWord_1514363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514363).length < 2 ^ (prefixWord ++ tailWord_1514363).sum := by decide
  have hdescent : baseEnd_1514363 < baseStart_1514363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514391 : List Nat := [1, 1, 3, 3, 1, 2, 3, 7]
def baseStart_1514391 : Nat := 118140960795 + 1514391 * 2 ^ 59
def prefixEnd_1514391 : Nat := 4983230072969 + 3 ^ 40 * 1514391 * 2
def baseEnd_1514391 : Nat := 115201552865642914362659

theorem tailTrace_1514391 : CollatzResearch.WordTrace tailWord_1514391 prefixEnd_1514391 115201552865642914362659 := by
  unfold tailWord_1514391
  simp only [CollatzResearch.WordTrace]
  refine ⟨55234377456627519236735027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36822918304418346157823351 55234377456627519236735027)
  ·
    refine ⟨82851566184941278855102541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55234377456627519236735027 82851566184941278855102541)
    ·
      refine ⟨31069337319352979570663453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82851566184941278855102541 31069337319352979570663453)
      ·
        refine ⟨11651001494757367338998795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31069337319352979570663453 11651001494757367338998795)
        ·
          refine ⟨17476502242136051008498193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11651001494757367338998795 17476502242136051008498193)
          ·
            refine ⟨13107376681602038256373645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17476502242136051008498193 13107376681602038256373645)
            ·
              refine ⟨4915266255600764346140117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13107376681602038256373645 4915266255600764346140117)
              ·
                refine ⟨115201552865642914362659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4915266255600764346140117 115201552865642914362659)
                ·
                  rfl

theorem cell21_1514391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 7].length) (baseStart_1514391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514391 prefixEnd_1514391 := by exact prefixLift 1514391
  have htrace : WordTrace (prefixWord ++ tailWord_1514391) baseStart_1514391 baseEnd_1514391 := by
    simpa [prefixWord, tailWord_1514391, baseEnd_1514391] using wordTrace_append hprefix tailTrace_1514391
  have hstable : (prefixWord ++ tailWord_1514391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514391).length < 2 ^ (prefixWord ++ tailWord_1514391).sum := by decide
  have hdescent : baseEnd_1514391 < baseStart_1514391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514529 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 6]
def baseStart_1514529 : Nat := 118140960795 + 1514529 * 2 ^ 59
def prefixEnd_1514529 : Nat := 4983230072969 + 3 ^ 40 * 1514529 * 2
def baseEnd_1514529 : Nat := 345636152077071169787695

theorem tailTrace_1514529 : CollatzResearch.WordTrace tailWord_1514529 prefixEnd_1514529 345636152077071169787695 := by
  unfold tailWord_1514529
  simp only [CollatzResearch.WordTrace]
  refine ⟨55239410730127568805258641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36826273820085045870172427 55239410730127568805258641)
  ·
    refine ⟨41429558047595676603943981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55239410730127568805258641 41429558047595676603943981)
    ·
      refine ⟨15536084267848378726478993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41429558047595676603943981 15536084267848378726478993)
      ·
        refine ⟨11652063200886284044859245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15536084267848378726478993 11652063200886284044859245)
        ·
          refine ⟨4369523700332356516822217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11652063200886284044859245 4369523700332356516822217)
          ·
            refine ⟨3277142775249267387616663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4369523700332356516822217 3277142775249267387616663)
            ·
              refine ⟨4915714162873901081424995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277142775249267387616663 4915714162873901081424995)
              ·
                refine ⟨7373571244310851622137493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4915714162873901081424995 7373571244310851622137493)
                ·
                  refine ⟨345636152077071169787695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7373571244310851622137493 345636152077071169787695)
                  ·
                    rfl

theorem cell21_1514529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_1514529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514529 prefixEnd_1514529 := by exact prefixLift 1514529
  have htrace : WordTrace (prefixWord ++ tailWord_1514529) baseStart_1514529 baseEnd_1514529 := by
    simpa [prefixWord, tailWord_1514529, baseEnd_1514529] using wordTrace_append hprefix tailTrace_1514529
  have hstable : (prefixWord ++ tailWord_1514529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514529).length < 2 ^ (prefixWord ++ tailWord_1514529).sum := by decide
  have hdescent : baseEnd_1514529 < baseStart_1514529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514532 : List Nat := [2, 3, 1, 4, 1, 1, 2, 4, 3]
def baseStart_1514532 : Nat := 118140960795 + 1514532 * 2 ^ 59
def prefixEnd_1514532 : Nat := 4983230072969 + 3 ^ 40 * 1514532 * 2
def baseEnd_1514532 : Nat := 345636836717943831237689

theorem tailTrace_1514532 : CollatzResearch.WordTrace tailWord_1514532 prefixEnd_1514532 345636836717943831237689 := by
  unfold tailWord_1514532
  simp only [CollatzResearch.WordTrace]
  refine ⟨27619760074558350158808925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36826346766077800211745233 27619760074558350158808925)
  ·
    refine ⟨10357410027959381309553347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27619760074558350158808925 10357410027959381309553347)
    ·
      refine ⟨15536115041939071964330021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10357410027959381309553347 15536115041939071964330021)
      ·
        refine ⟨2913021570363575993311879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15536115041939071964330021 2913021570363575993311879)
        ·
          refine ⟨4369532355545363989967819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913021570363575993311879 4369532355545363989967819)
          ·
            refine ⟨6554298533318045984951729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4369532355545363989967819 6554298533318045984951729)
            ·
              refine ⟨4915723899988534488713797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6554298533318045984951729 4915723899988534488713797)
              ·
                refine ⟨921698231247850216633837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4915723899988534488713797 921698231247850216633837)
                ·
                  refine ⟨345636836717943831237689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921698231247850216633837 345636836717943831237689)
                  ·
                    rfl

theorem cell21_1514532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_1514532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514532 prefixEnd_1514532 := by exact prefixLift 1514532
  have htrace : WordTrace (prefixWord ++ tailWord_1514532) baseStart_1514532 baseEnd_1514532 := by
    simpa [prefixWord, tailWord_1514532, baseEnd_1514532] using wordTrace_append hprefix tailTrace_1514532
  have hstable : (prefixWord ++ tailWord_1514532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514532).length < 2 ^ (prefixWord ++ tailWord_1514532).sum := by decide
  have hdescent : baseEnd_1514532 < baseStart_1514532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514546 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_1514546 : Nat := 118140960795 + 1514546 * 2 ^ 59
def prefixEnd_1514546 : Nat := 4983230072969 + 3 ^ 40 * 1514546 * 2
def baseEnd_1514546 : Nat := 345640031708682918004327

theorem tailTrace_1514546 : CollatzResearch.WordTrace tailWord_1514546 prefixEnd_1514546 345640031708682918004327 := by
  unfold tailWord_1514546
  simp only [CollatzResearch.WordTrace]
  refine ⟨13810007692766495177156873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36826687180710653805751661 13810007692766495177156873)
  ·
    refine ⟨10357505769574871382867655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13810007692766495177156873 10357505769574871382867655)
    ·
      refine ⟨15536258654362307074301483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10357505769574871382867655 15536258654362307074301483)
      ·
        refine ⟨23304387981543460611452225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15536258654362307074301483 23304387981543460611452225)
        ·
          refine ⟨17478290986157595458589169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23304387981543460611452225 17478290986157595458589169)
          ·
            refine ⟨13108718239618196593941877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17478290986157595458589169 13108718239618196593941877)
            ·
              refine ⟨1228942334964205930682051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13108718239618196593941877 1228942334964205930682051)
              ·
                refine ⟨1843413502446308896023077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228942334964205930682051 1843413502446308896023077)
                ·
                  refine ⟨345640031708682918004327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1843413502446308896023077 345640031708682918004327)
                  ·
                    rfl

theorem cell21_1514546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_1514546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514546 prefixEnd_1514546 := by exact prefixLift 1514546
  have htrace : WordTrace (prefixWord ++ tailWord_1514546) baseStart_1514546 baseEnd_1514546 := by
    simpa [prefixWord, tailWord_1514546, baseEnd_1514546] using wordTrace_append hprefix tailTrace_1514546
  have hstable : (prefixWord ++ tailWord_1514546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514546).length < 2 ^ (prefixWord ++ tailWord_1514546).sum := by decide
  have hdescent : baseEnd_1514546 < baseStart_1514546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514566 : List Nat := [6, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1514566 : Nat := 118140960795 + 1514566 * 2 ^ 59
def prefixEnd_1514566 : Nat := 4983230072969 + 3 ^ 40 * 1514566 * 2
def baseEnd_1514566 : Nat := 345644595981167327670953

theorem tailTrace_1514566 : CollatzResearch.WordTrace tailWord_1514566 prefixEnd_1514566 345644595981167327670953 := by
  unfold tailWord_1514566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726273757218547628886111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36827173487329016082903701 1726273757218547628886111)
  ·
    refine ⟨2589410635827821443329167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1726273757218547628886111 2589410635827821443329167)
    ·
      refine ⟨3884115953741732164993751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2589410635827821443329167 3884115953741732164993751)
      ·
        refine ⟨5826173930612598247490627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884115953741732164993751 5826173930612598247490627)
        ·
          refine ⟨8739260895918897371235941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826173930612598247490627 8739260895918897371235941)
          ·
            refine ⟨1638611417984793257106739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8739260895918897371235941 1638611417984793257106739)
            ·
              refine ⟨2457917126977189885660109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638611417984793257106739 2457917126977189885660109)
              ·
                refine ⟨921718922616446207122541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2457917126977189885660109 921718922616446207122541)
                ·
                  refine ⟨345644595981167327670953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921718922616446207122541 345644595981167327670953)
                  ·
                    rfl

theorem cell21_1514566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1514566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514566 prefixEnd_1514566 := by exact prefixLift 1514566
  have htrace : WordTrace (prefixWord ++ tailWord_1514566) baseStart_1514566 baseEnd_1514566 := by
    simpa [prefixWord, tailWord_1514566, baseEnd_1514566] using wordTrace_append hprefix tailTrace_1514566
  have hstable : (prefixWord ++ tailWord_1514566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514566).length < 2 ^ (prefixWord ++ tailWord_1514566).sum := by decide
  have hdescent : baseEnd_1514566 < baseStart_1514566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514684 : List Nat := [2, 2, 2, 3, 2, 2, 2, 3, 3]
def baseStart_1514684 : Nat := 118140960795 + 1514684 * 2 ^ 59
def prefixEnd_1514684 : Nat := 4983230072969 + 3 ^ 40 * 1514684 * 2
def baseEnd_1514684 : Nat := 345671525188825344704045

theorem tailTrace_1514684 : CollatzResearch.WordTrace tailWord_1514684 prefixEnd_1514684 345671525188825344704045 := by
  unfold tailWord_1514684
  simp only [CollatzResearch.WordTrace]
  refine ⟨27622532022283015138575553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36830042696377353518100737 27622532022283015138575553)
  ·
    refine ⟨20716899016712261353931665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27622532022283015138575553 20716899016712261353931665)
    ·
      refine ⟨15537674262534196015448749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20716899016712261353931665 15537674262534196015448749)
      ·
        refine ⟨5826627848450323505793281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15537674262534196015448749 5826627848450323505793281)
        ·
          refine ⟨4369970886337742629344961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5826627848450323505793281 4369970886337742629344961)
          ·
            refine ⟨3277478164753306972008721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4369970886337742629344961 3277478164753306972008721)
            ·
              refine ⟨2458108623564980229006541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277478164753306972008721 2458108623564980229006541)
              ·
                refine ⟨921790733836867585877453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2458108623564980229006541 921790733836867585877453)
                ·
                  refine ⟨345671525188825344704045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921790733836867585877453 345671525188825344704045)
                  ·
                    rfl

theorem cell21_1514684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_1514684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514684 prefixEnd_1514684 := by exact prefixLift 1514684
  have htrace : WordTrace (prefixWord ++ tailWord_1514684) baseStart_1514684 baseEnd_1514684 := by
    simpa [prefixWord, tailWord_1514684, baseEnd_1514684] using wordTrace_append hprefix tailTrace_1514684
  have hstable : (prefixWord ++ tailWord_1514684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514684).length < 2 ^ (prefixWord ++ tailWord_1514684).sum := by decide
  have hdescent : baseEnd_1514684 < baseStart_1514684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514698 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_1514698 : Nat := 118140960795 + 1514698 * 2 ^ 59
def prefixEnd_1514698 : Nat := 4983230072969 + 3 ^ 40 * 1514698 * 2
def baseEnd_1514698 : Nat := 345674720179564431470683

theorem tailTrace_1514698 : CollatzResearch.WordTrace tailWord_1514698 prefixEnd_1514698 345674720179564431470683 := by
  unfold tailWord_1514698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811393666628827667040187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36830383111010207112107165 13811393666628827667040187)
  ·
    refine ⟨20717090499943241500560281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13811393666628827667040187 20717090499943241500560281)
    ·
      refine ⟨15537817874957431125420211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20717090499943241500560281 15537817874957431125420211)
      ·
        refine ⟨23306726812436146688130317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15537817874957431125420211 23306726812436146688130317)
        ·
          refine ⟨8740022554663555008048869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23306726812436146688130317 8740022554663555008048869)
          ·
            refine ⟨1638754228999416564009163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8740022554663555008048869 1638754228999416564009163)
            ·
              refine ⟨2458131343499124846013745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638754228999416564009163 2458131343499124846013745)
              ·
                refine ⟨1843598507624343634510309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458131343499124846013745 1843598507624343634510309)
                ·
                  refine ⟨345674720179564431470683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1843598507624343634510309 345674720179564431470683)
                  ·
                    rfl

theorem cell21_1514698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_1514698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514698 prefixEnd_1514698 := by exact prefixLift 1514698
  have htrace : WordTrace (prefixWord ++ tailWord_1514698) baseStart_1514698 baseEnd_1514698 := by
    simpa [prefixWord, tailWord_1514698, baseEnd_1514698] using wordTrace_append hprefix tailTrace_1514698
  have hstable : (prefixWord ++ tailWord_1514698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514698).length < 2 ^ (prefixWord ++ tailWord_1514698).sum := by decide
  have hdescent : baseEnd_1514698 < baseStart_1514698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514701 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1514701 : Nat := 118140960795 + 1514701 * 2 ^ 59
def prefixEnd_1514701 : Nat := 4983230072969 + 3 ^ 40 * 1514701 * 2
def baseEnd_1514701 : Nat := 345675404820437092920677

theorem tailTrace_1514701 : CollatzResearch.WordTrace tailWord_1514701 prefixEnd_1514701 345675404820437092920677 := by
  unfold tailWord_1514701
  simp only [CollatzResearch.WordTrace]
  refine ⟨55245684085504442180519957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36830456057002961453679971 55245684085504442180519957)
  ·
    refine ⟨2589641441508020727211873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55245684085504442180519957 2589641441508020727211873)
    ·
      refine ⟨1942231081131015545408905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2589641441508020727211873 1942231081131015545408905)
      ·
        refine ⟨1456673310848261659056679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1942231081131015545408905 1456673310848261659056679)
        ·
          refine ⟨2185009966272392488585019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456673310848261659056679 2185009966272392488585019)
          ·
            refine ⟨3277514949408588732877529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185009966272392488585019 3277514949408588732877529)
            ·
              refine ⟨2458136212056441549658147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277514949408588732877529 2458136212056441549658147)
              ·
                refine ⟨3687204318084662324487221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458136212056441549658147 3687204318084662324487221)
                ·
                  refine ⟨345675404820437092920677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3687204318084662324487221 345675404820437092920677)
                  ·
                    rfl

theorem cell21_1514701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1514701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514701 prefixEnd_1514701 := by exact prefixLift 1514701
  have htrace : WordTrace (prefixWord ++ tailWord_1514701) baseStart_1514701 baseEnd_1514701 := by
    simpa [prefixWord, tailWord_1514701, baseEnd_1514701] using wordTrace_append hprefix tailTrace_1514701
  have hstable : (prefixWord ++ tailWord_1514701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514701).length < 2 ^ (prefixWord ++ tailWord_1514701).sum := by decide
  have hdescent : baseEnd_1514701 < baseStart_1514701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514760 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 5]
def baseStart_1514760 : Nat := 118140960795 + 1514760 * 2 ^ 59
def prefixEnd_1514760 : Nat := 4983230072969 + 3 ^ 40 * 1514760 * 2
def baseEnd_1514760 : Nat := 345688869424266101437223

theorem tailTrace_1514760 : CollatzResearch.WordTrace tailWord_1514760 prefixEnd_1514760 345688869424266101437223 := by
  unfold tailWord_1514760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623917996145347628458867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36831890661527130171278489 27623917996145347628458867)
  ·
    refine ⟨41435876994218021442688301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27623917996145347628458867 41435876994218021442688301)
    ·
      refine ⟨15538453872831758041008113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41435876994218021442688301 15538453872831758041008113)
      ·
        refine ⟨11653840404623818530756085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15538453872831758041008113 11653840404623818530756085)
        ·
          refine ⟨1092547537933482987258383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11653840404623818530756085 1092547537933482987258383)
          ·
            refine ⟨1638821306900224480887575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092547537933482987258383 1638821306900224480887575)
            ·
              refine ⟨2458231960350336721331363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638821306900224480887575 2458231960350336721331363)
              ·
                refine ⟨3687347940525505081997045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458231960350336721331363 3687347940525505081997045)
                ·
                  refine ⟨345688869424266101437223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3687347940525505081997045 345688869424266101437223)
                  ·
                    rfl

theorem cell21_1514760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_1514760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514760 prefixEnd_1514760 := by exact prefixLift 1514760
  have htrace : WordTrace (prefixWord ++ tailWord_1514760) baseStart_1514760 baseEnd_1514760 := by
    simpa [prefixWord, tailWord_1514760, baseEnd_1514760] using wordTrace_append hprefix tailTrace_1514760
  have hstable : (prefixWord ++ tailWord_1514760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514760).length < 2 ^ (prefixWord ++ tailWord_1514760).sum := by decide
  have hdescent : baseEnd_1514760 < baseStart_1514760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514785 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 7]
def baseStart_1514785 : Nat := 118140960795 + 1514785 * 2 ^ 59
def prefixEnd_1514785 : Nat := 4983230072969 + 3 ^ 40 * 1514785 * 2
def baseEnd_1514785 : Nat := 345694574764871613520505

theorem tailTrace_1514785 : CollatzResearch.WordTrace tailWord_1514785 prefixEnd_1514785 345694574764871613520505 := by
  unfold tailWord_1514785
  simp only [CollatzResearch.WordTrace]
  refine ⟨55248747817200124526577809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36832498544800083017718539 55248747817200124526577809)
  ·
    refine ⟨41436560862900093394933357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55248747817200124526577809 41436560862900093394933357)
    ·
      refine ⟨15538710323587535023100009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41436560862900093394933357 15538710323587535023100009)
      ·
        refine ⟨11654032742690651267325007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15538710323587535023100009 11654032742690651267325007)
        ·
          refine ⟨17481049114035976900987511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11654032742690651267325007 17481049114035976900987511)
          ·
            refine ⟨26221573671053965351481267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17481049114035976900987511 26221573671053965351481267)
            ·
              refine ⟨39332360506580948027221901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26221573671053965351481267 39332360506580948027221901)
              ·
                refine ⟨14749635189967855510208213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39332360506580948027221901 14749635189967855510208213)
                ·
                  refine ⟨345694574764871613520505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14749635189967855510208213 345694574764871613520505)
                  ·
                    rfl

theorem cell21_1514785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_1514785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514785 prefixEnd_1514785 := by exact prefixLift 1514785
  have htrace : WordTrace (prefixWord ++ tailWord_1514785) baseStart_1514785 baseEnd_1514785 := by
    simpa [prefixWord, tailWord_1514785, baseEnd_1514785] using wordTrace_append hprefix tailTrace_1514785
  have hstable : (prefixWord ++ tailWord_1514785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514785).length < 2 ^ (prefixWord ++ tailWord_1514785).sum := by decide
  have hdescent : baseEnd_1514785 < baseStart_1514785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514898 : List Nat := [3, 2, 3, 3, 1, 2, 2, 5]
def baseStart_1514898 : Nat := 118140960795 + 1514898 * 2 ^ 59
def prefixEnd_1514898 : Nat := 4983230072969 + 3 ^ 40 * 1514898 * 2
def baseEnd_1514898 : Nat := 115240120968136176045647

theorem tailTrace_1514898 : CollatzResearch.WordTrace tailWord_1514898 prefixEnd_1514898 115240120968136176045647 := by
  unfold tailWord_1514898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13813217316447686206360337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36835246177193829883627565 13813217316447686206360337)
  ·
    refine ⟨10359912987335764654770253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13813217316447686206360337 10359912987335764654770253)
    ·
      refine ⟨3884967370250911745538845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10359912987335764654770253 3884967370250911745538845)
      ·
        refine ⟨1456862763844091904577067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3884967370250911745538845 1456862763844091904577067)
        ·
          refine ⟨2185294145766137856865601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456862763844091904577067 2185294145766137856865601)
          ·
            refine ⟨1638970609324603392649201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2185294145766137856865601 1638970609324603392649201)
            ·
              refine ⟨1229227956993452544486901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638970609324603392649201 1229227956993452544486901)
              ·
                refine ⟨115240120968136176045647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1229227956993452544486901 115240120968136176045647)
                ·
                  rfl

theorem cell21_1514898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_1514898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514898 prefixEnd_1514898 := by exact prefixLift 1514898
  have htrace : WordTrace (prefixWord ++ tailWord_1514898) baseStart_1514898 baseEnd_1514898 := by
    simpa [prefixWord, tailWord_1514898, baseEnd_1514898] using wordTrace_append hprefix tailTrace_1514898
  have hstable : (prefixWord ++ tailWord_1514898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514898).length < 2 ^ (prefixWord ++ tailWord_1514898).sum := by decide
  have hdescent : baseEnd_1514898 < baseStart_1514898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514940 : List Nat := [2, 2, 2, 4, 2, 1, 2, 6]
def baseStart_1514940 : Nat := 118140960795 + 1514940 * 2 ^ 59
def prefixEnd_1514940 : Nat := 4983230072969 + 3 ^ 40 * 1514940 * 2
def baseEnd_1514940 : Nat := 115243315958875262812285

theorem tailTrace_1514940 : CollatzResearch.WordTrace tailWord_1514940 prefixEnd_1514940 115243315958875262812285 := by
  unfold tailWord_1514940
  simp only [CollatzResearch.WordTrace]
  refine ⟨27627200565819292999235137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36836267421092390665646849 27627200565819292999235137)
  ·
    refine ⟨20720400424364469749426353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27627200565819292999235137 20720400424364469749426353)
    ·
      refine ⟨15540300318273352312069765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20720400424364469749426353 15540300318273352312069765)
      ·
        refine ⟨2913806309676253558513081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15540300318273352312069765 2913806309676253558513081)
        ·
          refine ⟨2185354732257190168884811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2913806309676253558513081 2185354732257190168884811)
          ·
            refine ⟨3278032098385785253327217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185354732257190168884811 3278032098385785253327217)
            ·
              refine ⟨2458524073789338939995413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3278032098385785253327217 2458524073789338939995413)
              ·
                refine ⟨115243315958875262812285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2458524073789338939995413 115243315958875262812285)
                ·
                  rfl

theorem cell21_1514940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_1514940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1514940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1514940 prefixEnd_1514940 := by exact prefixLift 1514940
  have htrace : WordTrace (prefixWord ++ tailWord_1514940) baseStart_1514940 baseEnd_1514940 := by
    simpa [prefixWord, tailWord_1514940, baseEnd_1514940] using wordTrace_append hprefix tailTrace_1514940
  have hstable : (prefixWord ++ tailWord_1514940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514940).length < 2 ^ (prefixWord ++ tailWord_1514940).sum := by decide
  have hdescent : baseEnd_1514940 < baseStart_1514940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515058 : List Nat := [3, 2, 1, 1, 2, 1, 1, 10]
def baseStart_1515058 : Nat := 118140960795 + 1515058 * 2 ^ 59
def prefixEnd_1515058 : Nat := 4983230072969 + 3 ^ 40 * 1515058 * 2
def baseEnd_1515058 : Nat := 115252292361427935156649

theorem tailTrace_1515058 : CollatzResearch.WordTrace tailWord_1515058 prefixEnd_1515058 115252292361427935156649 := by
  unfold tailWord_1515058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13814676236302773037816457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36839136630140728100843885 13814676236302773037816457)
  ·
    refine ⟨10361007177227079778362343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13814676236302773037816457 10361007177227079778362343)
    ·
      refine ⟨15541510765840619667543515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10361007177227079778362343 15541510765840619667543515)
      ·
        refine ⟨23312266148760929501315273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15541510765840619667543515 23312266148760929501315273)
        ·
          refine ⟨17484199611570697125986455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23312266148760929501315273 17484199611570697125986455)
          ·
            refine ⟨26226299417356045688979683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17484199611570697125986455 26226299417356045688979683)
            ·
              refine ⟨39339449126034068533469525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26226299417356045688979683 39339449126034068533469525)
              ·
                refine ⟨115252292361427935156649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39339449126034068533469525 115252292361427935156649)
                ·
                  rfl

theorem cell21_1515058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_1515058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515058 prefixEnd_1515058 := by exact prefixLift 1515058
  have htrace : WordTrace (prefixWord ++ tailWord_1515058) baseStart_1515058 baseEnd_1515058 := by
    simpa [prefixWord, tailWord_1515058, baseEnd_1515058] using wordTrace_append hprefix tailTrace_1515058
  have hstable : (prefixWord ++ tailWord_1515058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515058).length < 2 ^ (prefixWord ++ tailWord_1515058).sum := by decide
  have hdescent : baseEnd_1515058 < baseStart_1515058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515154 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1515154 : Nat := 118140960795 + 1515154 * 2 ^ 59
def prefixEnd_1515154 : Nat := 4983230072969 + 3 ^ 40 * 1515154 * 2
def baseEnd_1515154 : Nat := 345778785592208971869751

theorem tailTrace_1515154 : CollatzResearch.WordTrace tailWord_1515154 prefixEnd_1515154 345778785592208971869751 := by
  unfold tailWord_1515154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13815551588215825136690129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36841470901908867031173677 13815551588215825136690129)
  ·
    refine ⟨10361663691161868852517597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13815551588215825136690129 10361663691161868852517597)
    ·
      refine ⟨3885623884185700819694099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10361663691161868852517597 3885623884185700819694099)
      ·
        refine ⟨5828435826278551229541149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885623884185700819694099 5828435826278551229541149)
        ·
          refine ⟨2185663434854456711077931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5828435826278551229541149 2185663434854456711077931)
          ·
            refine ⟨3278495152281685066616897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185663434854456711077931 3278495152281685066616897)
            ·
              refine ⟨2458871364211263799962673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3278495152281685066616897 2458871364211263799962673)
              ·
                refine ⟨1844153523158447849972005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458871364211263799962673 1844153523158447849972005)
                ·
                  refine ⟨345778785592208971869751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1844153523158447849972005 345778785592208971869751)
                  ·
                    rfl

theorem cell21_1515154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1515154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515154 prefixEnd_1515154 := by exact prefixLift 1515154
  have htrace : WordTrace (prefixWord ++ tailWord_1515154) baseStart_1515154 baseEnd_1515154 := by
    simpa [prefixWord, tailWord_1515154, baseEnd_1515154] using wordTrace_append hprefix tailTrace_1515154
  have hstable : (prefixWord ++ tailWord_1515154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515154).length < 2 ^ (prefixWord ++ tailWord_1515154).sum := by decide
  have hdescent : baseEnd_1515154 < baseStart_1515154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515165 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1515165 : Nat := 118140960795 + 1515165 * 2 ^ 59
def prefixEnd_1515165 : Nat := 4983230072969 + 3 ^ 40 * 1515165 * 2
def baseEnd_1515165 : Nat := 345781295942075397186395

theorem tailTrace_1515165 : CollatzResearch.WordTrace tailWord_1515165 prefixEnd_1515165 345781295942075397186395 := by
  unfold tailWord_1515165
  simp only [CollatzResearch.WordTrace]
  refine ⟨55262607555823449425410949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36841738370548966283607299 55262607555823449425410949)
  ·
    refine ⟨10361738916716896767264553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55262607555823449425410949 10361738916716896767264553)
    ·
      refine ⟨7771304187537672575448415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10361738916716896767264553 7771304187537672575448415)
      ·
        refine ⟨11656956281306508863172623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7771304187537672575448415 11656956281306508863172623)
        ·
          refine ⟨17485434421959763294758935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11656956281306508863172623 17485434421959763294758935)
          ·
            refine ⟨26228151632939644942138403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17485434421959763294758935 26228151632939644942138403)
            ·
              refine ⟨39342227449409467413207605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26228151632939644942138403 39342227449409467413207605)
              ·
                refine ⟨3688333823382137569988213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39342227449409467413207605 3688333823382137569988213)
                ·
                  refine ⟨345781295942075397186395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3688333823382137569988213 345781295942075397186395)
                  ·
                    rfl

theorem cell21_1515165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1515165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515165 prefixEnd_1515165 := by exact prefixLift 1515165
  have htrace : WordTrace (prefixWord ++ tailWord_1515165) baseStart_1515165 baseEnd_1515165 := by
    simpa [prefixWord, tailWord_1515165, baseEnd_1515165] using wordTrace_append hprefix tailTrace_1515165
  have hstable : (prefixWord ++ tailWord_1515165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515165).length < 2 ^ (prefixWord ++ tailWord_1515165).sum := by decide
  have hdescent : baseEnd_1515165 < baseStart_1515165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515255 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 6]
def baseStart_1515255 : Nat := 118140960795 + 1515255 * 2 ^ 59
def prefixEnd_1515255 : Nat := 4983230072969 + 3 ^ 40 * 1515255 * 2
def baseEnd_1515255 : Nat := 345801835168255240686211

theorem tailTrace_1515255 : CollatzResearch.WordTrace tailWord_1515255 prefixEnd_1515255 345801835168255240686211 := by
  unfold tailWord_1515255
  simp only [CollatzResearch.WordTrace]
  refine ⟨55265890125497394796187219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36843926750331596530791479 55265890125497394796187219)
  ·
    refine ⟨82898835188246092194280829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55265890125497394796187219 82898835188246092194280829)
    ·
      refine ⟨31087063195592284572855311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82898835188246092194280829 31087063195592284572855311)
      ·
        refine ⟨46630594793388426859282967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31087063195592284572855311 46630594793388426859282967)
        ·
          refine ⟨69945892190082640288924451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46630594793388426859282967 69945892190082640288924451)
          ·
            refine ⟨104918838285123960433386677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69945892190082640288924451 104918838285123960433386677)
            ·
              refine ⟨9836141089230371290630001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104918838285123960433386677 9836141089230371290630001)
              ·
                refine ⟨7377105816922778467972501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9836141089230371290630001 7377105816922778467972501)
                ·
                  refine ⟨345801835168255240686211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7377105816922778467972501 345801835168255240686211)
                  ·
                    rfl

theorem cell21_1515255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_1515255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515255 prefixEnd_1515255 := by exact prefixLift 1515255
  have htrace : WordTrace (prefixWord ++ tailWord_1515255) baseStart_1515255 baseEnd_1515255 := by
    simpa [prefixWord, tailWord_1515255, baseEnd_1515255] using wordTrace_append hprefix tailTrace_1515255
  have hstable : (prefixWord ++ tailWord_1515255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515255).length < 2 ^ (prefixWord ++ tailWord_1515255).sum := by decide
  have hdescent : baseEnd_1515255 < baseStart_1515255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515272 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_1515272 : Nat := 118140960795 + 1515272 * 2 ^ 59
def prefixEnd_1515272 : Nat := 4983230072969 + 3 ^ 40 * 1515272 * 2
def baseEnd_1515272 : Nat := 345805714799866988902843

theorem tailTrace_1515272 : CollatzResearch.WordTrace tailWord_1515272 prefixEnd_1515272 345805714799866988902843 := by
  unfold tailWord_1515272
  simp only [CollatzResearch.WordTrace]
  refine ⟨27633255083217903349778035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36844340110957204466370713 27633255083217903349778035)
  ·
    refine ⟨41449882624826855024667053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27633255083217903349778035 41449882624826855024667053)
    ·
      refine ⟨15543705984310070634250145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41449882624826855024667053 15543705984310070634250145)
      ·
        refine ⟨11657779488232552975687609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15543705984310070634250145 11657779488232552975687609)
        ·
          refine ⟨8743334616174414731765707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11657779488232552975687609 8743334616174414731765707)
          ·
            refine ⟨13115001924261622097648561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8743334616174414731765707 13115001924261622097648561)
            ·
              refine ⟨9836251443196216573236421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13115001924261622097648561 9836251443196216573236421)
              ·
                refine ⟨1844297145599290607481829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9836251443196216573236421 1844297145599290607481829)
                ·
                  refine ⟨345805714799866988902843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1844297145599290607481829 345805714799866988902843)
                  ·
                    rfl

theorem cell21_1515272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_1515272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515272 prefixEnd_1515272 := by exact prefixLift 1515272
  have htrace : WordTrace (prefixWord ++ tailWord_1515272) baseStart_1515272 baseEnd_1515272 := by
    simpa [prefixWord, tailWord_1515272, baseEnd_1515272] using wordTrace_append hprefix tailTrace_1515272
  have hstable : (prefixWord ++ tailWord_1515272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515272).length < 2 ^ (prefixWord ++ tailWord_1515272).sum := by decide
  have hdescent : baseEnd_1515272 < baseStart_1515272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515376 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_1515376 : Nat := 118140960795 + 1515376 * 2 ^ 59
def prefixEnd_1515376 : Nat := 4983230072969 + 3 ^ 40 * 1515376 * 2
def baseEnd_1515376 : Nat := 345829449016785919169297

theorem tailTrace_1515376 : CollatzResearch.WordTrace tailWord_1515376 prefixEnd_1515376 345829449016785919169297 := by
  unfold tailWord_1515376
  simp only [CollatzResearch.WordTrace]
  refine ⟨27635151679029516230670991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36846868905372688307561321 27635151679029516230670991)
  ·
    refine ⟨41452727518544274346006487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27635151679029516230670991 41452727518544274346006487)
    ·
      refine ⟨62179091277816411519009731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41452727518544274346006487 62179091277816411519009731)
      ·
        refine ⟨93268636916724617278514597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62179091277816411519009731 93268636916724617278514597)
        ·
          refine ⟨17487869421885865739721487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93268636916724617278514597 17487869421885865739721487)
          ·
            refine ⟨26231804132828798609582231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17487869421885865739721487 26231804132828798609582231)
            ·
              refine ⟨39347706199243197914373347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26231804132828798609582231 39347706199243197914373347)
              ·
                refine ⟨59021559298864796871560021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39347706199243197914373347 59021559298864796871560021)
                ·
                  refine ⟨345829449016785919169297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59021559298864796871560021 345829449016785919169297)
                  ·
                    rfl

theorem cell21_1515376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_1515376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515376 prefixEnd_1515376 := by exact prefixLift 1515376
  have htrace : WordTrace (prefixWord ++ tailWord_1515376) baseStart_1515376 baseEnd_1515376 := by
    simpa [prefixWord, tailWord_1515376, baseEnd_1515376] using wordTrace_append hprefix tailTrace_1515376
  have hstable : (prefixWord ++ tailWord_1515376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515376).length < 2 ^ (prefixWord ++ tailWord_1515376).sum := by decide
  have hdescent : baseEnd_1515376 < baseStart_1515376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515410 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1515410 : Nat := 118140960795 + 1515410 * 2 ^ 59
def prefixEnd_1515410 : Nat := 4983230072969 + 3 ^ 40 * 1515410 * 2
def baseEnd_1515410 : Nat := 345837208280009415602561

theorem tailTrace_1515410 : CollatzResearch.WordTrace tailWord_1515410 prefixEnd_1515410 345837208280009415602561 := by
  unfold tailWord_1515410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817885859983964067019921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36847695626623904178719789 13817885859983964067019921)
  ·
    refine ⟨10363414394987973050264941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13817885859983964067019921 10363414394987973050264941)
    ·
      refine ⟨3886280398120489893849353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10363414394987973050264941 3886280398120489893849353)
      ·
        refine ⟨2914710298590367420387015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3886280398120489893849353 2914710298590367420387015)
        ·
          refine ⟨4372065447885551130580523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914710298590367420387015 4372065447885551130580523)
          ·
            refine ⟨6558098171828326695870785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372065447885551130580523 6558098171828326695870785)
            ·
              refine ⟨4918573628871245021903089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6558098171828326695870785 4918573628871245021903089)
              ·
                refine ⟨3688930221653433766427317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4918573628871245021903089 3688930221653433766427317)
                ·
                  refine ⟨345837208280009415602561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3688930221653433766427317 345837208280009415602561)
                  ·
                    rfl

theorem cell21_1515410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1515410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515410 prefixEnd_1515410 := by exact prefixLift 1515410
  have htrace : WordTrace (prefixWord ++ tailWord_1515410) baseStart_1515410 baseEnd_1515410 := by
    simpa [prefixWord, tailWord_1515410, baseEnd_1515410] using wordTrace_append hprefix tailTrace_1515410
  have hstable : (prefixWord ++ tailWord_1515410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515410).length < 2 ^ (prefixWord ++ tailWord_1515410).sum := by decide
  have hdescent : baseEnd_1515410 < baseStart_1515410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515444 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1515444 : Nat := 118140960795 + 1515444 * 2 ^ 59
def prefixEnd_1515444 : Nat := 4983230072969 + 3 ^ 40 * 1515444 * 2
def baseEnd_1515444 : Nat := 345844967543232912035825

theorem tailTrace_1515444 : CollatzResearch.WordTrace tailWord_1515444 prefixEnd_1515444 345844967543232912035825 := by
  unfold tailWord_1515444
  simp only [CollatzResearch.WordTrace]
  refine ⟨27636391760906340037408693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36848522347875120049878257 27636391760906340037408693)
  ·
    refine ⟨2590911727584969378507065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27636391760906340037408693 2590911727584969378507065)
    ·
      refine ⟨1943183795688727033880299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2590911727584969378507065 1943183795688727033880299)
      ·
        refine ⟨2914775693533090550820449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943183795688727033880299 2914775693533090550820449)
        ·
          refine ⟨2186081770149817913115337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2914775693533090550820449 2186081770149817913115337)
          ·
            refine ⟨1639561327612363434836503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186081770149817913115337 1639561327612363434836503)
            ·
              refine ⟨2459341991418545152254755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639561327612363434836503 2459341991418545152254755)
              ·
                refine ⟨3689012987127817728382133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459341991418545152254755 3689012987127817728382133)
                ·
                  refine ⟨345844967543232912035825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3689012987127817728382133 345844967543232912035825)
                  ·
                    rfl

theorem cell21_1515444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1515444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515444 prefixEnd_1515444 := by exact prefixLift 1515444
  have htrace : WordTrace (prefixWord ++ tailWord_1515444) baseStart_1515444 baseEnd_1515444 := by
    simpa [prefixWord, tailWord_1515444, baseEnd_1515444] using wordTrace_append hprefix tailTrace_1515444
  have hstable : (prefixWord ++ tailWord_1515444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515444).length < 2 ^ (prefixWord ++ tailWord_1515444).sum := by decide
  have hdescent : baseEnd_1515444 < baseStart_1515444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515562 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_1515562 : Nat := 118140960795 + 1515562 * 2 ^ 59
def prefixEnd_1515562 : Nat := 4983230072969 + 3 ^ 40 * 1515562 * 2
def baseEnd_1515562 : Nat := 345871896750890929068917

theorem tailTrace_1515562 : CollatzResearch.WordTrace tailWord_1515562 prefixEnd_1515562 345871896750890929068917 := by
  unfold tailWord_1515562
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819271833846296556903235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36851391556923457485075293 13819271833846296556903235)
  ·
    refine ⟨20728907750769444835354853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13819271833846296556903235 20728907750769444835354853)
    ·
      refine ⟨3886670203269270906629035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20728907750769444835354853 3886670203269270906629035)
      ·
        refine ⟨5830005304903906359943553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3886670203269270906629035 5830005304903906359943553)
        ·
          refine ⟨4372503978677929769957665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5830005304903906359943553 4372503978677929769957665)
          ·
            refine ⟨3279377984008447327468249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4372503978677929769957665 3279377984008447327468249)
            ·
              refine ⟨2459533488006335495601187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3279377984008447327468249 2459533488006335495601187)
              ·
                refine ⟨3689300232009503243401781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459533488006335495601187 3689300232009503243401781)
                ·
                  refine ⟨345871896750890929068917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3689300232009503243401781 345871896750890929068917)
                  ·
                    rfl

theorem cell21_1515562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_1515562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515562 prefixEnd_1515562 := by exact prefixLift 1515562
  have htrace : WordTrace (prefixWord ++ tailWord_1515562) baseStart_1515562 baseEnd_1515562 := by
    simpa [prefixWord, tailWord_1515562, baseEnd_1515562] using wordTrace_append hprefix tailTrace_1515562
  have hstable : (prefixWord ++ tailWord_1515562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515562).length < 2 ^ (prefixWord ++ tailWord_1515562).sum := by decide
  have hdescent : baseEnd_1515562 < baseStart_1515562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515621 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 5]
def baseStart_1515621 : Nat := 118140960795 + 1515621 * 2 ^ 59
def prefixEnd_1515621 : Nat := 4983230072969 + 3 ^ 40 * 1515621 * 2
def baseEnd_1515621 : Nat := 345885361354719937585463

theorem tailTrace_1515621 : CollatzResearch.WordTrace tailWord_1515621 prefixEnd_1515621 345885361354719937585463 := by
  unfold tailWord_1515621
  simp only [CollatzResearch.WordTrace]
  refine ⟨55279239242171439304010717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36852826161447626202673811 55279239242171439304010717)
  ·
    refine ⟨20729714715814289739004019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55279239242171439304010717 20729714715814289739004019)
    ·
      refine ⟨31094572073721434608506029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20729714715814289739004019 31094572073721434608506029)
      ·
        refine ⟨11660464527645537978189761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31094572073721434608506029 11660464527645537978189761)
        ·
          refine ⟨8745348395734153483642321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11660464527645537978189761 8745348395734153483642321)
          ·
            refine ⟨6559011296800615112731741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8745348395734153483642321 6559011296800615112731741)
            ·
              refine ⟨2459629236300230667274403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6559011296800615112731741 2459629236300230667274403)
              ·
                refine ⟨3689443854450346000911605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459629236300230667274403 3689443854450346000911605)
                ·
                  refine ⟨345885361354719937585463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3689443854450346000911605 345885361354719937585463)
                  ·
                    rfl

theorem cell21_1515621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_1515621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515621 prefixEnd_1515621 := by exact prefixLift 1515621
  have htrace : WordTrace (prefixWord ++ tailWord_1515621) baseStart_1515621 baseEnd_1515621 := by
    simpa [prefixWord, tailWord_1515621, baseEnd_1515621] using wordTrace_append hprefix tailTrace_1515621
  have hstable : (prefixWord ++ tailWord_1515621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515621).length < 2 ^ (prefixWord ++ tailWord_1515621).sum := by decide
  have hdescent : baseEnd_1515621 < baseStart_1515621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515672 : List Nat := [2, 1, 2, 4, 3, 2, 2, 2, 3]
def baseStart_1515672 : Nat := 118140960795 + 1515672 * 2 ^ 59
def prefixEnd_1515672 : Nat := 4983230072969 + 3 ^ 40 * 1515672 * 2
def baseEnd_1515672 : Nat := 345897000249555182235359

theorem tailTrace_1515672 : CollatzResearch.WordTrace tailWord_1515672 prefixEnd_1515672 345897000249555182235359 := by
  unfold tailWord_1515672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27640549682493337507058635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36854066243324450009411513 27640549682493337507058635)
  ·
    refine ⟨41460824523740006260587953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27640549682493337507058635 41460824523740006260587953)
    ·
      refine ⟨31095618392805004695440965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41460824523740006260587953 31095618392805004695440965)
      ·
        refine ⟨5830428448650938380395181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31095618392805004695440965 5830428448650938380395181)
        ·
          refine ⟨2186410668244101892648193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5830428448650938380395181 2186410668244101892648193)
          ·
            refine ⟨1639808001183076419486145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186410668244101892648193 1639808001183076419486145)
            ·
              refine ⟨1229856000887307314614609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639808001183076419486145 1229856000887307314614609)
              ·
                refine ⟨922392000665480485960957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229856000887307314614609 922392000665480485960957)
                ·
                  refine ⟨345897000249555182235359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922392000665480485960957 345897000249555182235359)
                  ·
                    rfl

theorem cell21_1515672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_1515672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515672 prefixEnd_1515672 := by exact prefixLift 1515672
  have htrace : WordTrace (prefixWord ++ tailWord_1515672) baseStart_1515672 baseEnd_1515672 := by
    simpa [prefixWord, tailWord_1515672, baseEnd_1515672] using wordTrace_append hprefix tailTrace_1515672
  have hstable : (prefixWord ++ tailWord_1515672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515672).length < 2 ^ (prefixWord ++ tailWord_1515672).sum := by decide
  have hdescent : baseEnd_1515672 < baseStart_1515672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515756 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_1515756 : Nat := 118140960795 + 1515756 * 2 ^ 59
def prefixEnd_1515756 : Nat := 4983230072969 + 3 ^ 40 * 1515756 * 2
def baseEnd_1515756 : Nat := 345916170193989702835187

theorem tailTrace_1515756 : CollatzResearch.WordTrace tailWord_1515756 prefixEnd_1515756 345916170193989702835187 := by
  unfold tailWord_1515756
  simp only [CollatzResearch.WordTrace]
  refine ⟨27642081548341178680087561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36856108731121571573450081 27642081548341178680087561)
  ·
    refine ⟨20731561161255884010065671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27642081548341178680087561 20731561161255884010065671)
    ·
      refine ⟨31097341741883826015098507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20731561161255884010065671 31097341741883826015098507)
      ·
        refine ⟨46646012612825739022647761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31097341741883826015098507 46646012612825739022647761)
        ·
          refine ⟨34984509459619304266985821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46646012612825739022647761 34984509459619304266985821)
          ·
            refine ⟨13119191047357239100119683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34984509459619304266985821 13119191047357239100119683)
            ·
              refine ⟨19678786571035858650179525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13119191047357239100119683 19678786571035858650179525)
              ·
                refine ⟨3689772482069223496908661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19678786571035858650179525 3689772482069223496908661)
                ·
                  refine ⟨345916170193989702835187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3689772482069223496908661 345916170193989702835187)
                  ·
                    rfl

theorem cell21_1515756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_1515756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515756 prefixEnd_1515756 := by exact prefixLift 1515756
  have htrace : WordTrace (prefixWord ++ tailWord_1515756) baseStart_1515756 baseEnd_1515756 := by
    simpa [prefixWord, tailWord_1515756, baseEnd_1515756] using wordTrace_append hprefix tailTrace_1515756
  have hstable : (prefixWord ++ tailWord_1515756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515756).length < 2 ^ (prefixWord ++ tailWord_1515756).sum := by decide
  have hdescent : baseEnd_1515756 < baseStart_1515756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515759 : List Nat := [1, 1, 2, 1, 6, 3, 2, 5]
def baseStart_1515759 : Nat := 118140960795 + 1515759 * 2 ^ 59
def prefixEnd_1515759 : Nat := 4983230072969 + 3 ^ 40 * 1515759 * 2
def baseEnd_1515759 : Nat := 115305618278287454761727

theorem tailTrace_1515759 : CollatzResearch.WordTrace tailWord_1515759 prefixEnd_1515759 115305618278287454761727 := by
  unfold tailWord_1515759
  simp only [CollatzResearch.WordTrace]
  refine ⟨55284272515671488872534331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36856181677114325915022887 55284272515671488872534331)
  ·
    refine ⟨82926408773507233308801497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55284272515671488872534331 82926408773507233308801497)
    ·
      refine ⟨62194806580130424981601123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82926408773507233308801497 62194806580130424981601123)
      ·
        refine ⟨93292209870195637472401685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62194806580130424981601123 93292209870195637472401685)
        ·
          refine ⟨4373072337665420506518829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93292209870195637472401685 4373072337665420506518829)
          ·
            refine ⟨1639902126624532689944561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4373072337665420506518829 1639902126624532689944561)
            ·
              refine ⟨1229926594968399517458421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639902126624532689944561 1229926594968399517458421)
              ·
                refine ⟨115305618278287454761727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1229926594968399517458421 115305618278287454761727)
                ·
                  rfl

theorem cell21_1515759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 5].length) (baseStart_1515759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515759 prefixEnd_1515759 := by exact prefixLift 1515759
  have htrace : WordTrace (prefixWord ++ tailWord_1515759) baseStart_1515759 baseEnd_1515759 := by
    simpa [prefixWord, tailWord_1515759, baseEnd_1515759] using wordTrace_append hprefix tailTrace_1515759
  have hstable : (prefixWord ++ tailWord_1515759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515759).length < 2 ^ (prefixWord ++ tailWord_1515759).sum := by decide
  have hdescent : baseEnd_1515759 < baseStart_1515759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515787 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 4]
def baseStart_1515787 : Nat := 118140960795 + 1515787 * 2 ^ 59
def prefixEnd_1515787 : Nat := 4983230072969 + 3 ^ 40 * 1515787 * 2
def baseEnd_1515787 : Nat := 345923244816340537818457

theorem tailTrace_1515787 : CollatzResearch.WordTrace tailWord_1515787 prefixEnd_1515787 345923244816340537818457 := by
  unfold tailWord_1515787
  simp only [CollatzResearch.WordTrace]
  refine ⟨55285293759570049654553615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36856862506380033103035743 55285293759570049654553615)
  ·
    refine ⟨82927940639355074481830423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55285293759570049654553615 82927940639355074481830423)
    ·
      refine ⟨124391910959032611722745635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82927940639355074481830423 124391910959032611722745635)
      ·
        refine ⟨186587866438548917584118453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124391910959032611722745635 186587866438548917584118453)
        ·
          refine ⟨17492612478613961023511105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186587866438548917584118453 17492612478613961023511105)
          ·
            refine ⟨13119459358960470767633329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17492612478613961023511105 13119459358960470767633329)
            ·
              refine ⟨9839594519220353075724997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13119459358960470767633329 9839594519220353075724997)
              ·
                refine ⟨1844923972353816201698437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9839594519220353075724997 1844923972353816201698437)
                ·
                  refine ⟨345923244816340537818457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1844923972353816201698437 345923244816340537818457)
                  ·
                    rfl

theorem cell21_1515787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 4].length) (baseStart_1515787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515787 prefixEnd_1515787 := by exact prefixLift 1515787
  have htrace : WordTrace (prefixWord ++ tailWord_1515787) baseStart_1515787 baseEnd_1515787 := by
    simpa [prefixWord, tailWord_1515787, baseEnd_1515787] using wordTrace_append hprefix tailTrace_1515787
  have hstable : (prefixWord ++ tailWord_1515787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515787).length < 2 ^ (prefixWord ++ tailWord_1515787).sum := by decide
  have hdescent : baseEnd_1515787 < baseStart_1515787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515841 : List Nat := [1, 2, 5, 2, 3, 1, 2, 2, 3]
def baseStart_1515841 : Nat := 118140960795 + 1515841 * 2 ^ 59
def prefixEnd_1515841 : Nat := 4983230072969 + 3 ^ 40 * 1515841 * 2
def baseEnd_1515841 : Nat := 345935568352048443918347

theorem tailTrace_1515841 : CollatzResearch.WordTrace tailWord_1515841 prefixEnd_1515841 345935568352048443918347 := by
  unfold tailWord_1515841
  simp only [CollatzResearch.WordTrace]
  refine ⟨55287263301374416877019377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36858175534249611251346251 55287263301374416877019377)
  ·
    refine ⟨41465447476030812657764533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55287263301374416877019377 41465447476030812657764533)
    ·
      refine ⟨3887385700877888686665425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41465447476030812657764533 3887385700877888686665425)
      ·
        refine ⟨2915539275658416514999069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3887385700877888686665425 2915539275658416514999069)
        ·
          refine ⟨1093327228371906193124651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2915539275658416514999069 1093327228371906193124651)
          ·
            refine ⟨1639990842557859289686977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093327228371906193124651 1639990842557859289686977)
            ·
              refine ⟨1229993131918394467265233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639990842557859289686977 1229993131918394467265233)
              ·
                refine ⟨922494848938795850448925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229993131918394467265233 922494848938795850448925)
                ·
                  refine ⟨345935568352048443918347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922494848938795850448925 345935568352048443918347)
                  ·
                    rfl

theorem cell21_1515841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_1515841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515841 prefixEnd_1515841 := by exact prefixLift 1515841
  have htrace : WordTrace (prefixWord ++ tailWord_1515841) baseStart_1515841 baseEnd_1515841 := by
    simpa [prefixWord, tailWord_1515841, baseEnd_1515841] using wordTrace_append hprefix tailTrace_1515841
  have hstable : (prefixWord ++ tailWord_1515841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515841).length < 2 ^ (prefixWord ++ tailWord_1515841).sum := by decide
  have hdescent : baseEnd_1515841 < baseStart_1515841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515863 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 4]
def baseStart_1515863 : Nat := 118140960795 + 1515863 * 2 ^ 59
def prefixEnd_1515863 : Nat := 4983230072969 + 3 ^ 40 * 1515863 * 2
def baseEnd_1515863 : Nat := 345940589051781294551635

theorem tailTrace_1515863 : CollatzResearch.WordTrace tailWord_1515863 prefixEnd_1515863 345940589051781294551635 := by
  unfold tailWord_1515863
  simp only [CollatzResearch.WordTrace]
  refine ⟨55288065707294714634320243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36858710471529809756213495 55288065707294714634320243)
  ·
    refine ⟨82932098560942071951480365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55288065707294714634320243 82932098560942071951480365)
    ·
      refine ⟨31099536960353276981805137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82932098560942071951480365 31099536960353276981805137)
      ·
        refine ⟨23324652720264957736353853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31099536960353276981805137 23324652720264957736353853)
        ·
          refine ⟨8746744770099359151132695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23324652720264957736353853 8746744770099359151132695)
          ·
            refine ⟨13120117155149038726699043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746744770099359151132695 13120117155149038726699043)
            ·
              refine ⟨19680175732723558090048565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13120117155149038726699043 19680175732723558090048565)
              ·
                refine ⟨1845016474942833570942053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19680175732723558090048565 1845016474942833570942053)
                ·
                  refine ⟨345940589051781294551635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845016474942833570942053 345940589051781294551635)
                  ·
                    rfl

theorem cell21_1515863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 4].length) (baseStart_1515863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515863 prefixEnd_1515863 := by exact prefixLift 1515863
  have htrace : WordTrace (prefixWord ++ tailWord_1515863) baseStart_1515863 baseEnd_1515863 := by
    simpa [prefixWord, tailWord_1515863, baseEnd_1515863] using wordTrace_append hprefix tailTrace_1515863
  have hstable : (prefixWord ++ tailWord_1515863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515863).length < 2 ^ (prefixWord ++ tailWord_1515863).sum := by decide
  have hdescent : baseEnd_1515863 < baseStart_1515863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515914 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_1515914 : Nat := 118140960795 + 1515914 * 2 ^ 59
def prefixEnd_1515914 : Nat := 4983230072969 + 3 ^ 40 * 1515914 * 2
def baseEnd_1515914 : Nat := 345952227946616539201531

theorem tailTrace_1515914 : CollatzResearch.WordTrace tailWord_1515914 prefixEnd_1515914 345952227946616539201531 := by
  unfold tailWord_1515914
  simp only [CollatzResearch.WordTrace]
  refine ⟨13822481457527487586106699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36859950553406633562951197 13822481457527487586106699)
  ·
    refine ⟨20733722186291231379160049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13822481457527487586106699 20733722186291231379160049)
    ·
      refine ⟨15550291639718423534370037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20733722186291231379160049 15550291639718423534370037)
      ·
        refine ⟨1457839841223602206347191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15550291639718423534370037 1457839841223602206347191)
        ·
          refine ⟨2186759761835403309520787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457839841223602206347191 2186759761835403309520787)
          ·
            refine ⟨3280139642753104964281181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186759761835403309520787 3280139642753104964281181)
            ·
              refine ⟨1230052366032414361605443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3280139642753104964281181 1230052366032414361605443)
              ·
                refine ⟨1845078549048621542408165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230052366032414361605443 1845078549048621542408165)
                ·
                  refine ⟨345952227946616539201531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845078549048621542408165 345952227946616539201531)
                  ·
                    rfl

theorem cell21_1515914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_1515914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515914 prefixEnd_1515914 := by exact prefixLift 1515914
  have htrace : WordTrace (prefixWord ++ tailWord_1515914) baseStart_1515914 baseEnd_1515914 := by
    simpa [prefixWord, tailWord_1515914, baseEnd_1515914] using wordTrace_append hprefix tailTrace_1515914
  have hstable : (prefixWord ++ tailWord_1515914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515914).length < 2 ^ (prefixWord ++ tailWord_1515914).sum := by decide
  have hdescent : baseEnd_1515914 < baseStart_1515914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515953 : List Nat := [1, 2, 2, 4, 1, 2, 9]
def baseStart_1515953 : Nat := 118140960795 + 1515953 * 2 ^ 59
def prefixEnd_1515953 : Nat := 4983230072969 + 3 ^ 40 * 1515953 * 2
def baseEnd_1515953 : Nat := 38440125364217904227939

theorem tailTrace_1515953 : CollatzResearch.WordTrace tailWord_1515953 prefixEnd_1515953 38440125364217904227939 := by
  unfold tailWord_1515953
  simp only [CollatzResearch.WordTrace]
  refine ⟨55291348276968660005096513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36860898851312440003397675 55291348276968660005096513)
  ·
    refine ⟨41468511207726495003822385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55291348276968660005096513 41468511207726495003822385)
    ·
      refine ⟨31101383405794871252866789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41468511207726495003822385 31101383405794871252866789)
      ·
        refine ⟨5831509388586538359912523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31101383405794871252866789 5831509388586538359912523)
        ·
          refine ⟨8747264082879807539868785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831509388586538359912523 8747264082879807539868785)
          ·
            refine ⟨6560448062159855654901589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8747264082879807539868785 6560448062159855654901589)
            ·
              refine ⟨38440125364217904227939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6560448062159855654901589 38440125364217904227939)
              ·
                rfl

theorem cell21_1515953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 9].length) (baseStart_1515953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1515953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1515953 prefixEnd_1515953 := by exact prefixLift 1515953
  have htrace : WordTrace (prefixWord ++ tailWord_1515953) baseStart_1515953 baseEnd_1515953 := by
    simpa [prefixWord, tailWord_1515953, baseEnd_1515953] using wordTrace_append hprefix tailTrace_1515953
  have hstable : (prefixWord ++ tailWord_1515953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515953).length < 2 ^ (prefixWord ++ tailWord_1515953).sum := by decide
  have hdescent : baseEnd_1515953 < baseStart_1515953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516001 : List Nat := [1, 2, 3, 1, 2, 2, 2, 5, 3]
def baseStart_1516001 : Nat := 118140960795 + 1516001 * 2 ^ 59
def prefixEnd_1516001 : Nat := 4983230072969 + 3 ^ 40 * 1516001 * 2
def baseEnd_1516001 : Nat := 345972082531923721251353

theorem tailTrace_1516001 : CollatzResearch.WordTrace tailWord_1516001 prefixEnd_1516001 345972082531923721251353 := by
  unfold tailWord_1516001
  simp only [CollatzResearch.WordTrace]
  refine ⟨55293098980794764202843857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36862065987196509468562571 55293098980794764202843857)
  ·
    refine ⟨41469824235596073152132893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55293098980794764202843857 41469824235596073152132893)
    ·
      refine ⟨15551184088348527432049835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41469824235596073152132893 15551184088348527432049835)
      ·
        refine ⟨23326776132522791148074753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15551184088348527432049835 23326776132522791148074753)
        ·
          refine ⟨17495082099392093361056065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23326776132522791148074753 17495082099392093361056065)
          ·
            refine ⟨13121311574544070020792049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17495082099392093361056065 13121311574544070020792049)
            ·
              refine ⟨9840983680908052515594037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13121311574544070020792049 9840983680908052515594037)
              ·
                refine ⟨922592220085129923336941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9840983680908052515594037 922592220085129923336941)
                ·
                  refine ⟨345972082531923721251353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922592220085129923336941 345972082531923721251353)
                  ·
                    rfl

theorem cell21_1516001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_1516001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516001 prefixEnd_1516001 := by exact prefixLift 1516001
  have htrace : WordTrace (prefixWord ++ tailWord_1516001) baseStart_1516001 baseEnd_1516001 := by
    simpa [prefixWord, tailWord_1516001, baseEnd_1516001] using wordTrace_append hprefix tailTrace_1516001
  have hstable : (prefixWord ++ tailWord_1516001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516001).length < 2 ^ (prefixWord ++ tailWord_1516001).sum := by decide
  have hdescent : baseEnd_1516001 < baseStart_1516001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516260 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1516260 : Nat := 118140960795 + 1516260 * 2 ^ 59
def prefixEnd_1516260 : Nat := 4983230072969 + 3 ^ 40 * 1516260 * 2
def baseEnd_1516260 : Nat := 346031189860596826434157

theorem tailTrace_1516260 : CollatzResearch.WordTrace tailWord_1516260 prefixEnd_1516260 346031189860596826434157 := by
  unfold tailWord_1516260
  simp only [CollatzResearch.WordTrace]
  refine ⟨27651272743428225718261117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36868363657904300957681489 27651272743428225718261117)
  ·
    refine ⟨10369227278785584644347919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27651272743428225718261117 10369227278785584644347919)
    ·
      refine ⟨15553840918178376966521879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10369227278785584644347919 15553840918178376966521879)
      ·
        refine ⟨23330761377267565449782819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15553840918178376966521879 23330761377267565449782819)
        ·
          refine ⟨34996142065901348174674229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23330761377267565449782819 34996142065901348174674229)
          ·
            refine ⟨3280888318678251391375709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34996142065901348174674229 3280888318678251391375709)
            ·
              refine ⟨1230333119504344271765891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3280888318678251391375709 1230333119504344271765891)
              ·
                refine ⟨1845499679256516407648837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230333119504344271765891 1845499679256516407648837)
                ·
                  refine ⟨346031189860596826434157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845499679256516407648837 346031189860596826434157)
                  ·
                    rfl

theorem cell21_1516260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1516260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516260 prefixEnd_1516260 := by exact prefixLift 1516260
  have htrace : WordTrace (prefixWord ++ tailWord_1516260) baseStart_1516260 baseEnd_1516260 := by
    simpa [prefixWord, tailWord_1516260, baseEnd_1516260] using wordTrace_append hprefix tailTrace_1516260
  have hstable : (prefixWord ++ tailWord_1516260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516260).length < 2 ^ (prefixWord ++ tailWord_1516260).sum := by decide
  have hdescent : baseEnd_1516260 < baseStart_1516260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516274 : List Nat := [3, 2, 1, 3, 1, 2, 4, 5]
def baseStart_1516274 : Nat := 118140960795 + 1516274 * 2 ^ 59
def prefixEnd_1516274 : Nat := 4983230072969 + 3 ^ 40 * 1516274 * 2
def baseEnd_1516274 : Nat := 115344794950445304400265

theorem tailTrace_1516274 : CollatzResearch.WordTrace tailWord_1516274 prefixEnd_1516274 115344794950445304400265 := by
  unfold tailWord_1516274
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825764027201432956882969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36868704072537154551687917 13825764027201432956882969)
  ·
    refine ⟨10369323020401074717662227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13825764027201432956882969 10369323020401074717662227)
    ·
      refine ⟨15553984530601612076493341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10369323020401074717662227 15553984530601612076493341)
      ·
        refine ⟨5832744198975604528685003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15553984530601612076493341 5832744198975604528685003)
        ·
          refine ⟨8749116298463406793027505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832744198975604528685003 8749116298463406793027505)
          ·
            refine ⟨6561837223847555094770629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8749116298463406793027505 6561837223847555094770629)
            ·
              refine ⟨1230344479471416580269493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6561837223847555094770629 1230344479471416580269493)
              ·
                refine ⟨115344794950445304400265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1230344479471416580269493 115344794950445304400265)
                ·
                  rfl

theorem cell21_1516274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_1516274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516274 prefixEnd_1516274 := by exact prefixLift 1516274
  have htrace : WordTrace (prefixWord ++ tailWord_1516274) baseStart_1516274 baseEnd_1516274 := by
    simpa [prefixWord, tailWord_1516274, baseEnd_1516274] using wordTrace_append hprefix tailTrace_1516274
  have hstable : (prefixWord ++ tailWord_1516274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516274).length < 2 ^ (prefixWord ++ tailWord_1516274).sum := by decide
  have hdescent : baseEnd_1516274 < baseStart_1516274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516319 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 4]
def baseStart_1516319 : Nat := 118140960795 + 1516319 * 2 ^ 59
def prefixEnd_1516319 : Nat := 4983230072969 + 3 ^ 40 * 1516319 * 2
def baseEnd_1516319 : Nat := 346044654464425834950703

theorem tailTrace_1516319 : CollatzResearch.WordTrace tailWord_1516319 prefixEnd_1516319 346044654464425834950703 := by
  unfold tailWord_1516319
  simp only [CollatzResearch.WordTrace]
  refine ⟨55304697393642704512920011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36869798262428469675280007 55304697393642704512920011)
  ·
    refine ⟨82957046090464056769380017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55304697393642704512920011 82957046090464056769380017)
    ·
      refine ⟨62217784567848042577035013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82957046090464056769380017 62217784567848042577035013)
      ·
        refine ⟨11665834606471507983194065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62217784567848042577035013 11665834606471507983194065)
        ·
          refine ⟨8749375954853630987395549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11665834606471507983194065 8749375954853630987395549)
          ·
            refine ⟨3281015983070111620273331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8749375954853630987395549 3281015983070111620273331)
            ·
              refine ⟨4921523974605167430409997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281015983070111620273331 4921523974605167430409997)
              ·
                refine ⟨1845571490476937786403749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4921523974605167430409997 1845571490476937786403749)
                ·
                  refine ⟨346044654464425834950703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845571490476937786403749 346044654464425834950703)
                  ·
                    rfl

theorem cell21_1516319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 4].length) (baseStart_1516319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516319 prefixEnd_1516319 := by exact prefixLift 1516319
  have htrace : WordTrace (prefixWord ++ tailWord_1516319) baseStart_1516319 baseEnd_1516319 := by
    simpa [prefixWord, tailWord_1516319, baseEnd_1516319] using wordTrace_append hprefix tailTrace_1516319
  have hstable : (prefixWord ++ tailWord_1516319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516319).length < 2 ^ (prefixWord ++ tailWord_1516319).sum := by decide
  have hdescent : baseEnd_1516319 < baseStart_1516319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516350 : List Nat := [4, 2, 1, 2, 4, 8]
def baseStart_1516350 : Nat := 118140960795 + 1516350 * 2 ^ 59
def prefixEnd_1516350 : Nat := 4983230072969 + 3 ^ 40 * 1516350 * 2
def baseEnd_1516350 : Nat := 12816730706917654441999

theorem tailTrace_1516350 : CollatzResearch.WordTrace tailWord_1516350 prefixEnd_1516350 12816730706917654441999 := by
  unfold tailWord_1516350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913228507066299600912313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36870552037686931204865669 6913228507066299600912313)
  ·
    refine ⟨5184921380299724700684235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6913228507066299600912313 5184921380299724700684235)
    ·
      refine ⟨7777382070449587051026353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5184921380299724700684235 7777382070449587051026353)
      ·
        refine ⟨5833036552837190288269765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7777382070449587051026353 5833036552837190288269765)
        ·
          refine ⟨1093694353656973179050581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5833036552837190288269765 1093694353656973179050581)
          ·
            refine ⟨12816730706917654441999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1093694353656973179050581 12816730706917654441999)
            ·
              rfl

theorem cell21_1516350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 8].length) (baseStart_1516350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516350 prefixEnd_1516350 := by exact prefixLift 1516350
  have htrace : WordTrace (prefixWord ++ tailWord_1516350) baseStart_1516350 baseEnd_1516350 := by
    simpa [prefixWord, tailWord_1516350, baseEnd_1516350] using wordTrace_append hprefix tailTrace_1516350
  have hstable : (prefixWord ++ tailWord_1516350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516350).length < 2 ^ (prefixWord ++ tailWord_1516350).sum := by decide
  have hdescent : baseEnd_1516350 < baseStart_1516350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516353 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 4]
def baseStart_1516353 : Nat := 118140960795 + 1516353 * 2 ^ 59
def prefixEnd_1516353 : Nat := 4983230072969 + 3 ^ 40 * 1516353 * 2
def baseEnd_1516353 : Nat := 346052413727649331383967

theorem tailTrace_1516353 : CollatzResearch.WordTrace tailWord_1516353 prefixEnd_1516353 346052413727649331383967 := by
  unfold tailWord_1516353
  simp only [CollatzResearch.WordTrace]
  refine ⟨55305937475519528319657713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36870624983679685546438475 55305937475519528319657713)
  ·
    refine ⟨41479453106639646239743285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55305937475519528319657713 41479453106639646239743285)
    ·
      refine ⟨3888698728747466834975933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41479453106639646239743285 3888698728747466834975933)
      ·
        refine ⟨1458262023280300063115975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3888698728747466834975933 1458262023280300063115975)
        ·
          refine ⟨2187393034920450094673963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458262023280300063115975 2187393034920450094673963)
          ·
            refine ⟨3281089552380675142010945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187393034920450094673963 3281089552380675142010945)
            ·
              refine ⟨2460817164285506356508209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3281089552380675142010945 2460817164285506356508209)
              ·
                refine ⟨1845612873214129767381157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460817164285506356508209 1845612873214129767381157)
                ·
                  refine ⟨346052413727649331383967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1845612873214129767381157 346052413727649331383967)
                  ·
                    rfl

theorem cell21_1516353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_1516353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516353 prefixEnd_1516353 := by exact prefixLift 1516353
  have htrace : WordTrace (prefixWord ++ tailWord_1516353) baseStart_1516353 baseEnd_1516353 := by
    simpa [prefixWord, tailWord_1516353, baseEnd_1516353] using wordTrace_append hprefix tailTrace_1516353
  have hstable : (prefixWord ++ tailWord_1516353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516353).length < 2 ^ (prefixWord ++ tailWord_1516353).sum := by decide
  have hdescent : baseEnd_1516353 < baseStart_1516353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516502 : List Nat := [5, 2, 1, 1, 2, 1, 2, 7]
def baseStart_1516502 : Nat := 118140960795 + 1516502 * 2 ^ 59
def prefixEnd_1516502 : Nat := 4983230072969 + 3 ^ 40 * 1516502 * 2
def baseEnd_1516502 : Nat := 115362139185886061133443

theorem tailTrace_1516502 : CollatzResearch.WordTrace tailWord_1516502 prefixEnd_1516502 115362139185886061133443 := by
  unfold tailWord_1516502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456960746998732922926985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36874247967986484511221173 3456960746998732922926985)
  ·
    refine ⟨2592720560249049692195239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3456960746998732922926985 2592720560249049692195239)
    ·
      refine ⟨3889080840373574538292859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592720560249049692195239 3889080840373574538292859)
      ·
        refine ⟨5833621260560361807439289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889080840373574538292859 5833621260560361807439289)
        ·
          refine ⟨4375215945420271355579467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5833621260560361807439289 4375215945420271355579467)
          ·
            refine ⟨6562823918130407033369201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375215945420271355579467 6562823918130407033369201)
            ·
              refine ⟨4922117938597805275026901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6562823918130407033369201 4922117938597805275026901)
              ·
                refine ⟨115362139185886061133443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4922117938597805275026901 115362139185886061133443)
                ·
                  rfl

theorem cell21_1516502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_1516502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516502 prefixEnd_1516502 := by exact prefixLift 1516502
  have htrace : WordTrace (prefixWord ++ tailWord_1516502) baseStart_1516502 baseEnd_1516502 := by
    simpa [prefixWord, tailWord_1516502, baseEnd_1516502] using wordTrace_append hprefix tailTrace_1516502
  have hstable : (prefixWord ++ tailWord_1516502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516502).length < 2 ^ (prefixWord ++ tailWord_1516502).sum := by decide
  have hdescent : baseEnd_1516502 < baseStart_1516502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516592 : List Nat := [2, 1, 1, 1, 2, 4, 1, 6, 3]
def baseStart_1516592 : Nat := 118140960795 + 1516592 * 2 ^ 59
def prefixEnd_1516592 : Nat := 4983230072969 + 3 ^ 40 * 1516592 * 2
def baseEnd_1516592 : Nat := 346106956783838026900145

theorem tailTrace_1516592 : CollatzResearch.WordTrace tailWord_1516592 prefixEnd_1516592 346106956783838026900145 := by
  unfold tailWord_1516592
  simp only [CollatzResearch.WordTrace]
  refine ⟨27657327260826836068804015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36876436347769114758405353 27657327260826836068804015)
  ·
    refine ⟨41485990891240254103206023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27657327260826836068804015 41485990891240254103206023)
    ·
      refine ⟨62228986336860381154809035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41485990891240254103206023 62228986336860381154809035)
      ·
        refine ⟨93343479505290571732213553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62228986336860381154809035 93343479505290571732213553)
        ·
          refine ⟨70007609628967928799160165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93343479505290571732213553 70007609628967928799160165)
          ·
            refine ⟨13126426805431486649842531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70007609628967928799160165 13126426805431486649842531)
            ·
              refine ⟨19689640208147229974763797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13126426805431486649842531 19689640208147229974763797)
              ·
                refine ⟨922951884756901405067053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19689640208147229974763797 922951884756901405067053)
                ·
                  refine ⟨346106956783838026900145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922951884756901405067053 346106956783838026900145)
                  ·
                    rfl

theorem cell21_1516592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_1516592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516592 prefixEnd_1516592 := by exact prefixLift 1516592
  have htrace : WordTrace (prefixWord ++ tailWord_1516592) baseStart_1516592 baseEnd_1516592 := by
    simpa [prefixWord, tailWord_1516592, baseEnd_1516592] using wordTrace_append hprefix tailTrace_1516592
  have hstable : (prefixWord ++ tailWord_1516592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516592).length < 2 ^ (prefixWord ++ tailWord_1516592).sum := by decide
  have hdescent : baseEnd_1516592 < baseStart_1516592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516626 : List Nat := [3, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_1516626 : Nat := 118140960795 + 1516626 * 2 ^ 59
def prefixEnd_1516626 : Nat := 4983230072969 + 3 ^ 40 * 1516626 * 2
def baseEnd_1516626 : Nat := 346114716047061523333409

theorem tailTrace_1516626 : CollatzResearch.WordTrace tailWord_1516626 prefixEnd_1516626 346114716047061523333409 := by
  unfold tailWord_1516626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13828973650882623986086433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36877263069020330629563821 13828973650882623986086433)
  ·
    refine ⟨10371730238161967989564825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13828973650882623986086433 10371730238161967989564825)
    ·
      refine ⟨7778797678621475992173619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10371730238161967989564825 7778797678621475992173619)
      ·
        refine ⟨11668196517932213988260429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7778797678621475992173619 11668196517932213988260429)
        ·
          refine ⟨4375573694224580245597661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11668196517932213988260429 4375573694224580245597661)
          ·
            refine ⟨1640840135334217592099123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4375573694224580245597661 1640840135334217592099123)
            ·
              refine ⟨2461260203001326388148685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640840135334217592099123 2461260203001326388148685)
              ·
                refine ⟨922972576125497395555757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2461260203001326388148685 922972576125497395555757)
                ·
                  refine ⟨346114716047061523333409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922972576125497395555757 346114716047061523333409)
                  ·
                    rfl

theorem cell21_1516626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_1516626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516626 prefixEnd_1516626 := by exact prefixLift 1516626
  have htrace : WordTrace (prefixWord ++ tailWord_1516626) baseStart_1516626 baseEnd_1516626 := by
    simpa [prefixWord, tailWord_1516626, baseEnd_1516626] using wordTrace_append hprefix tailTrace_1516626
  have hstable : (prefixWord ++ tailWord_1516626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516626).length < 2 ^ (prefixWord ++ tailWord_1516626).sum := by decide
  have hdescent : baseEnd_1516626 < baseStart_1516626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516696 : List Nat := [2, 1, 2, 4, 2, 10]
def baseStart_1516696 : Nat := 118140960795 + 1516696 * 2 ^ 59
def prefixEnd_1516696 : Nat := 4983230072969 + 3 ^ 40 * 1516696 * 2
def baseEnd_1516696 : Nat := 12819655222250257672837

theorem tailTrace_1516696 : CollatzResearch.WordTrace tailWord_1516696 prefixEnd_1516696 12819655222250257672837 := by
  unfold tailWord_1516696
  simp only [CollatzResearch.WordTrace]
  refine ⟨27659223856638448949696971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36878965142184598599595961 27659223856638448949696971)
  ·
    refine ⟨41488835784957673424545457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27659223856638448949696971 41488835784957673424545457)
    ·
      refine ⟨31116626838718255068409093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41488835784957673424545457 31116626838718255068409093)
      ·
        refine ⟨5834367532259672825326705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31116626838718255068409093 5834367532259672825326705)
        ·
          refine ⟨4375775649194754618995029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5834367532259672825326705 4375775649194754618995029)
          ·
            refine ⟨12819655222250257672837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4375775649194754618995029 12819655222250257672837)
            ·
              rfl

theorem cell21_1516696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 10].length) (baseStart_1516696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516696 prefixEnd_1516696 := by exact prefixLift 1516696
  have htrace : WordTrace (prefixWord ++ tailWord_1516696) baseStart_1516696 baseEnd_1516696 := by
    simpa [prefixWord, tailWord_1516696, baseEnd_1516696] using wordTrace_append hprefix tailTrace_1516696
  have hstable : (prefixWord ++ tailWord_1516696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516696).length < 2 ^ (prefixWord ++ tailWord_1516696).sum := by decide
  have hdescent : baseEnd_1516696 < baseStart_1516696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516702 : List Nat := [4, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1516702 : Nat := 118140960795 + 1516702 * 2 ^ 59
def prefixEnd_1516702 : Nat := 4983230072969 + 3 ^ 40 * 1516702 * 2
def baseEnd_1516702 : Nat := 346132060282502280066587

theorem tailTrace_1516702 : CollatzResearch.WordTrace tailWord_1516702 prefixEnd_1516702 346132060282502280066587 := by
  unfold tailWord_1516702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6914833318906895115514045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36879111034170107282741573 6914833318906895115514045)
  ·
    refine ⟨2593062494590085668317767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6914833318906895115514045 2593062494590085668317767)
    ·
      refine ⟨3889593741885128502476651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2593062494590085668317767 3889593741885128502476651)
      ·
        refine ⟨5834390612827692753714977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889593741885128502476651 5834390612827692753714977)
        ·
          refine ⟨4375792959620769565286233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5834390612827692753714977 4375792959620769565286233)
          ·
            refine ⟨3281844719715577173964675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4375792959620769565286233 3281844719715577173964675)
            ·
              refine ⟨4922767079573365760947013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281844719715577173964675 4922767079573365760947013)
              ·
                refine ⟨923018827420006080177565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4922767079573365760947013 923018827420006080177565)
                ·
                  refine ⟨346132060282502280066587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923018827420006080177565 346132060282502280066587)
                  ·
                    rfl

theorem cell21_1516702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1516702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516702 prefixEnd_1516702 := by exact prefixLift 1516702
  have htrace : WordTrace (prefixWord ++ tailWord_1516702) baseStart_1516702 baseEnd_1516702 := by
    simpa [prefixWord, tailWord_1516702, baseEnd_1516702] using wordTrace_append hprefix tailTrace_1516702
  have hstable : (prefixWord ++ tailWord_1516702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516702).length < 2 ^ (prefixWord ++ tailWord_1516702).sum := by decide
  have hdescent : baseEnd_1516702 < baseStart_1516702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516727 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 5]
def baseStart_1516727 : Nat := 118140960795 + 1516727 * 2 ^ 59
def prefixEnd_1516727 : Nat := 4983230072969 + 3 ^ 40 * 1516727 * 2
def baseEnd_1516727 : Nat := 346137765623107792149869

theorem tailTrace_1516727 : CollatzResearch.WordTrace tailWord_1516727 prefixEnd_1516727 346137765623107792149869 := by
  unfold tailWord_1516727
  simp only [CollatzResearch.WordTrace]
  refine ⟨55319578376164590193772435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36879718917443060129181623 55319578376164590193772435)
  ·
    refine ⟨82979367564246885290658653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55319578376164590193772435 82979367564246885290658653)
    ·
      refine ⟨31117262836592581983996995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82979367564246885290658653 31117262836592581983996995)
      ·
        refine ⟨46675894254888872975995493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31117262836592581983996995 46675894254888872975995493)
        ·
          refine ⟨8751730172791663682999155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46675894254888872975995493 8751730172791663682999155)
          ·
            refine ⟨13127595259187495524498733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751730172791663682999155 13127595259187495524498733)
            ·
              refine ⟨4922848222195310821687025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13127595259187495524498733 4922848222195310821687025)
              ·
                refine ⟨3692136166646483116265269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4922848222195310821687025 3692136166646483116265269)
                ·
                  refine ⟨346137765623107792149869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3692136166646483116265269 346137765623107792149869)
                  ·
                    rfl

theorem cell21_1516727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_1516727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516727 prefixEnd_1516727 := by exact prefixLift 1516727
  have htrace : WordTrace (prefixWord ++ tailWord_1516727) baseStart_1516727 baseEnd_1516727 := by
    simpa [prefixWord, tailWord_1516727, baseEnd_1516727] using wordTrace_append hprefix tailTrace_1516727
  have hstable : (prefixWord ++ tailWord_1516727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516727).length < 2 ^ (prefixWord ++ tailWord_1516727).sum := by decide
  have hdescent : baseEnd_1516727 < baseStart_1516727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516741 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 6]
def baseStart_1516741 : Nat := 118140960795 + 1516741 * 2 ^ 59
def prefixEnd_1516741 : Nat := 4983230072969 + 3 ^ 40 * 1516741 * 2
def baseEnd_1516741 : Nat := 346140960613846878916507

theorem tailTrace_1516741 : CollatzResearch.WordTrace tailWord_1516741 prefixEnd_1516741 346140960613846878916507 := by
  unfold tailWord_1516741
  simp only [CollatzResearch.WordTrace]
  refine ⟨55320088998113870584782077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36880059332075913723188051 55320088998113870584782077)
  ·
    refine ⟨20745033374292701469293279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55320088998113870584782077 20745033374292701469293279)
    ·
      refine ⟨31117550061439052203939919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20745033374292701469293279 31117550061439052203939919)
      ·
        refine ⟨46676325092158578305909879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31117550061439052203939919 46676325092158578305909879)
        ·
          refine ⟨70014487638237867458864819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46676325092158578305909879 70014487638237867458864819)
          ·
            refine ⟨105021731457356801188297229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70014487638237867458864819 105021731457356801188297229)
            ·
              refine ⟨39383149296508800445611461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105021731457356801188297229 39383149296508800445611461)
              ·
                refine ⟨7384340493095400083552149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39383149296508800445611461 7384340493095400083552149)
                ·
                  refine ⟨346140960613846878916507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7384340493095400083552149 346140960613846878916507)
                  ·
                    rfl

theorem cell21_1516741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_1516741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516741 prefixEnd_1516741 := by exact prefixLift 1516741
  have htrace : WordTrace (prefixWord ++ tailWord_1516741) baseStart_1516741 baseEnd_1516741 := by
    simpa [prefixWord, tailWord_1516741, baseEnd_1516741] using wordTrace_append hprefix tailTrace_1516741
  have hstable : (prefixWord ++ tailWord_1516741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516741).length < 2 ^ (prefixWord ++ tailWord_1516741).sum := by decide
  have hdescent : baseEnd_1516741 < baseStart_1516741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516744 : List Nat := [2, 1, 3, 1, 2, 1, 3, 5, 3]
def baseStart_1516744 : Nat := 118140960795 + 1516744 * 2 ^ 59
def prefixEnd_1516744 : Nat := 4983230072969 + 3 ^ 40 * 1516744 * 2
def baseEnd_1516744 : Nat := 346141645254719540366501

theorem tailTrace_1516744 : CollatzResearch.WordTrace tailWord_1516744 prefixEnd_1516744 346141645254719540366501 := by
  unfold tailWord_1516744
  simp only [CollatzResearch.WordTrace]
  refine ⟨27660099208551501048570643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36880132278068668064760857 27660099208551501048570643)
  ·
    refine ⟨41490148812827251572855965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27660099208551501048570643 41490148812827251572855965)
    ·
      refine ⟨15558805804810219339820987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41490148812827251572855965 15558805804810219339820987)
      ·
        refine ⟨23338208707215329009731481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15558805804810219339820987 23338208707215329009731481)
        ·
          refine ⟨17503656530411496757298611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23338208707215329009731481 17503656530411496757298611)
          ·
            refine ⟨26255484795617245135947917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17503656530411496757298611 26255484795617245135947917)
            ·
              refine ⟨9845806798356466925980469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26255484795617245135947917 9845806798356466925980469)
              ·
                refine ⟨923044387345918774310669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9845806798356466925980469 923044387345918774310669)
                ·
                  refine ⟨346141645254719540366501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923044387345918774310669 346141645254719540366501)
                  ·
                    rfl

theorem cell21_1516744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_1516744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516744 prefixEnd_1516744 := by exact prefixLift 1516744
  have htrace : WordTrace (prefixWord ++ tailWord_1516744) baseStart_1516744 baseEnd_1516744 := by
    simpa [prefixWord, tailWord_1516744, baseEnd_1516744] using wordTrace_append hprefix tailTrace_1516744
  have hstable : (prefixWord ++ tailWord_1516744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516744).length < 2 ^ (prefixWord ++ tailWord_1516744).sum := by decide
  have hdescent : baseEnd_1516744 < baseStart_1516744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516817 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 6]
def baseStart_1516817 : Nat := 118140960795 + 1516817 * 2 ^ 59
def prefixEnd_1516817 : Nat := 4983230072969 + 3 ^ 40 * 1516817 * 2
def baseEnd_1516817 : Nat := 346158304849287635649685

theorem tailTrace_1516817 : CollatzResearch.WordTrace tailWord_1516817 prefixEnd_1516817 346158304849287635649685 := by
  unfold tailWord_1516817
  simp only [CollatzResearch.WordTrace]
  refine ⟨55322860945838535564548705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36881907297225690376365803 55322860945838535564548705)
  ·
    refine ⟨41492145709378901673411529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55322860945838535564548705 41492145709378901673411529)
    ·
      refine ⟨31119109282034176255058647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41492145709378901673411529 31119109282034176255058647)
      ·
        refine ⟨46678663923051264382587971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31119109282034176255058647 46678663923051264382587971)
        ·
          refine ⟨70017995884576896573881957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46678663923051264382587971 70017995884576896573881957)
          ·
            refine ⟨13128374228358168107602867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70017995884576896573881957 13128374228358168107602867)
            ·
              refine ⟨19692561342537252161404301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13128374228358168107602867 19692561342537252161404301)
              ·
                refine ⟨7384710503451469560526613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19692561342537252161404301 7384710503451469560526613)
                ·
                  refine ⟨346158304849287635649685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7384710503451469560526613 346158304849287635649685)
                  ·
                    rfl

theorem cell21_1516817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_1516817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516817 prefixEnd_1516817 := by exact prefixLift 1516817
  have htrace : WordTrace (prefixWord ++ tailWord_1516817) baseStart_1516817 baseEnd_1516817 := by
    simpa [prefixWord, tailWord_1516817, baseEnd_1516817] using wordTrace_append hprefix tailTrace_1516817
  have hstable : (prefixWord ++ tailWord_1516817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516817).length < 2 ^ (prefixWord ++ tailWord_1516817).sum := by decide
  have hdescent : baseEnd_1516817 < baseStart_1516817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516868 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1516868 : Nat := 118140960795 + 1516868 * 2 ^ 59
def prefixEnd_1516868 : Nat := 4983230072969 + 3 ^ 40 * 1516868 * 2
def baseEnd_1516868 : Nat := 346169943744122880299581

theorem tailTrace_1516868 : CollatzResearch.WordTrace tailWord_1516868 prefixEnd_1516868 346169943744122880299581 := by
  unfold tailWord_1516868
  simp only [CollatzResearch.WordTrace]
  refine ⟨27662360534326885637327629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36883147379102514183103505 27662360534326885637327629)
  ·
    refine ⟨10373385200372582113997861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27662360534326885637327629 10373385200372582113997861)
    ·
      refine ⟨1945009725069859146374599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10373385200372582113997861 1945009725069859146374599)
      ·
        refine ⟨2917514587604788719561899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945009725069859146374599 2917514587604788719561899)
        ·
          refine ⟨4376271881407183079342849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917514587604788719561899 4376271881407183079342849)
          ·
            refine ⟨3282203911055387309507137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376271881407183079342849 3282203911055387309507137)
            ·
              refine ⟨2461652933291540482130353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3282203911055387309507137 2461652933291540482130353)
              ·
                refine ⟨1846239699968655361597765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2461652933291540482130353 1846239699968655361597765)
                ·
                  refine ⟨346169943744122880299581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1846239699968655361597765 346169943744122880299581)
                  ·
                    rfl

theorem cell21_1516868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1516868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516868 prefixEnd_1516868 := by exact prefixLift 1516868
  have htrace : WordTrace (prefixWord ++ tailWord_1516868) baseStart_1516868 baseEnd_1516868 := by
    simpa [prefixWord, tailWord_1516868, baseEnd_1516868] using wordTrace_append hprefix tailTrace_1516868
  have hstable : (prefixWord ++ tailWord_1516868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516868).length < 2 ^ (prefixWord ++ tailWord_1516868).sum := by decide
  have hdescent : baseEnd_1516868 < baseStart_1516868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516930 : List Nat := [3, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1516930 : Nat := 118140960795 + 1516930 * 2 ^ 59
def prefixEnd_1516930 : Nat := 4983230072969 + 3 ^ 40 * 1516930 * 2
def baseEnd_1516930 : Nat := 346184092988824550266121

theorem tailTrace_1516930 : CollatzResearch.WordTrace tailWord_1516930 prefixEnd_1516930 346184092988824550266121 := by
  unfold tailWord_1516930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13831745598607288965853061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36884654929619437242274829 13831745598607288965853061)
  ·
    refine ⟨2593452299738866681097449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13831745598607288965853061 2593452299738866681097449)
    ·
      refine ⟨1945089224804150010823087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2593452299738866681097449 1945089224804150010823087)
      ·
        refine ⟨2917633837206225016234631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945089224804150010823087 2917633837206225016234631)
        ·
          refine ⟨4376450755809337524351947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917633837206225016234631 4376450755809337524351947)
          ·
            refine ⟨6564676133714006286527921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376450755809337524351947 6564676133714006286527921)
            ·
              refine ⟨4923507100285504714895941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6564676133714006286527921 4923507100285504714895941)
              ·
                refine ⟨923157581303532134042989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4923507100285504714895941 923157581303532134042989)
                ·
                  refine ⟨346184092988824550266121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923157581303532134042989 346184092988824550266121)
                  ·
                    rfl

theorem cell21_1516930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1516930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516930 prefixEnd_1516930 := by exact prefixLift 1516930
  have htrace : WordTrace (prefixWord ++ tailWord_1516930) baseStart_1516930 baseEnd_1516930 := by
    simpa [prefixWord, tailWord_1516930, baseEnd_1516930] using wordTrace_append hprefix tailTrace_1516930
  have hstable : (prefixWord ++ tailWord_1516930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516930).length < 2 ^ (prefixWord ++ tailWord_1516930).sum := by decide
  have hdescent : baseEnd_1516930 < baseStart_1516930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516958 : List Nat := [4, 3, 1, 2, 2, 1, 1, 7]
def baseStart_1516958 : Nat := 118140960795 + 1516958 * 2 ^ 59
def prefixEnd_1516958 : Nat := 4983230072969 + 3 ^ 40 * 1516958 * 2
def baseEnd_1516958 : Nat := 115396827656767574599799

theorem tailTrace_1516958 : CollatzResearch.WordTrace tailWord_1516958 prefixEnd_1516958 115396827656767574599799 := by
  unfold tailWord_1516958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916000454790964580678941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36885335758885144430287685 6916000454790964580678941)
  ·
    refine ⟨2593500170546611717754603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6916000454790964580678941 2593500170546611717754603)
    ·
      refine ⟨3890250255819917576631905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2593500170546611717754603 3890250255819917576631905)
      ·
        refine ⟨2917687691864938182473929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3890250255819917576631905 2917687691864938182473929)
        ·
          refine ⟨2188265768898703636855447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2917687691864938182473929 2188265768898703636855447)
          ·
            refine ⟨3282398653348055455283171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188265768898703636855447 3282398653348055455283171)
            ·
              refine ⟨4923597980022083182924757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282398653348055455283171 4923597980022083182924757)
              ·
                refine ⟨115396827656767574599799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4923597980022083182924757 115396827656767574599799)
                ·
                  rfl

theorem cell21_1516958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_1516958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516958 prefixEnd_1516958 := by exact prefixLift 1516958
  have htrace : WordTrace (prefixWord ++ tailWord_1516958) baseStart_1516958 baseEnd_1516958 := by
    simpa [prefixWord, tailWord_1516958, baseEnd_1516958] using wordTrace_append hprefix tailTrace_1516958
  have hstable : (prefixWord ++ tailWord_1516958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516958).length < 2 ^ (prefixWord ++ tailWord_1516958).sum := by decide
  have hdescent : baseEnd_1516958 < baseStart_1516958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516972 : List Nat := [2, 2, 1, 1, 1, 1, 7, 3, 3]
def baseStart_1516972 : Nat := 118140960795 + 1516972 * 2 ^ 59
def prefixEnd_1516972 : Nat := 4983230072969 + 3 ^ 40 * 1516972 * 2
def baseEnd_1516972 : Nat := 346193677961041810566035

theorem tailTrace_1516972 : CollatzResearch.WordTrace tailWord_1516972 prefixEnd_1516972 346193677961041810566035 := by
  unfold tailWord_1516972
  simp only [CollatzResearch.WordTrace]
  refine ⟨27664257130138498518220585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36885676173517998024294113 27664257130138498518220585)
  ·
    refine ⟨20748192847603873888665439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27664257130138498518220585 20748192847603873888665439)
    ·
      refine ⟨31122289271405810832998159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20748192847603873888665439 31122289271405810832998159)
      ·
        refine ⟨46683433907108716249497239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31122289271405810832998159 46683433907108716249497239)
        ·
          refine ⟨70025150860663074374245859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46683433907108716249497239 70025150860663074374245859)
          ·
            refine ⟨105037726290994611561368789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70025150860663074374245859 105037726290994611561368789)
            ·
              refine ⟨2461821709945186208469581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 105037726290994611561368789 2461821709945186208469581)
              ·
                refine ⟨923183141229444828176093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2461821709945186208469581 923183141229444828176093)
                ·
                  refine ⟨346193677961041810566035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923183141229444828176093 346193677961041810566035)
                  ·
                    rfl

theorem cell21_1516972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_1516972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516972 prefixEnd_1516972 := by exact prefixLift 1516972
  have htrace : WordTrace (prefixWord ++ tailWord_1516972) baseStart_1516972 baseEnd_1516972 := by
    simpa [prefixWord, tailWord_1516972, baseEnd_1516972] using wordTrace_append hprefix tailTrace_1516972
  have hstable : (prefixWord ++ tailWord_1516972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516972).length < 2 ^ (prefixWord ++ tailWord_1516972).sum := by decide
  have hdescent : baseEnd_1516972 < baseStart_1516972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516989 : List Nat := [1, 4, 1, 2, 2, 1, 5, 2, 3]
def baseStart_1516989 : Nat := 118140960795 + 1516989 * 2 ^ 59
def prefixEnd_1516989 : Nat := 4983230072969 + 3 ^ 40 * 1516989 * 2
def baseEnd_1516989 : Nat := 346197557592653558782667

theorem tailTrace_1516989 : CollatzResearch.WordTrace tailWord_1516989 prefixEnd_1516989 346197557592653558782667 := by
  unfold tailWord_1516989
  simp only [CollatzResearch.WordTrace]
  refine ⟨55329134301215408939810021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36886089534143605959873347 55329134301215408939810021)
  ·
    refine ⟨10374212681477889176214379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55329134301215408939810021 10374212681477889176214379)
    ·
      refine ⟨15561319022216833764321569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10374212681477889176214379 15561319022216833764321569)
      ·
        refine ⟨11670989266662625323241177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15561319022216833764321569 11670989266662625323241177)
        ·
          refine ⟨8753241949996968992430883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11670989266662625323241177 8753241949996968992430883)
          ·
            refine ⟨13129862924995453488646325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8753241949996968992430883 13129862924995453488646325)
            ·
              refine ⟨1230924649218323764560593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13129862924995453488646325 1230924649218323764560593)
              ·
                refine ⟨923193486913742823420445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1230924649218323764560593 923193486913742823420445)
                ·
                  refine ⟨346197557592653558782667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923193486913742823420445 346197557592653558782667)
                  ·
                    rfl

theorem cell21_1516989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_1516989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1516989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1516989 prefixEnd_1516989 := by exact prefixLift 1516989
  have htrace : WordTrace (prefixWord ++ tailWord_1516989) baseStart_1516989 baseEnd_1516989 := by
    simpa [prefixWord, tailWord_1516989, baseEnd_1516989] using wordTrace_append hprefix tailTrace_1516989
  have hstable : (prefixWord ++ tailWord_1516989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516989).length < 2 ^ (prefixWord ++ tailWord_1516989).sum := by decide
  have hdescent : baseEnd_1516989 < baseStart_1516989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517000 : List Nat := [2, 1, 3, 1, 3, 1, 4, 6]
def baseStart_1517000 : Nat := 118140960795 + 1517000 * 2 ^ 59
def prefixEnd_1517000 : Nat := 4983230072969 + 3 ^ 40 * 1517000 * 2
def baseEnd_1517000 : Nat := 115400022647506661366437

theorem tailTrace_1517000 : CollatzResearch.WordTrace tailWord_1517000 prefixEnd_1517000 115400022647506661366437 := by
  unfold tailWord_1517000
  simp only [CollatzResearch.WordTrace]
  refine ⟨27664767752087778909230227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36886357002783705212306969 27664767752087778909230227)
  ·
    refine ⟨41497151628131668363845341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27664767752087778909230227 41497151628131668363845341)
    ·
      refine ⟨15561431860549375636442003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41497151628131668363845341 15561431860549375636442003)
      ·
        refine ⟨23342147790824063454663005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15561431860549375636442003 23342147790824063454663005)
        ·
          refine ⟨8753305421559023795498627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23342147790824063454663005 8753305421559023795498627)
          ·
            refine ⟨13129958132338535693247941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8753305421559023795498627 13129958132338535693247941)
            ·
              refine ⟨2461867149813475442483989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13129958132338535693247941 2461867149813475442483989)
              ·
                refine ⟨115400022647506661366437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2461867149813475442483989 115400022647506661366437)
                ·
                  rfl

theorem cell21_1517000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_1517000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517000 prefixEnd_1517000 := by exact prefixLift 1517000
  have htrace : WordTrace (prefixWord ++ tailWord_1517000) baseStart_1517000 baseEnd_1517000 := by
    simpa [prefixWord, tailWord_1517000, baseEnd_1517000] using wordTrace_append hprefix tailTrace_1517000
  have hstable : (prefixWord ++ tailWord_1517000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517000).length < 2 ^ (prefixWord ++ tailWord_1517000).sum := by decide
  have hdescent : baseEnd_1517000 < baseStart_1517000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517048 : List Nat := [2, 1, 2, 1, 1, 6, 1, 4, 3]
def baseStart_1517048 : Nat := 118140960795 + 1517048 * 2 ^ 59
def prefixEnd_1517048 : Nat := 4983230072969 + 3 ^ 40 * 1517048 * 2
def baseEnd_1517048 : Nat := 346211022196482567299213

theorem tailTrace_1517048 : CollatzResearch.WordTrace tailWord_1517048 prefixEnd_1517048 346211022196482567299213 := by
  unfold tailWord_1517048
  simp only [CollatzResearch.WordTrace]
  refine ⟨27665643104000831008103899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36887524138667774677471865 27665643104000831008103899)
  ·
    refine ⟨41498464656001246512155849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27665643104000831008103899 41498464656001246512155849)
    ·
      refine ⟨31123848492000934884116887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41498464656001246512155849 31123848492000934884116887)
      ·
        refine ⟨46685772738001402326175331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31123848492000934884116887 46685772738001402326175331)
        ·
          refine ⟨70028659107002103489262997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46685772738001402326175331 70028659107002103489262997)
          ·
            refine ⟨3282593395640723601059203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70028659107002103489262997 3282593395640723601059203)
            ·
              refine ⟨4923890093461085401588805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282593395640723601059203 4923890093461085401588805)
              ·
                refine ⟨923229392523953512797901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4923890093461085401588805 923229392523953512797901)
                ·
                  refine ⟨346211022196482567299213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923229392523953512797901 346211022196482567299213)
                  ·
                    rfl

theorem cell21_1517048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_1517048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517048 prefixEnd_1517048 := by exact prefixLift 1517048
  have htrace : WordTrace (prefixWord ++ tailWord_1517048) baseStart_1517048 baseEnd_1517048 := by
    simpa [prefixWord, tailWord_1517048, baseEnd_1517048] using wordTrace_append hprefix tailTrace_1517048
  have hstable : (prefixWord ++ tailWord_1517048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517048).length < 2 ^ (prefixWord ++ tailWord_1517048).sum := by decide
  have hdescent : baseEnd_1517048 < baseStart_1517048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517059 : List Nat := [1, 1, 1, 3, 2, 1, 2, 10]
def baseStart_1517059 : Nat := 118140960795 + 1517059 * 2 ^ 59
def prefixEnd_1517059 : Nat := 4983230072969 + 3 ^ 40 * 1517059 * 2
def baseEnd_1517059 : Nat := 115404510848782997538619

theorem tailTrace_1517059 : CollatzResearch.WordTrace tailWord_1517059 prefixEnd_1517059 115404510848782997538619 := by
  unfold tailWord_1517059
  simp only [CollatzResearch.WordTrace]
  refine ⟨55331687410961810894858231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36887791607307873929905487 55331687410961810894858231)
  ·
    refine ⟨82997531116442716342287347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55331687410961810894858231 82997531116442716342287347)
    ·
      refine ⟨124496296674664074513431021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82997531116442716342287347 124496296674664074513431021)
      ·
        refine ⟨46686111252999027942536633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124496296674664074513431021 46686111252999027942536633)
        ·
          refine ⟨35014583439749270956902475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46686111252999027942536633 35014583439749270956902475)
          ·
            refine ⟨52521875159623906435353713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35014583439749270956902475 52521875159623906435353713)
            ·
              refine ⟨39391406369717929826515285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52521875159623906435353713 39391406369717929826515285)
              ·
                refine ⟨115404510848782997538619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39391406369717929826515285 115404510848782997538619)
                ·
                  rfl

theorem cell21_1517059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 10].length) (baseStart_1517059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517059 prefixEnd_1517059 := by exact prefixLift 1517059
  have htrace : WordTrace (prefixWord ++ tailWord_1517059) baseStart_1517059 baseEnd_1517059 := by
    simpa [prefixWord, tailWord_1517059, baseEnd_1517059] using wordTrace_append hprefix tailTrace_1517059
  have hstable : (prefixWord ++ tailWord_1517059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517059).length < 2 ^ (prefixWord ++ tailWord_1517059).sum := by decide
  have hdescent : baseEnd_1517059 < baseStart_1517059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517096 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_1517096 : Nat := 118140960795 + 1517096 * 2 ^ 59
def prefixEnd_1517096 : Nat := 4983230072969 + 3 ^ 40 * 1517096 * 2
def baseEnd_1517096 : Nat := 346221976450445150499115

theorem tailTrace_1517096 : CollatzResearch.WordTrace tailWord_1517096 prefixEnd_1517096 346221976450445150499115 := by
  unfold tailWord_1517096
  simp only [CollatzResearch.WordTrace]
  refine ⟨27666518455913883106977571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36888691274551844142636761 27666518455913883106977571)
  ·
    refine ⟨41499777683870824660466357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27666518455913883106977571 41499777683870824660466357)
    ·
      refine ⟨3890604157862889811918721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41499777683870824660466357 3890604157862889811918721)
      ·
        refine ⟨2917953118397167358939041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3890604157862889811918721 2917953118397167358939041)
        ·
          refine ⟨2188464838797875519204281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2917953118397167358939041 2188464838797875519204281)
          ·
            refine ⟨1641348629098406639403211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2188464838797875519204281 1641348629098406639403211)
            ·
              refine ⟨2462022943647609959104817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641348629098406639403211 2462022943647609959104817)
              ·
                refine ⟨1846517207735707469328613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462022943647609959104817 1846517207735707469328613)
                ·
                  refine ⟨346221976450445150499115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1846517207735707469328613 346221976450445150499115)
                  ·
                    rfl

theorem cell21_1517096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_1517096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517096 prefixEnd_1517096 := by exact prefixLift 1517096
  have htrace : WordTrace (prefixWord ++ tailWord_1517096) baseStart_1517096 baseEnd_1517096 := by
    simpa [prefixWord, tailWord_1517096, baseEnd_1517096] using wordTrace_append hprefix tailTrace_1517096
  have hstable : (prefixWord ++ tailWord_1517096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517096).length < 2 ^ (prefixWord ++ tailWord_1517096).sum := by decide
  have hdescent : baseEnd_1517096 < baseStart_1517096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517107 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 5]
def baseStart_1517107 : Nat := 118140960795 + 1517107 * 2 ^ 59
def prefixEnd_1517107 : Nat := 4983230072969 + 3 ^ 40 * 1517107 * 2
def baseEnd_1517107 : Nat := 346224486800311575815759

theorem tailTrace_1517107 : CollatzResearch.WordTrace tailWord_1517107 prefixEnd_1517107 346224486800311575815759 := by
  unfold tailWord_1517107
  simp only [CollatzResearch.WordTrace]
  refine ⟨55333438114787915092605575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36888958743191943395070383 55333438114787915092605575)
  ·
    refine ⟨83000157172181872638908363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55333438114787915092605575 83000157172181872638908363)
    ·
      refine ⟨124500235758272808958362545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83000157172181872638908363 124500235758272808958362545)
      ·
        refine ⟨93375176818704606718771909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124500235758272808958362545 93375176818704606718771909)
        ·
          refine ⟨17507845653507113759769733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93375176818704606718771909 17507845653507113759769733)
          ·
            refine ⟨3282721060032583829956825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17507845653507113759769733 3282721060032583829956825)
            ·
              refine ⟨2462040795024437872467619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3282721060032583829956825 2462040795024437872467619)
              ·
                refine ⟨3693061192536656808701429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462040795024437872467619 3693061192536656808701429)
                ·
                  refine ⟨346224486800311575815759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3693061192536656808701429 346224486800311575815759)
                  ·
                    rfl

theorem cell21_1517107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_1517107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517107 prefixEnd_1517107 := by exact prefixLift 1517107
  have htrace : WordTrace (prefixWord ++ tailWord_1517107) baseStart_1517107 baseEnd_1517107 := by
    simpa [prefixWord, tailWord_1517107, baseEnd_1517107] using wordTrace_append hprefix tailTrace_1517107
  have hstable : (prefixWord ++ tailWord_1517107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517107).length < 2 ^ (prefixWord ++ tailWord_1517107).sum := by decide
  have hdescent : baseEnd_1517107 < baseStart_1517107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517217 : List Nat := [1, 2, 3, 3, 2, 1, 4, 2, 3]
def baseStart_1517217 : Nat := 118140960795 + 1517217 * 2 ^ 59
def prefixEnd_1517217 : Nat := 4983230072969 + 3 ^ 40 * 1517217 * 2
def baseEnd_1517217 : Nat := 346249590298975828982201

theorem tailTrace_1517217 : CollatzResearch.WordTrace tailWord_1517217 prefixEnd_1517217 346249590298975828982201 := by
  unfold tailWord_1517217
  simp only [CollatzResearch.WordTrace]
  refine ⟨55337450144389403879109905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36891633429592935919406603 55337450144389403879109905)
  ·
    refine ⟨41503087608292052909332429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55337450144389403879109905 41503087608292052909332429)
    ·
      refine ⟨15563657853109519840999661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41503087608292052909332429 15563657853109519840999661)
      ·
        refine ⟨5836371694916069940374873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15563657853109519840999661 5836371694916069940374873)
        ·
          refine ⟨4377278771187052455281155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5836371694916069940374873 4377278771187052455281155)
          ·
            refine ⟨6565918156780578682921733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377278771187052455281155 6565918156780578682921733)
            ·
              refine ⟨1231109654396358503047825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6565918156780578682921733 1231109654396358503047825)
              ·
                refine ⟨923332240797268877285869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231109654396358503047825 923332240797268877285869)
                ·
                  refine ⟨346249590298975828982201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923332240797268877285869 346249590298975828982201)
                  ·
                    rfl

theorem cell21_1517217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_1517217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517217 prefixEnd_1517217 := by exact prefixLift 1517217
  have htrace : WordTrace (prefixWord ++ tailWord_1517217) baseStart_1517217 baseEnd_1517217 := by
    simpa [prefixWord, tailWord_1517217, baseEnd_1517217] using wordTrace_append hprefix tailTrace_1517217
  have hstable : (prefixWord ++ tailWord_1517217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517217).length < 2 ^ (prefixWord ++ tailWord_1517217).sum := by decide
  have hdescent : baseEnd_1517217 < baseStart_1517217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517242 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1517242 : Nat := 118140960795 + 1517242 * 2 ^ 59
def prefixEnd_1517242 : Nat := 4983230072969 + 3 ^ 40 * 1517242 * 2
def baseEnd_1517242 : Nat := 346255295639581341065483

theorem tailTrace_1517242 : CollatzResearch.WordTrace tailWord_1517242 prefixEnd_1517242 346255295639581341065483 := by
  unfold tailWord_1517242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13834590492324708287192495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36892241312865888765846653 13834590492324708287192495)
  ·
    refine ⟨20751885738487062430788743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13834590492324708287192495 20751885738487062430788743)
    ·
      refine ⟨31127828607730593646183115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20751885738487062430788743 31127828607730593646183115)
      ·
        refine ⟨46691742911595890469274673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31127828607730593646183115 46691742911595890469274673)
        ·
          refine ⟨35018807183696917851956005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46691742911595890469274673 35018807183696917851956005)
          ·
            refine ⟨6566026346943172097241751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35018807183696917851956005 6566026346943172097241751)
            ·
              refine ⟨9849039520414758145862627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6566026346943172097241751 9849039520414758145862627)
              ·
                refine ⟨14773559280622137218793941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9849039520414758145862627 14773559280622137218793941)
                ·
                  refine ⟨346255295639581341065483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14773559280622137218793941 346255295639581341065483)
                  ·
                    rfl

theorem cell21_1517242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1517242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517242 prefixEnd_1517242 := by exact prefixLift 1517242
  have htrace : WordTrace (prefixWord ++ tailWord_1517242) baseStart_1517242 baseEnd_1517242 := by
    simpa [prefixWord, tailWord_1517242, baseEnd_1517242] using wordTrace_append hprefix tailTrace_1517242
  have hstable : (prefixWord ++ tailWord_1517242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517242).length < 2 ^ (prefixWord ++ tailWord_1517242).sum := by decide
  have hdescent : baseEnd_1517242 < baseStart_1517242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517273 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 6]
def baseStart_1517273 : Nat := 118140960795 + 1517273 * 2 ^ 59
def prefixEnd_1517273 : Nat := 4983230072969 + 3 ^ 40 * 1517273 * 2
def baseEnd_1517273 : Nat := 346262370261932176048753

theorem tailTrace_1517273 : CollatzResearch.WordTrace tailWord_1517273 prefixEnd_1517273 346262370261932176048753 := by
  unfold tailWord_1517273
  simp only [CollatzResearch.WordTrace]
  refine ⟨55339492632186525443148473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36892995088124350295432315 55339492632186525443148473)
  ·
    refine ⟨41504619474139894082361355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55339492632186525443148473 41504619474139894082361355)
    ·
      refine ⟨62256929211209841123542033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41504619474139894082361355 62256929211209841123542033)
      ·
        refine ⟨46692696908407380842656525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62256929211209841123542033 46692696908407380842656525)
        ·
          refine ⟨17509761340652767815996197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46692696908407380842656525 17509761340652767815996197)
          ·
            refine ⟨3283080251372393965499287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17509761340652767815996197 3283080251372393965499287)
            ·
              refine ⟨4924620377058590948248931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283080251372393965499287 4924620377058590948248931)
              ·
                refine ⟨7386930565587886422373397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924620377058590948248931 7386930565587886422373397)
                ·
                  refine ⟨346262370261932176048753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7386930565587886422373397 346262370261932176048753)
                  ·
                    rfl

theorem cell21_1517273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_1517273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517273 prefixEnd_1517273 := by exact prefixLift 1517273
  have htrace : WordTrace (prefixWord ++ tailWord_1517273) baseStart_1517273 baseEnd_1517273 := by
    simpa [prefixWord, tailWord_1517273, baseEnd_1517273] using wordTrace_append hprefix tailTrace_1517273
  have hstable : (prefixWord ++ tailWord_1517273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517273).length < 2 ^ (prefixWord ++ tailWord_1517273).sum := by decide
  have hdescent : baseEnd_1517273 < baseStart_1517273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517310 : List Nat := [4, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1517310 : Nat := 118140960795 + 1517310 * 2 ^ 59
def prefixEnd_1517310 : Nat := 4983230072969 + 3 ^ 40 * 1517310 * 2
def baseEnd_1517310 : Nat := 346270814166028333932011

theorem tailTrace_1517310 : CollatzResearch.WordTrace tailWord_1517310 prefixEnd_1517310 346270814166028333932011 := by
  unfold tailWord_1517310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6917605266631560095280673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36893894755368320508163589 6917605266631560095280673)
  ·
    refine ⟨5188203949973670071460505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6917605266631560095280673 5188203949973670071460505)
    ·
      refine ⟨3891152962480252553595379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5188203949973670071460505 3891152962480252553595379)
      ·
        refine ⟨5836729443720378830393069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891152962480252553595379 5836729443720378830393069)
        ·
          refine ⟨2188773541395142061397401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5836729443720378830393069 2188773541395142061397401)
          ·
            refine ⟨1641580156046356546048051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2188773541395142061397401 1641580156046356546048051)
            ·
              refine ⟨2462370234069534819072077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641580156046356546048051 2462370234069534819072077)
              ·
                refine ⟨923388837776075557152029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2462370234069534819072077 923388837776075557152029)
                ·
                  refine ⟨346270814166028333932011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923388837776075557152029 346270814166028333932011)
                  ·
                    rfl

theorem cell21_1517310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1517310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517310 prefixEnd_1517310 := by exact prefixLift 1517310
  have htrace : WordTrace (prefixWord ++ tailWord_1517310) baseStart_1517310 baseEnd_1517310 := by
    simpa [prefixWord, tailWord_1517310, baseEnd_1517310] using wordTrace_append hprefix tailTrace_1517310
  have hstable : (prefixWord ++ tailWord_1517310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517310).length < 2 ^ (prefixWord ++ tailWord_1517310).sum := by decide
  have hdescent : baseEnd_1517310 < baseStart_1517310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517335 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 5]
def baseStart_1517335 : Nat := 118140960795 + 1517335 * 2 ^ 59
def prefixEnd_1517335 : Nat := 4983230072969 + 3 ^ 40 * 1517335 * 2
def baseEnd_1517335 : Nat := 346276519506633846015293

theorem tailTrace_1517335 : CollatzResearch.WordTrace tailWord_1517335 prefixEnd_1517335 346276519506633846015293 := by
  unfold tailWord_1517335
  simp only [CollatzResearch.WordTrace]
  refine ⟨55341753957961910031905459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36894502638641273354603639 55341753957961910031905459)
  ·
    refine ⟨83012630936942865047858189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55341753957961910031905459 83012630936942865047858189)
    ·
      refine ⟨31129736601353574392946821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83012630936942865047858189 31129736601353574392946821)
      ·
        refine ⟨5836825612753795198677529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31129736601353574392946821 5836825612753795198677529)
        ·
          refine ⟨4377619209565346399008147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5836825612753795198677529 4377619209565346399008147)
          ·
            refine ⟨6566428814348019598512221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377619209565346399008147 6566428814348019598512221)
            ·
              refine ⟨2462410805380507349442083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6566428814348019598512221 2462410805380507349442083)
              ·
                refine ⟨3693616208070761024163125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2462410805380507349442083 3693616208070761024163125)
                ·
                  refine ⟨346276519506633846015293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3693616208070761024163125 346276519506633846015293)
                  ·
                    rfl

theorem cell21_1517335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_1517335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517335 prefixEnd_1517335 := by exact prefixLift 1517335
  have htrace : WordTrace (prefixWord ++ tailWord_1517335) baseStart_1517335 baseEnd_1517335 := by
    simpa [prefixWord, tailWord_1517335, baseEnd_1517335] using wordTrace_append hprefix tailTrace_1517335
  have hstable : (prefixWord ++ tailWord_1517335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517335).length < 2 ^ (prefixWord ++ tailWord_1517335).sum := by decide
  have hdescent : baseEnd_1517335 < baseStart_1517335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517411 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 5]
def baseStart_1517411 : Nat := 118140960795 + 1517411 * 2 ^ 59
def prefixEnd_1517411 : Nat := 4983230072969 + 3 ^ 40 * 1517411 * 2
def baseEnd_1517411 : Nat := 346293863742074602748471

theorem tailTrace_1517411 : CollatzResearch.WordTrace tailWord_1517411 prefixEnd_1517411 346293863742074602748471 := by
  unfold tailWord_1517411
  simp only [CollatzResearch.WordTrace]
  refine ⟨55344525905686575011672087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36896350603791050007781391 55344525905686575011672087)
  ·
    refine ⟨83016788858529862517508131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55344525905686575011672087 83016788858529862517508131)
    ·
      refine ⟨124525183287794793776262197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83016788858529862517508131 124525183287794793776262197)
      ·
        refine ⟨11674235933230761916524581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124525183287794793776262197 11674235933230761916524581)
        ·
          refine ⟨2188919237480767859348359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11674235933230761916524581 2188919237480767859348359)
          ·
            refine ⟨3283378856221151789022539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188919237480767859348359 3283378856221151789022539)
            ·
              refine ⟨4925068284331727683533809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283378856221151789022539 4925068284331727683533809)
              ·
                refine ⟨3693801213248795762650357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925068284331727683533809 3693801213248795762650357)
                ·
                  refine ⟨346293863742074602748471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3693801213248795762650357 346293863742074602748471)
                  ·
                    rfl

theorem cell21_1517411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_1517411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517411 prefixEnd_1517411 := by exact prefixLift 1517411
  have htrace : WordTrace (prefixWord ++ tailWord_1517411) baseStart_1517411 baseEnd_1517411 := by
    simpa [prefixWord, tailWord_1517411, baseEnd_1517411] using wordTrace_append hprefix tailTrace_1517411
  have hstable : (prefixWord ++ tailWord_1517411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517411).length < 2 ^ (prefixWord ++ tailWord_1517411).sum := by decide
  have hdescent : baseEnd_1517411 < baseStart_1517411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517501 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1517501 : Nat := 118140960795 + 1517501 * 2 ^ 59
def prefixEnd_1517501 : Nat := 4983230072969 + 3 ^ 40 * 1517501 * 2
def baseEnd_1517501 : Nat := 346314402968254446248287

theorem tailTrace_1517501 : CollatzResearch.WordTrace tailWord_1517501 prefixEnd_1517501 346314402968254446248287 := by
  unfold tailWord_1517501
  simp only [CollatzResearch.WordTrace]
  refine ⟨55347808475360520382448357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36898538983573680254965571 55347808475360520382448357)
  ·
    refine ⟨10377714089130097571709067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55347808475360520382448357 10377714089130097571709067)
    ·
      refine ⟨15566571133695146357563601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10377714089130097571709067 15566571133695146357563601)
      ·
        refine ⟨11674928350271359768172701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15566571133695146357563601 11674928350271359768172701)
        ·
          refine ⟨4378098131351759913064763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11674928350271359768172701 4378098131351759913064763)
          ·
            refine ⟨6567147197027639869597145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378098131351759913064763 6567147197027639869597145)
            ·
              refine ⟨4925360397770729902197859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6567147197027639869597145 4925360397770729902197859)
              ·
                refine ⟨7388040596656094853296789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4925360397770729902197859 7388040596656094853296789)
                ·
                  refine ⟨346314402968254446248287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7388040596656094853296789 346314402968254446248287)
                  ·
                    rfl

theorem cell21_1517501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1517501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517501 prefixEnd_1517501 := by exact prefixLift 1517501
  have htrace : WordTrace (prefixWord ++ tailWord_1517501) baseStart_1517501 baseEnd_1517501 := by
    simpa [prefixWord, tailWord_1517501, baseEnd_1517501] using wordTrace_append hprefix tailTrace_1517501
  have hstable : (prefixWord ++ tailWord_1517501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517501).length < 2 ^ (prefixWord ++ tailWord_1517501).sum := by decide
  have hdescent : baseEnd_1517501 < baseStart_1517501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517504 : List Nat := [2, 1, 1, 2, 3, 2, 5, 2, 3]
def baseStart_1517504 : Nat := 118140960795 + 1517504 * 2 ^ 59
def prefixEnd_1517504 : Nat := 4983230072969 + 3 ^ 40 * 1517504 * 2
def baseEnd_1517504 : Nat := 346315087609127107698281

theorem tailTrace_1517504 : CollatzResearch.WordTrace tailWord_1517504 prefixEnd_1517504 346315087609127107698281 := by
  unfold tailWord_1517504
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673958947174825947403783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36898611929566434596538377 27673958947174825947403783)
  ·
    refine ⟨41510938420762238921105675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27673958947174825947403783 41510938420762238921105675)
    ·
      refine ⟨62266407631143358381658513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41510938420762238921105675 62266407631143358381658513)
      ·
        refine ⟨46699805723357518786243885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62266407631143358381658513 46699805723357518786243885)
        ·
          refine ⟨17512427146259069544841457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46699805723357518786243885 17512427146259069544841457)
          ·
            refine ⟨13134320359694302158631093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17512427146259069544841457 13134320359694302158631093)
            ·
              refine ⟨1231342533721340827371665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13134320359694302158631093 1231342533721340827371665)
              ·
                refine ⟨923506900291005620528749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231342533721340827371665 923506900291005620528749)
                ·
                  refine ⟨346315087609127107698281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923506900291005620528749 346315087609127107698281)
                  ·
                    rfl

theorem cell21_1517504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_1517504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517504 prefixEnd_1517504 := by exact prefixLift 1517504
  have htrace : WordTrace (prefixWord ++ tailWord_1517504) baseStart_1517504 baseEnd_1517504 := by
    simpa [prefixWord, tailWord_1517504, baseEnd_1517504] using wordTrace_append hprefix tailTrace_1517504
  have hstable : (prefixWord ++ tailWord_1517504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517504).length < 2 ^ (prefixWord ++ tailWord_1517504).sum := by decide
  have hdescent : baseEnd_1517504 < baseStart_1517504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517515 : List Nat := [1, 1, 1, 1, 3, 4, 4, 6]
def baseStart_1517515 : Nat := 118140960795 + 1517515 * 2 ^ 59
def prefixEnd_1517515 : Nat := 4983230072969 + 3 ^ 40 * 1517515 * 2
def baseEnd_1517515 : Nat := 115439199319664511004975

theorem tailTrace_1517515 : CollatzResearch.WordTrace tailWord_1517515 prefixEnd_1517515 115439199319664511004975 := by
  unfold tailWord_1517515
  simp only [CollatzResearch.WordTrace]
  refine ⟨55348319097309800773457999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36898879398206533848971999 55348319097309800773457999)
  ·
    refine ⟨83022478645964701160186999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55348319097309800773457999 83022478645964701160186999)
    ·
      refine ⟨124533717968947051740280499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83022478645964701160186999 124533717968947051740280499)
      ·
        refine ⟨186800576953420577610420749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124533717968947051740280499 186800576953420577610420749)
        ·
          refine ⟨70050216357532716603907781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186800576953420577610420749 70050216357532716603907781)
          ·
            refine ⟨13134415567037384363232709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70050216357532716603907781 13134415567037384363232709)
            ·
              refine ⟨2462702918819509568106133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13134415567037384363232709 2462702918819509568106133)
              ·
                refine ⟨115439199319664511004975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2462702918819509568106133 115439199319664511004975)
                ·
                  rfl

theorem cell21_1517515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 6].length) (baseStart_1517515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517515 prefixEnd_1517515 := by exact prefixLift 1517515
  have htrace : WordTrace (prefixWord ++ tailWord_1517515) baseStart_1517515 baseEnd_1517515 := by
    simpa [prefixWord, tailWord_1517515, baseEnd_1517515] using wordTrace_append hprefix tailTrace_1517515
  have hstable : (prefixWord ++ tailWord_1517515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517515).length < 2 ^ (prefixWord ++ tailWord_1517515).sum := by decide
  have hdescent : baseEnd_1517515 < baseStart_1517515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517549 : List Nat := [1, 5, 1, 4, 2, 8]
def baseStart_1517549 : Nat := 118140960795 + 1517549 * 2 ^ 59
def prefixEnd_1517549 : Nat := 4983230072969 + 3 ^ 40 * 1517549 * 2
def baseEnd_1517549 : Nat := 12826865082304334424007

theorem tailTrace_1517549 : CollatzResearch.WordTrace tailWord_1517549 prefixEnd_1517549 12826865082304334424007 := by
  unfold tailWord_1517549
  simp only [CollatzResearch.WordTrace]
  refine ⟨55349559179186624580195701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36899706119457749720130467 55349559179186624580195701)
  ·
    refine ⟨5189021173048746054393347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55349559179186624580195701 5189021173048746054393347)
    ·
      refine ⟨7783531759573119081590021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5189021173048746054393347 7783531759573119081590021)
      ·
        refine ⟨1459412204919959827798129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7783531759573119081590021 1459412204919959827798129)
        ·
          refine ⟨1094559153689969870848597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1459412204919959827798129 1094559153689969870848597)
          ·
            refine ⟨12826865082304334424007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1094559153689969870848597 12826865082304334424007)
            ·
              rfl

theorem cell21_1517549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 8].length) (baseStart_1517549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517549 prefixEnd_1517549 := by exact prefixLift 1517549
  have htrace : WordTrace (prefixWord ++ tailWord_1517549) baseStart_1517549 baseEnd_1517549 := by
    simpa [prefixWord, tailWord_1517549, baseEnd_1517549] using wordTrace_append hprefix tailTrace_1517549
  have hstable : (prefixWord ++ tailWord_1517549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517549).length < 2 ^ (prefixWord ++ tailWord_1517549).sum := by decide
  have hdescent : baseEnd_1517549 < baseStart_1517549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517560 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_1517560 : Nat := 118140960795 + 1517560 * 2 ^ 59
def prefixEnd_1517560 : Nat := 4983230072969 + 3 ^ 40 * 1517560 * 2
def baseEnd_1517560 : Nat := 346327867572083454764833

theorem tailTrace_1517560 : CollatzResearch.WordTrace tailWord_1517560 prefixEnd_1517560 346327867572083454764833 := by
  unfold tailWord_1517560
  simp only [CollatzResearch.WordTrace]
  refine ⟨27674980191073386729423067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36899973588097848972564089 27674980191073386729423067)
  ·
    refine ⟨41512470286610080094134601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27674980191073386729423067 41512470286610080094134601)
    ·
      refine ⟨31134352714957560070600951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41512470286610080094134601 31134352714957560070600951)
      ·
        refine ⟨46701529072436340105901427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31134352714957560070600951 46701529072436340105901427)
        ·
          refine ⟨70052293608654510158852141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46701529072436340105901427 70052293608654510158852141)
          ·
            refine ⟨26269610103245441309569553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70052293608654510158852141 26269610103245441309569553)
            ·
              refine ⟨19702207577434080982177165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26269610103245441309569553 19702207577434080982177165)
              ·
                refine ⟨7388327841537780368316437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19702207577434080982177165 7388327841537780368316437)
                ·
                  refine ⟨346327867572083454764833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7388327841537780368316437 346327867572083454764833)
                  ·
                    rfl

theorem cell21_1517560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_1517560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517560 prefixEnd_1517560 := by exact prefixLift 1517560
  have htrace : WordTrace (prefixWord ++ tailWord_1517560) baseStart_1517560 baseEnd_1517560 := by
    simpa [prefixWord, tailWord_1517560, baseEnd_1517560] using wordTrace_append hprefix tailTrace_1517560
  have hstable : (prefixWord ++ tailWord_1517560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517560).length < 2 ^ (prefixWord ++ tailWord_1517560).sum := by decide
  have hdescent : baseEnd_1517560 < baseStart_1517560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517656 : List Nat := [2, 1, 2, 2, 1, 6, 1, 3, 3]
def baseStart_1517656 : Nat := 118140960795 + 1517656 * 2 ^ 59
def prefixEnd_1517656 : Nat := 4983230072969 + 3 ^ 40 * 1517656 * 2
def baseEnd_1517656 : Nat := 346349776080008621164637

theorem tailTrace_1517656 : CollatzResearch.WordTrace tailWord_1517656 prefixEnd_1517656 346349776080008621164637 := by
  unfold tailWord_1517656
  simp only [CollatzResearch.WordTrace]
  refine ⟨27676730894899490927170411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36902307859865987902893881 27676730894899490927170411)
  ·
    refine ⟨41515096342349236390755617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27676730894899490927170411 41515096342349236390755617)
    ·
      refine ⟨31136322256761927293066713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41515096342349236390755617 31136322256761927293066713)
      ·
        refine ⟨23352241692571445469800035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31136322256761927293066713 23352241692571445469800035)
        ·
          refine ⟨35028362538857168204700053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23352241692571445469800035 35028362538857168204700053)
          ·
            refine ⟨1641954494008929759595315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35028362538857168204700053 1641954494008929759595315)
            ·
              refine ⟨2462931741013394639392973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641954494008929759595315 2462931741013394639392973)
              ·
                refine ⟨923599402880022989772365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2462931741013394639392973 923599402880022989772365)
                ·
                  refine ⟨346349776080008621164637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923599402880022989772365 346349776080008621164637)
                  ·
                    rfl

theorem cell21_1517656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_1517656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517656 prefixEnd_1517656 := by exact prefixLift 1517656
  have htrace : WordTrace (prefixWord ++ tailWord_1517656) baseStart_1517656 baseEnd_1517656 := by
    simpa [prefixWord, tailWord_1517656, baseEnd_1517656] using wordTrace_append hprefix tailTrace_1517656
  have hstable : (prefixWord ++ tailWord_1517656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517656).length < 2 ^ (prefixWord ++ tailWord_1517656).sum := by decide
  have hdescent : baseEnd_1517656 < baseStart_1517656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517718 : List Nat := [5, 3, 2, 1, 10]
def baseStart_1517718 : Nat := 118140960795 + 1517718 * 2 ^ 59
def prefixEnd_1517718 : Nat := 4983230072969 + 3 ^ 40 * 1517718 * 2
def baseEnd_1517718 : Nat := 4276097843514941865817

theorem tailTrace_1517718 : CollatzResearch.WordTrace tailWord_1517718 prefixEnd_1517718 4276097843514941865817 := by
  unfold tailWord_1517718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459732694723397902693613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36903815410382910962065205 3459732694723397902693613)
  ·
    refine ⟨1297399760521274213510105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3459732694723397902693613 1297399760521274213510105)
    ·
      refine ⟨973049820390955660132579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1297399760521274213510105 973049820390955660132579)
      ·
        refine ⟨1459574730586433490198869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973049820390955660132579 1459574730586433490198869)
        ·
          refine ⟨4276097843514941865817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1459574730586433490198869 4276097843514941865817)
          ·
            rfl

theorem cell21_1517718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 10].length) (baseStart_1517718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517718 prefixEnd_1517718 := by exact prefixLift 1517718
  have htrace : WordTrace (prefixWord ++ tailWord_1517718) baseStart_1517718 baseEnd_1517718 := by
    simpa [prefixWord, tailWord_1517718, baseEnd_1517718] using wordTrace_append hprefix tailTrace_1517718
  have hstable : (prefixWord ++ tailWord_1517718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517718).length < 2 ^ (prefixWord ++ tailWord_1517718).sum := by decide
  have hdescent : baseEnd_1517718 < baseStart_1517718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517729 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 4]
def baseStart_1517729 : Nat := 118140960795 + 1517729 * 2 ^ 59
def prefixEnd_1517729 : Nat := 4983230072969 + 3 ^ 40 * 1517729 * 2
def baseEnd_1517729 : Nat := 346366435674576716447821

theorem tailTrace_1517729 : CollatzResearch.WordTrace tailWord_1517729 prefixEnd_1517729 346366435674576716447821 := by
  unfold tailWord_1517729
  simp only [CollatzResearch.WordTrace]
  refine ⟨55356124318534515321748241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36904082879023010214498827 55356124318534515321748241)
  ·
    refine ⟨41517093238900886491311181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55356124318534515321748241 41517093238900886491311181)
    ·
      refine ⟨15568909964587832434241693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41517093238900886491311181 15568909964587832434241693)
      ·
        refine ⟨5838341236720437162840635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15568909964587832434241693 5838341236720437162840635)
        ·
          refine ⟨8757511855080655744260953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5838341236720437162840635 8757511855080655744260953)
          ·
            refine ⟨6568133891310491808195715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8757511855080655744260953 6568133891310491808195715)
            ·
              refine ⟨9852200836965737712293573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6568133891310491808195715 9852200836965737712293573)
              ·
                refine ⟨1847287656931075821055045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9852200836965737712293573 1847287656931075821055045)
                ·
                  refine ⟨346366435674576716447821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847287656931075821055045 346366435674576716447821)
                  ·
                    rfl

theorem cell21_1517729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_1517729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517729 prefixEnd_1517729 := by exact prefixLift 1517729
  have htrace : WordTrace (prefixWord ++ tailWord_1517729) baseStart_1517729 baseEnd_1517729 := by
    simpa [prefixWord, tailWord_1517729, baseEnd_1517729] using wordTrace_append hprefix tailTrace_1517729
  have hstable : (prefixWord ++ tailWord_1517729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517729).length < 2 ^ (prefixWord ++ tailWord_1517729).sum := by decide
  have hdescent : baseEnd_1517729 < baseStart_1517729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517732 : List Nat := [2, 3, 1, 2, 4, 1, 1, 4, 3]
def baseStart_1517732 : Nat := 118140960795 + 1517732 * 2 ^ 59
def prefixEnd_1517732 : Nat := 4983230072969 + 3 ^ 40 * 1517732 * 2
def baseEnd_1517732 : Nat := 346367120315449377897815

theorem tailTrace_1517732 : CollatzResearch.WordTrace tailWord_1517732 prefixEnd_1517732 346367120315449377897815 := by
  unfold tailWord_1517732
  simp only [CollatzResearch.WordTrace]
  refine ⟨27678116868761823417053725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36904155825015764556071633 27678116868761823417053725)
  ·
    refine ⟨10379293825785683781395147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27678116868761823417053725 10379293825785683781395147)
    ·
      refine ⟨15568940738678525672092721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10379293825785683781395147 15568940738678525672092721)
      ·
        refine ⟨11676705554008894254069541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15568940738678525672092721 11676705554008894254069541)
        ·
          refine ⟨2189382291376667672638039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11676705554008894254069541 2189382291376667672638039)
          ·
            refine ⟨3284073437065001508957059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189382291376667672638039 3284073437065001508957059)
            ·
              refine ⟨4926110155597502263435589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284073437065001508957059 4926110155597502263435589)
              ·
                refine ⟨923645654174531674394173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4926110155597502263435589 923645654174531674394173)
                ·
                  refine ⟨346367120315449377897815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923645654174531674394173 346367120315449377897815)
                  ·
                    rfl

theorem cell21_1517732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_1517732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517732 prefixEnd_1517732 := by exact prefixLift 1517732
  have htrace : WordTrace (prefixWord ++ tailWord_1517732) baseStart_1517732 baseEnd_1517732 := by
    simpa [prefixWord, tailWord_1517732, baseEnd_1517732] using wordTrace_append hprefix tailTrace_1517732
  have hstable : (prefixWord ++ tailWord_1517732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517732).length < 2 ^ (prefixWord ++ tailWord_1517732).sum := by decide
  have hdescent : baseEnd_1517732 < baseStart_1517732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517760 : List Nat := [2, 1, 1, 2, 5, 2, 3, 5]
def baseStart_1517760 : Nat := 118140960795 + 1517760 * 2 ^ 59
def prefixEnd_1517760 : Nat := 4983230072969 + 3 ^ 40 * 1517760 * 2
def baseEnd_1517760 : Nat := 115457836765642517143697

theorem tailTrace_1517760 : CollatzResearch.WordTrace tailWord_1517760 prefixEnd_1517760 115457836765642517143697 := by
  unfold tailWord_1517760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27678627490711103808063367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36904836654281471744084489 27678627490711103808063367)
  ·
    refine ⟨41517941236066655712095051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27678627490711103808063367 41517941236066655712095051)
    ·
      refine ⟨62276911854099983568142577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41517941236066655712095051 62276911854099983568142577)
      ·
        refine ⟨46707683890574987676106933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62276911854099983568142577 46707683890574987676106933)
        ·
          refine ⟨4378845364741405094635025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46707683890574987676106933 4378845364741405094635025)
          ·
            refine ⟨3284134023556053820976269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4378845364741405094635025 3284134023556053820976269)
            ·
              refine ⟨1231550258833520182866101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3284134023556053820976269 1231550258833520182866101)
              ·
                refine ⟨115457836765642517143697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1231550258833520182866101 115457836765642517143697)
                ·
                  rfl

theorem cell21_1517760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_1517760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517760 prefixEnd_1517760 := by exact prefixLift 1517760
  have htrace : WordTrace (prefixWord ++ tailWord_1517760) baseStart_1517760 baseEnd_1517760 := by
    simpa [prefixWord, tailWord_1517760, baseEnd_1517760] using wordTrace_append hprefix tailTrace_1517760
  have hstable : (prefixWord ++ tailWord_1517760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517760).length < 2 ^ (prefixWord ++ tailWord_1517760).sum := by decide
  have hdescent : baseEnd_1517760 < baseStart_1517760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517918 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1517918 : Nat := 118140960795 + 1517918 * 2 ^ 59
def prefixEnd_1517918 : Nat := 4983230072969 + 3 ^ 40 * 1517918 * 2
def baseEnd_1517918 : Nat := 346409568049554387797435

theorem tailTrace_1517918 : CollatzResearch.WordTrace tailWord_1517918 prefixEnd_1517918 346409568049554387797435 := by
  unfold tailWord_1517918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920377214356225075047301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36908678476566533733585605 6920377214356225075047301)
  ·
    refine ⟨1297570727691792201571369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6920377214356225075047301 1297570727691792201571369)
    ·
      refine ⟨973178045768844151178527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1297570727691792201571369 973178045768844151178527)
      ·
        refine ⟨1459767068653266226767791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973178045768844151178527 1459767068653266226767791)
        ·
          refine ⟨2189650602979899340151687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459767068653266226767791 2189650602979899340151687)
          ·
            refine ⟨3284475904469849010227531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189650602979899340151687 3284475904469849010227531)
            ·
              refine ⟨4926713856704773515341297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284475904469849010227531 4926713856704773515341297)
              ·
                refine ⟨3695035392528580136505973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4926713856704773515341297 3695035392528580136505973)
                ·
                  refine ⟨346409568049554387797435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3695035392528580136505973 346409568049554387797435)
                  ·
                    rfl

theorem cell21_1517918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1517918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1517918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1517918 prefixEnd_1517918 := by exact prefixLift 1517918
  have htrace : WordTrace (prefixWord ++ tailWord_1517918) baseStart_1517918 baseEnd_1517918 := by
    simpa [prefixWord, tailWord_1517918, baseEnd_1517918] using wordTrace_append hprefix tailTrace_1517918
  have hstable : (prefixWord ++ tailWord_1517918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517918).length < 2 ^ (prefixWord ++ tailWord_1517918).sum := by decide
  have hdescent : baseEnd_1517918 < baseStart_1517918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518016 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_1518016 : Nat := 118140960795 + 1518016 * 2 ^ 59
def prefixEnd_1518016 : Nat := 4983230072969 + 3 ^ 40 * 1518016 * 2
def baseEnd_1518016 : Nat := 346431932984727995163901

theorem tailTrace_1518016 : CollatzResearch.WordTrace tailWord_1518016 prefixEnd_1518016 346431932984727995163901 := by
  unfold tailWord_1518016
  simp only [CollatzResearch.WordTrace]
  refine ⟨27683296034247381668722951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36911061378996508891630601 27683296034247381668722951)
  ·
    refine ⟨41524944051371072503084427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27683296034247381668722951 41524944051371072503084427)
    ·
      refine ⟨62287416077056608754626641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41524944051371072503084427 62287416077056608754626641)
      ·
        refine ⟨46715562057792456565969981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62287416077056608754626641 46715562057792456565969981)
        ·
          refine ⟨17518335771672171212238743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46715562057792456565969981 17518335771672171212238743)
          ·
            refine ⟨26277503657508256818358115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17518335771672171212238743 26277503657508256818358115)
            ·
              refine ⟨39416255486262385227537173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26277503657508256818358115 39416255486262385227537173)
              ·
                refine ⟨1847636975918549307540805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39416255486262385227537173 1847636975918549307540805)
                ·
                  refine ⟨346431932984727995163901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847636975918549307540805 346431932984727995163901)
                  ·
                    rfl

theorem cell21_1518016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_1518016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518016 prefixEnd_1518016 := by exact prefixLift 1518016
  have htrace : WordTrace (prefixWord ++ tailWord_1518016) baseStart_1518016 baseEnd_1518016 := by
    simpa [prefixWord, tailWord_1518016, baseEnd_1518016] using wordTrace_append hprefix tailTrace_1518016
  have hstable : (prefixWord ++ tailWord_1518016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518016).length < 2 ^ (prefixWord ++ tailWord_1518016).sum := by decide
  have hdescent : baseEnd_1518016 < baseStart_1518016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518106 : List Nat := [3, 1, 1, 3, 1, 1, 2, 9]
def baseStart_1518106 : Nat := 118140960795 + 1518106 * 2 ^ 59
def prefixEnd_1518106 : Nat := 4983230072969 + 3 ^ 40 * 1518106 * 2
def baseEnd_1518106 : Nat := 115484157403635946221239

theorem tailTrace_1518106 : CollatzResearch.WordTrace tailWord_1518106 prefixEnd_1518106 115484157403635946221239 := by
  unfold tailWord_1518106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13842468659542177177055543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36913249758779139138814781 13842468659542177177055543)
  ·
    refine ⟨20763702989313265765583315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13842468659542177177055543 20763702989313265765583315)
    ·
      refine ⟨31145554483969898648374973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20763702989313265765583315 31145554483969898648374973)
      ·
        refine ⟨11679582931488711993140615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31145554483969898648374973 11679582931488711993140615)
        ·
          refine ⟨17519374397233067989710923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11679582931488711993140615 17519374397233067989710923)
          ·
            refine ⟨26279061595849601984566385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17519374397233067989710923 26279061595849601984566385)
            ·
              refine ⟨19709296196887201488424789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26279061595849601984566385 19709296196887201488424789)
              ·
                refine ⟨115484157403635946221239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19709296196887201488424789 115484157403635946221239)
                ·
                  rfl

theorem cell21_1518106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_1518106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518106 prefixEnd_1518106 := by exact prefixLift 1518106
  have htrace : WordTrace (prefixWord ++ tailWord_1518106) baseStart_1518106 baseEnd_1518106 := by
    simpa [prefixWord, tailWord_1518106, baseEnd_1518106] using wordTrace_append hprefix tailTrace_1518106
  have hstable : (prefixWord ++ tailWord_1518106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518106).length < 2 ^ (prefixWord ++ tailWord_1518106).sum := by decide
  have hdescent : baseEnd_1518106 < baseStart_1518106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518112 : List Nat := [2, 1, 1, 6, 2, 1, 2, 3, 3]
def baseStart_1518112 : Nat := 118140960795 + 1518112 * 2 ^ 59
def prefixEnd_1518112 : Nat := 4983230072969 + 3 ^ 40 * 1518112 * 2
def baseEnd_1518112 : Nat := 346453841492653161563705

theorem tailTrace_1518112 : CollatzResearch.WordTrace tailWord_1518112 prefixEnd_1518112 346453841492653161563705 := by
  unfold tailWord_1518112
  simp only [CollatzResearch.WordTrace]
  refine ⟨27685046738073485866470295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36913395650764647821960393 27685046738073485866470295)
  ·
    refine ⟨41527570107110228799705443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27685046738073485866470295 41527570107110228799705443)
    ·
      refine ⟨62291355160665343199558165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41527570107110228799705443 62291355160665343199558165)
      ·
        refine ⟨2919907273156187962479289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62291355160665343199558165 2919907273156187962479289)
        ·
          refine ⟨2189930454867140971859467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2919907273156187962479289 2189930454867140971859467)
          ·
            refine ⟨3284895682300711457789201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189930454867140971859467 3284895682300711457789201)
            ·
              refine ⟨2463671761725533593341901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3284895682300711457789201 2463671761725533593341901)
              ·
                refine ⟨923876910647075097503213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2463671761725533593341901 923876910647075097503213)
                ·
                  refine ⟨346453841492653161563705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923876910647075097503213 346453841492653161563705)
                  ·
                    rfl

theorem cell21_1518112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_1518112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518112 prefixEnd_1518112 := by exact prefixLift 1518112
  have htrace : WordTrace (prefixWord ++ tailWord_1518112) baseStart_1518112 baseEnd_1518112 := by
    simpa [prefixWord, tailWord_1518112, baseEnd_1518112] using wordTrace_append hprefix tailTrace_1518112
  have hstable : (prefixWord ++ tailWord_1518112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518112).length < 2 ^ (prefixWord ++ tailWord_1518112).sum := by decide
  have hdescent : baseEnd_1518112 < baseStart_1518112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518157 : List Nat := [1, 6, 1, 1, 2, 3, 2, 5]
def baseStart_1518157 : Nat := 118140960795 + 1518157 * 2 ^ 59
def prefixEnd_1518157 : Nat := 4983230072969 + 3 ^ 40 * 1518157 * 2
def baseEnd_1518157 : Nat := 115488037035247694437871

theorem tailTrace_1518157 : CollatzResearch.WordTrace tailWord_1518157 prefixEnd_1518157 115488037035247694437871 := by
  unfold tailWord_1518157
  simp only [CollatzResearch.WordTrace]
  refine ⟨55371734760983944418328725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36914489840655962945552483 55371734760983944418328725)
  ·
    refine ⟨2595550066921122394609159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55371734760983944418328725 2595550066921122394609159)
    ·
      refine ⟨3893325100381683591913739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595550066921122394609159 3893325100381683591913739)
      ·
        refine ⟨5839987650572525387870609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893325100381683591913739 5839987650572525387870609)
        ·
          refine ⟨4379990737929394040902957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5839987650572525387870609 4379990737929394040902957)
          ·
            refine ⟨1642496526723522765338609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4379990737929394040902957 1642496526723522765338609)
            ·
              refine ⟨1231872395042642074003957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642496526723522765338609 1231872395042642074003957)
              ·
                refine ⟨115488037035247694437871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1231872395042642074003957 115488037035247694437871)
                ·
                  rfl

theorem cell21_1518157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 5].length) (baseStart_1518157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518157 prefixEnd_1518157 := by exact prefixLift 1518157
  have htrace : WordTrace (prefixWord ++ tailWord_1518157) baseStart_1518157 baseEnd_1518157 := by
    simpa [prefixWord, tailWord_1518157, baseEnd_1518157] using wordTrace_append hprefix tailTrace_1518157
  have hstable : (prefixWord ++ tailWord_1518157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518157).length < 2 ^ (prefixWord ++ tailWord_1518157).sum := by decide
  have hdescent : baseEnd_1518157 < baseStart_1518157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518174 : List Nat := [4, 4, 1, 2, 1, 2, 7]
def baseStart_1518174 : Nat := 118140960795 + 1518174 * 2 ^ 59
def prefixEnd_1518174 : Nat := 4983230072969 + 3 ^ 40 * 1518174 * 2
def baseEnd_1518174 : Nat := 38496443415261647947805

theorem tailTrace_1518174 : CollatzResearch.WordTrace tailWord_1518174 prefixEnd_1518174 38496443415261647947805 := by
  unfold tailWord_1518174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921544350240294540212197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36914903201281570881131717 6921544350240294540212197)
  ·
    refine ⟨1297789565670055226289787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6921544350240294540212197 1297789565670055226289787)
    ·
      refine ⟨1946684348505082839434681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1297789565670055226289787 1946684348505082839434681)
      ·
        refine ⟨1460013261378812129576011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1946684348505082839434681 1460013261378812129576011)
        ·
          refine ⟨2190019892068218194364017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460013261378812129576011 2190019892068218194364017)
          ·
            refine ⟨1642514919051163645773013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190019892068218194364017 1642514919051163645773013)
            ·
              refine ⟨38496443415261647947805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1642514919051163645773013 38496443415261647947805)
              ·
                rfl

theorem cell21_1518174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 7].length) (baseStart_1518174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518174 prefixEnd_1518174 := by exact prefixLift 1518174
  have htrace : WordTrace (prefixWord ++ tailWord_1518174) baseStart_1518174 baseEnd_1518174 := by
    simpa [prefixWord, tailWord_1518174, baseEnd_1518174] using wordTrace_append hprefix tailTrace_1518174
  have hstable : (prefixWord ++ tailWord_1518174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518174).length < 2 ^ (prefixWord ++ tailWord_1518174).sum := by decide
  have hdescent : baseEnd_1518174 < baseStart_1518174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518250 : List Nat := [3, 1, 5, 2, 2, 1, 1, 6]
def baseStart_1518250 : Nat := 118140960795 + 1518250 * 2 ^ 59
def prefixEnd_1518250 : Nat := 4983230072969 + 3 ^ 40 * 1518250 * 2
def baseEnd_1518250 : Nat := 115495111657598529421141

theorem tailTrace_1518250 : CollatzResearch.WordTrace tailWord_1518250 prefixEnd_1518250 115495111657598529421141 := by
  unfold tailWord_1518250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13843781687411755325366051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36916751166431347534309469 13843781687411755325366051)
  ·
    refine ⟨20765672531117632988049077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13843781687411755325366051 20765672531117632988049077)
    ·
      refine ⟨1946781799792278092629601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20765672531117632988049077 1946781799792278092629601)
      ·
        refine ⟨1460086349844208569472201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1946781799792278092629601 1460086349844208569472201)
        ·
          refine ⟨1095064762383156427104151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1460086349844208569472201 1095064762383156427104151)
          ·
            refine ⟨1642597143574734640656227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095064762383156427104151 1642597143574734640656227)
            ·
              refine ⟨2463895715362101960984341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642597143574734640656227 2463895715362101960984341)
              ·
                refine ⟨115495111657598529421141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2463895715362101960984341 115495111657598529421141)
                ·
                  rfl

theorem cell21_1518250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_1518250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518250 prefixEnd_1518250 := by exact prefixLift 1518250
  have htrace : WordTrace (prefixWord ++ tailWord_1518250) baseStart_1518250 baseEnd_1518250 := by
    simpa [prefixWord, tailWord_1518250, baseEnd_1518250] using wordTrace_append hprefix tailTrace_1518250
  have hstable : (prefixWord ++ tailWord_1518250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518250).length < 2 ^ (prefixWord ++ tailWord_1518250).sum := by decide
  have hdescent : baseEnd_1518250 < baseStart_1518250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518261 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 4]
def baseStart_1518261 : Nat := 118140960795 + 1518261 * 2 ^ 59
def prefixEnd_1518261 : Nat := 4983230072969 + 3 ^ 40 * 1518261 * 2
def baseEnd_1518261 : Nat := 346487845322662013580067

theorem tailTrace_1518261 : CollatzResearch.WordTrace tailWord_1518261 prefixEnd_1518261 346487845322662013580067 := by
  unfold tailWord_1518261
  simp only [CollatzResearch.WordTrace]
  refine ⟨55375527952607170180114637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36917018635071446786743091 55375527952607170180114637)
  ·
    refine ⟨20765822982227688817542989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55375527952607170180114637 20765822982227688817542989)
    ·
      refine ⟨7787183618335383306578621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20765822982227688817542989 7787183618335383306578621)
      ·
        refine ⟨2920193856875768739966983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7787183618335383306578621 2920193856875768739966983)
        ·
          refine ⟨4380290785313653109950475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2920193856875768739966983 4380290785313653109950475)
          ·
            refine ⟨6570436177970479664925713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380290785313653109950475 6570436177970479664925713)
            ·
              refine ⟨4927827133477859748694285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6570436177970479664925713 4927827133477859748694285)
              ·
                refine ⟨1847935175054197405760357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4927827133477859748694285 1847935175054197405760357)
                ·
                  refine ⟨346487845322662013580067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847935175054197405760357 346487845322662013580067)
                  ·
                    rfl

theorem cell21_1518261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_1518261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518261 prefixEnd_1518261 := by exact prefixLift 1518261
  have htrace : WordTrace (prefixWord ++ tailWord_1518261) baseStart_1518261 baseEnd_1518261 := by
    simpa [prefixWord, tailWord_1518261, baseEnd_1518261] using wordTrace_append hprefix tailTrace_1518261
  have hstable : (prefixWord ++ tailWord_1518261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518261).length < 2 ^ (prefixWord ++ tailWord_1518261).sum := by decide
  have hdescent : baseEnd_1518261 < baseStart_1518261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518424 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_1518424 : Nat := 118140960795 + 1518424 * 2 ^ 59
def prefixEnd_1518424 : Nat := 4983230072969 + 3 ^ 40 * 1518424 * 2
def baseEnd_1518424 : Nat := 346525044143409952363067

theorem tailTrace_1518424 : CollatzResearch.WordTrace tailWord_1518424 prefixEnd_1518424 346525044143409952363067 := by
  unfold tailWord_1518424
  simp only [CollatzResearch.WordTrace]
  refine ⟨27690736525508324509149163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36920982034011099345532217 27690736525508324509149163)
  ·
    refine ⟨41536104788262486763723745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27690736525508324509149163 41536104788262486763723745)
    ·
      refine ⟨31152078591196865072792809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41536104788262486763723745 31152078591196865072792809)
      ·
        refine ⟨23364058943397648804594607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31152078591196865072792809 23364058943397648804594607)
        ·
          refine ⟨35046088415096473206891911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23364058943397648804594607 35046088415096473206891911)
          ·
            refine ⟨52569132622644709810337867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35046088415096473206891911 52569132622644709810337867)
            ·
              refine ⟨78853698933967064715506801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52569132622644709810337867 78853698933967064715506801)
              ·
                refine ⟨59140274200475298536630101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78853698933967064715506801 59140274200475298536630101)
                ·
                  refine ⟨346525044143409952363067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59140274200475298536630101 346525044143409952363067)
                  ·
                    rfl

theorem cell21_1518424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_1518424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518424 prefixEnd_1518424 := by exact prefixLift 1518424
  have htrace : WordTrace (prefixWord ++ tailWord_1518424) baseStart_1518424 baseEnd_1518424 := by
    simpa [prefixWord, tailWord_1518424, baseEnd_1518424] using wordTrace_append hprefix tailTrace_1518424
  have hstable : (prefixWord ++ tailWord_1518424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518424).length < 2 ^ (prefixWord ++ tailWord_1518424).sum := by decide
  have hdescent : baseEnd_1518424 < baseStart_1518424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518472 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_1518472 : Nat := 118140960795 + 1518472 * 2 ^ 59
def prefixEnd_1518472 : Nat := 4983230072969 + 3 ^ 40 * 1518472 * 2
def baseEnd_1518472 : Nat := 346535998397372535562969

theorem tailTrace_1518472 : CollatzResearch.WordTrace tailWord_1518472 prefixEnd_1518472 346535998397372535562969 := by
  unfold tailWord_1518472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27691611877421376608022835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36922149169895168810697113 27691611877421376608022835)
  ·
    refine ⟨41537417816132064912034253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27691611877421376608022835 41537417816132064912034253)
    ·
      refine ⟨15576531681049524342012845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41537417816132064912034253 15576531681049524342012845)
      ·
        refine ⟨5841199380393571628254817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15576531681049524342012845 5841199380393571628254817)
        ·
          refine ⟨4380899535295178721191113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5841199380393571628254817 4380899535295178721191113)
          ·
            refine ⟨3285674651471384040893335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4380899535295178721191113 3285674651471384040893335)
            ·
              refine ⟨4928511977207076061340003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285674651471384040893335 4928511977207076061340003)
              ·
                refine ⟨7392767965810614092010005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928511977207076061340003 7392767965810614092010005)
                ·
                  refine ⟨346535998397372535562969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7392767965810614092010005 346535998397372535562969)
                  ·
                    rfl

theorem cell21_1518472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_1518472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518472 prefixEnd_1518472 := by exact prefixLift 1518472
  have htrace : WordTrace (prefixWord ++ tailWord_1518472) baseStart_1518472 baseEnd_1518472 := by
    simpa [prefixWord, tailWord_1518472, baseEnd_1518472] using wordTrace_append hprefix tailTrace_1518472
  have hstable : (prefixWord ++ tailWord_1518472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518472).length < 2 ^ (prefixWord ++ tailWord_1518472).sum := by decide
  have hdescent : baseEnd_1518472 < baseStart_1518472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518503 : List Nat := [1, 1, 6, 1, 3, 1, 1, 7]
def baseStart_1518503 : Nat := 118140960795 + 1518503 * 2 ^ 59
def prefixEnd_1518503 : Nat := 4983230072969 + 3 ^ 40 * 1518503 * 2
def baseEnd_1518503 : Nat := 115514357673241123515413

theorem tailTrace_1518503 : CollatzResearch.WordTrace tailWord_1518503 prefixEnd_1518503 115514357673241123515413 := by
  unfold tailWord_1518503
  simp only [CollatzResearch.WordTrace]
  refine ⟨55384354417730445510424163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36922902945153630340282775 55384354417730445510424163)
  ·
    refine ⟨83076531626595668265636245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55384354417730445510424163 83076531626595668265636245)
    ·
      refine ⟨3894212419996671949951699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83076531626595668265636245 3894212419996671949951699)
      ·
        refine ⟨5841318629995007924927549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894212419996671949951699 5841318629995007924927549)
        ·
          refine ⟨2190494486248127971847831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5841318629995007924927549 2190494486248127971847831)
          ·
            refine ⟨3285741729372191957771747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190494486248127971847831 3285741729372191957771747)
            ·
              refine ⟨4928612594058287936657621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285741729372191957771747 4928612594058287936657621)
              ·
                refine ⟨115514357673241123515413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4928612594058287936657621 115514357673241123515413)
                ·
                  rfl

theorem cell21_1518503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 7].length) (baseStart_1518503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518503 prefixEnd_1518503 := by exact prefixLift 1518503
  have htrace : WordTrace (prefixWord ++ tailWord_1518503) baseStart_1518503 baseEnd_1518503 := by
    simpa [prefixWord, tailWord_1518503, baseEnd_1518503] using wordTrace_append hprefix tailTrace_1518503
  have hstable : (prefixWord ++ tailWord_1518503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518503).length < 2 ^ (prefixWord ++ tailWord_1518503).sum := by decide
  have hdescent : baseEnd_1518503 < baseStart_1518503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518509 : List Nat := [1, 5, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1518509 : Nat := 118140960795 + 1518509 * 2 ^ 59
def prefixEnd_1518509 : Nat := 4983230072969 + 3 ^ 40 * 1518509 * 2
def baseEnd_1518509 : Nat := 346544442301468693446227

theorem tailTrace_1518509 : CollatzResearch.WordTrace tailWord_1518509 prefixEnd_1518509 346544442301468693446227 := by
  unfold tailWord_1518509
  simp only [CollatzResearch.WordTrace]
  refine ⟨55384573255708708535142581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36923048837139139023428387 55384573255708708535142581)
  ·
    refine ⟨5192303742722691425169617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55384573255708708535142581 5192303742722691425169617)
    ·
      refine ⟨3894227807042018568877213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5192303742722691425169617 3894227807042018568877213)
      ·
        refine ⟨1460335427640756963328955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3894227807042018568877213 1460335427640756963328955)
        ·
          refine ⟨2190503141461135444993433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460335427640756963328955 2190503141461135444993433)
          ·
            refine ⟨1642877356095851583745075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190503141461135444993433 1642877356095851583745075)
            ·
              refine ⟨2464316034143777375617613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642877356095851583745075 2464316034143777375617613)
              ·
                refine ⟨924118512803916515856605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2464316034143777375617613 924118512803916515856605)
                ·
                  refine ⟨346544442301468693446227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924118512803916515856605 346544442301468693446227)
                  ·
                    rfl

theorem cell21_1518509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1518509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518509 prefixEnd_1518509 := by exact prefixLift 1518509
  have htrace : WordTrace (prefixWord ++ tailWord_1518509) baseStart_1518509 baseEnd_1518509 := by
    simpa [prefixWord, tailWord_1518509, baseEnd_1518509] using wordTrace_append hprefix tailTrace_1518509
  have hstable : (prefixWord ++ tailWord_1518509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518509).length < 2 ^ (prefixWord ++ tailWord_1518509).sum := by decide
  have hdescent : baseEnd_1518509 < baseStart_1518509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518638 : List Nat := [4, 1, 3, 1, 1, 1, 10]
def baseStart_1518638 : Nat := 118140960795 + 1518638 * 2 ^ 59
def prefixEnd_1518638 : Nat := 4983230072969 + 3 ^ 40 * 1518638 * 2
def baseEnd_1518638 : Nat := 38508209095443681755107

theorem tailTrace_1518638 : CollatzResearch.WordTrace tailWord_1518638 prefixEnd_1518638 38508209095443681755107 := by
  unfold tailWord_1518638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923659784030170445823571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36926185514827575711059045 6923659784030170445823571)
  ·
    refine ⟨10385489676045255668735357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6923659784030170445823571 10385489676045255668735357)
    ·
      refine ⟨3894558628516970875775759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10385489676045255668735357 3894558628516970875775759)
      ·
        refine ⟨5841837942775456313663639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894558628516970875775759 5841837942775456313663639)
        ·
          refine ⟨8762756914163184470495459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841837942775456313663639 8762756914163184470495459)
          ·
            refine ⟨13144135371244776705743189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762756914163184470495459 13144135371244776705743189)
            ·
              refine ⟨38508209095443681755107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13144135371244776705743189 38508209095443681755107)
              ·
                rfl

theorem cell21_1518638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 10].length) (baseStart_1518638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518638 prefixEnd_1518638 := by exact prefixLift 1518638
  have htrace : WordTrace (prefixWord ++ tailWord_1518638) baseStart_1518638 baseEnd_1518638 := by
    simpa [prefixWord, tailWord_1518638, baseEnd_1518638] using wordTrace_append hprefix tailTrace_1518638
  have hstable : (prefixWord ++ tailWord_1518638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518638).length < 2 ^ (prefixWord ++ tailWord_1518638).sum := by decide
  have hdescent : baseEnd_1518638 < baseStart_1518638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518678 : List Nat := [5, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1518678 : Nat := 118140960795 + 1518678 * 2 ^ 59
def prefixEnd_1518678 : Nat := 4983230072969 + 3 ^ 40 * 1518678 * 2
def baseEnd_1518678 : Nat := 346583010403961955129215

theorem tailTrace_1518678 : CollatzResearch.WordTrace tailWord_1518678 prefixEnd_1518678 346583010403961955129215 := by
  unfold tailWord_1518678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461921074506028149877793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36927158128064300265363125 3461921074506028149877793)
  ·
    refine ⟨2596440805879521112408345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3461921074506028149877793 2596440805879521112408345)
    ·
      refine ⟨1947330604409640834306259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2596440805879521112408345 1947330604409640834306259)
      ·
        refine ⟨2920995906614461251459389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947330604409640834306259 2920995906614461251459389)
        ·
          refine ⟨1095373464980422969297271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2920995906614461251459389 1095373464980422969297271)
          ·
            refine ⟨1643060197470634453945907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095373464980422969297271 1643060197470634453945907)
            ·
              refine ⟨2464590296205951680918861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643060197470634453945907 2464590296205951680918861)
              ·
                refine ⟨924221361077231880344573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2464590296205951680918861 924221361077231880344573)
                ·
                  refine ⟨346583010403961955129215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924221361077231880344573 346583010403961955129215)
                  ·
                    rfl

theorem cell21_1518678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1518678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518678 prefixEnd_1518678 := by exact prefixLift 1518678
  have htrace : WordTrace (prefixWord ++ tailWord_1518678) baseStart_1518678 baseEnd_1518678 := by
    simpa [prefixWord, tailWord_1518678, baseEnd_1518678] using wordTrace_append hprefix tailTrace_1518678
  have hstable : (prefixWord ++ tailWord_1518678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518678).length < 2 ^ (prefixWord ++ tailWord_1518678).sum := by decide
  have hdescent : baseEnd_1518678 < baseStart_1518678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518697 : List Nat := [1, 2, 1, 1, 1, 6, 9]
def baseStart_1518697 : Nat := 118140960795 + 1518697 * 2 ^ 59
def prefixEnd_1518697 : Nat := 4983230072969 + 3 ^ 40 * 1518697 * 2
def baseEnd_1518697 : Nat := 38509705162535793812501

theorem tailTrace_1518697 : CollatzResearch.WordTrace tailWord_1518697 prefixEnd_1518697 38509705162535793812501 := by
  unfold tailWord_1518697
  simp only [CollatzResearch.WordTrace]
  refine ⟨55391430179027616642986345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36927620119351744428657563 55391430179027616642986345)
  ·
    refine ⟨41543572634270712482239759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55391430179027616642986345 41543572634270712482239759)
    ·
      refine ⟨62315358951406068723359639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41543572634270712482239759 62315358951406068723359639)
      ·
        refine ⟨93473038427109103085039459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62315358951406068723359639 93473038427109103085039459)
        ·
          refine ⟨140209557640663654627559189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93473038427109103085039459 140209557640663654627559189)
          ·
            refine ⟨6572323014406108810666837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140209557640663654627559189 6572323014406108810666837)
            ·
              refine ⟨38509705162535793812501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6572323014406108810666837 38509705162535793812501)
              ·
                rfl

theorem cell21_1518697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 9].length) (baseStart_1518697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518697 prefixEnd_1518697 := by exact prefixLift 1518697
  have htrace : WordTrace (prefixWord ++ tailWord_1518697) baseStart_1518697 baseEnd_1518697 := by
    simpa [prefixWord, tailWord_1518697, baseEnd_1518697] using wordTrace_append hprefix tailTrace_1518697
  have hstable : (prefixWord ++ tailWord_1518697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518697).length < 2 ^ (prefixWord ++ tailWord_1518697).sum := by decide
  have hdescent : baseEnd_1518697 < baseStart_1518697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518934 : List Nat := [5, 2, 3, 1, 1, 2, 1, 6]
def baseStart_1518934 : Nat := 118140960795 + 1518934 * 2 ^ 59
def prefixEnd_1518934 : Nat := 4983230072969 + 3 ^ 40 * 1518934 * 2
def baseEnd_1518934 : Nat := 115547144363920799620675

theorem tailTrace_1518934 : CollatzResearch.WordTrace tailWord_1518934 prefixEnd_1518934 115547144363920799620675 := by
  unfold tailWord_1518934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3462504642448062882460241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36933382852779337412909237 3462504642448062882460241)
  ·
    refine ⟨2596878481836047161845181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3462504642448062882460241 2596878481836047161845181)
    ·
      refine ⟨973829430688517685691943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2596878481836047161845181 973829430688517685691943)
      ·
        refine ⟨1460744146032776528537915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973829430688517685691943 1460744146032776528537915)
        ·
          refine ⟨2191116219049164792806873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460744146032776528537915 2191116219049164792806873)
          ·
            refine ⟨1643337164286873594605155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2191116219049164792806873 1643337164286873594605155)
            ·
              refine ⟨2465005746430310391907733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643337164286873594605155 2465005746430310391907733)
              ·
                refine ⟨115547144363920799620675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2465005746430310391907733 115547144363920799620675)
                ·
                  rfl

theorem cell21_1518934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_1518934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518934 prefixEnd_1518934 := by exact prefixLift 1518934
  have htrace : WordTrace (prefixWord ++ tailWord_1518934) baseStart_1518934 baseEnd_1518934 := by
    simpa [prefixWord, tailWord_1518934, baseEnd_1518934] using wordTrace_append hprefix tailTrace_1518934
  have hstable : (prefixWord ++ tailWord_1518934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518934).length < 2 ^ (prefixWord ++ tailWord_1518934).sum := by decide
  have hdescent : baseEnd_1518934 < baseStart_1518934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518956 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_1518956 : Nat := 118140960795 + 1518956 * 2 ^ 59
def prefixEnd_1518956 : Nat := 4983230072969 + 3 ^ 40 * 1518956 * 2
def baseEnd_1518956 : Nat := 346646453791495249495313

theorem tailTrace_1518956 : CollatzResearch.WordTrace tailWord_1518956 prefixEnd_1518956 346646453791495249495313 := by
  unfold tailWord_1518956
  simp only [CollatzResearch.WordTrace]
  refine ⟨27700438342544651938332361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36933917790059535917776481 27700438342544651938332361)
  ·
    refine ⟨20775328756908488953749271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27700438342544651938332361 20775328756908488953749271)
    ·
      refine ⟨31162993135362733430623907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20775328756908488953749271 31162993135362733430623907)
      ·
        refine ⟨46744489703044100145935861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31162993135362733430623907 46744489703044100145935861)
        ·
          refine ⟨4382295909660384388681487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46744489703044100145935861 4382295909660384388681487)
          ·
            refine ⟨6573443864490576583022231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382295909660384388681487 6573443864490576583022231)
            ·
              refine ⟨9860165796735864874533347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6573443864490576583022231 9860165796735864874533347)
              ·
                refine ⟨14790248695103797311800021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9860165796735864874533347 14790248695103797311800021)
                ·
                  refine ⟨346646453791495249495313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14790248695103797311800021 346646453791495249495313)
                  ·
                    rfl

theorem cell21_1518956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_1518956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518956 prefixEnd_1518956 := by exact prefixLift 1518956
  have htrace : WordTrace (prefixWord ++ tailWord_1518956) baseStart_1518956 baseEnd_1518956 := by
    simpa [prefixWord, tailWord_1518956, baseEnd_1518956] using wordTrace_append hprefix tailTrace_1518956
  have hstable : (prefixWord ++ tailWord_1518956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518956).length < 2 ^ (prefixWord ++ tailWord_1518956).sum := by decide
  have hdescent : baseEnd_1518956 < baseStart_1518956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518970 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1518970 : Nat := 118140960795 + 1518970 * 2 ^ 59
def prefixEnd_1518970 : Nat := 4983230072969 + 3 ^ 40 * 1518970 * 2
def baseEnd_1518970 : Nat := 346649648782234336261951

theorem tailTrace_1518970 : CollatzResearch.WordTrace tailWord_1518970 prefixEnd_1518970 346649648782234336261951 := by
  unfold tailWord_1518970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13850346826759646066918591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36934258204692389511782909 13850346826759646066918591)
  ·
    refine ⟨20775520240139469100377887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13850346826759646066918591 20775520240139469100377887)
    ·
      refine ⟨31163280360209203650566831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20775520240139469100377887 31163280360209203650566831)
      ·
        refine ⟨46744920540313805475850247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31163280360209203650566831 46744920540313805475850247)
        ·
          refine ⟨70117380810470708213775371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46744920540313805475850247 70117380810470708213775371)
          ·
            refine ⟨105176071215706062320663057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70117380810470708213775371 105176071215706062320663057)
            ·
              refine ⟨78882053411779546740497293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105176071215706062320663057 78882053411779546740497293)
              ·
                refine ⟨29580770029417330027686485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78882053411779546740497293 29580770029417330027686485)
                ·
                  refine ⟨346649648782234336261951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29580770029417330027686485 346649648782234336261951)
                  ·
                    rfl

theorem cell21_1518970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1518970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518970 prefixEnd_1518970 := by exact prefixLift 1518970
  have htrace : WordTrace (prefixWord ++ tailWord_1518970) baseStart_1518970 baseEnd_1518970 := by
    simpa [prefixWord, tailWord_1518970, baseEnd_1518970] using wordTrace_append hprefix tailTrace_1518970
  have hstable : (prefixWord ++ tailWord_1518970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518970).length < 2 ^ (prefixWord ++ tailWord_1518970).sum := by decide
  have hdescent : baseEnd_1518970 < baseStart_1518970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1518990 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1518990 : Nat := 118140960795 + 1518990 * 2 ^ 59
def prefixEnd_1518990 : Nat := 4983230072969 + 3 ^ 40 * 1518990 * 2
def baseEnd_1518990 : Nat := 346654213054718745928577

theorem tailTrace_1518990 : CollatzResearch.WordTrace tailWord_1518990 prefixEnd_1518990 346654213054718745928577 := by
  unfold tailWord_1518990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6925264595870765960425303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36934744511310751788934949 6925264595870765960425303)
  ·
    refine ⟨10387896893806148940637955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6925264595870765960425303 10387896893806148940637955)
    ·
      refine ⟨15581845340709223410956933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10387896893806148940637955 15581845340709223410956933)
      ·
        refine ⟨2921596001382979389554425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15581845340709223410956933 2921596001382979389554425)
        ·
          refine ⟨2191197001037234542165819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921596001382979389554425 2191197001037234542165819)
          ·
            refine ⟨3286795501555851813248729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2191197001037234542165819 3286795501555851813248729)
            ·
              refine ⟨2465096626166888859936547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286795501555851813248729 2465096626166888859936547)
              ·
                refine ⟨3697644939250333289904821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465096626166888859936547 3697644939250333289904821)
                ·
                  refine ⟨346654213054718745928577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3697644939250333289904821 346654213054718745928577)
                  ·
                    rfl

theorem cell21_1518990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1518990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1518990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1518990 prefixEnd_1518990 := by exact prefixLift 1518990
  have htrace : WordTrace (prefixWord ++ tailWord_1518990) baseStart_1518990 baseEnd_1518990 := by
    simpa [prefixWord, tailWord_1518990, baseEnd_1518990] using wordTrace_append hprefix tailTrace_1518990
  have hstable : (prefixWord ++ tailWord_1518990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1518990).length < 2 ^ (prefixWord ++ tailWord_1518990).sum := by decide
  have hdescent : baseEnd_1518990 < baseStart_1518990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1518990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519091 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 9]
def baseStart_1519091 : Nat := 118140960795 + 1519091 * 2 ^ 59
def prefixEnd_1519091 : Nat := 4983230072969 + 3 ^ 40 * 1519091 * 2
def baseEnd_1519091 : Nat := 346677262630765014745037

theorem tailTrace_1519091 : CollatzResearch.WordTrace tailWord_1519091 prefixEnd_1519091 346677262630765014745037 := by
  unfold tailWord_1519091
  simp only [CollatzResearch.WordTrace]
  refine ⟨55405800539600221932829127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36937200359733481288552751 55405800539600221932829127)
  ·
    refine ⟨83108700809400332899243691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55405800539600221932829127 83108700809400332899243691)
    ·
      refine ⟨124663051214100499348865537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83108700809400332899243691 124663051214100499348865537)
      ·
        refine ⟨93497288410575374511649153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124663051214100499348865537 93497288410575374511649153)
        ·
          refine ⟨70122966307931530883736865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93497288410575374511649153 70122966307931530883736865)
          ·
            refine ⟨52592224730948648162802649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70122966307931530883736865 52592224730948648162802649)
            ·
              refine ⟨39444168548211486122101987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52592224730948648162802649 39444168548211486122101987)
              ·
                refine ⟨59166252822317229183152981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39444168548211486122101987 59166252822317229183152981)
                ·
                  refine ⟨346677262630765014745037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59166252822317229183152981 346677262630765014745037)
                  ·
                    rfl

theorem cell21_1519091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_1519091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519091 prefixEnd_1519091 := by exact prefixLift 1519091
  have htrace : WordTrace (prefixWord ++ tailWord_1519091) baseStart_1519091 baseEnd_1519091 := by
    simpa [prefixWord, tailWord_1519091, baseEnd_1519091] using wordTrace_append hprefix tailTrace_1519091
  have hstable : (prefixWord ++ tailWord_1519091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519091).length < 2 ^ (prefixWord ++ tailWord_1519091).sum := by decide
  have hdescent : baseEnd_1519091 < baseStart_1519091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519229 : List Nat := [1, 4, 1, 1, 4, 1, 1, 8]
def baseStart_1519229 : Nat := 118140960795 + 1519229 * 2 ^ 59
def prefixEnd_1519229 : Nat := 4983230072969 + 3 ^ 40 * 1519229 * 2
def baseEnd_1519229 : Nat := 115569585370302480481585

theorem tailTrace_1519229 : CollatzResearch.WordTrace tailWord_1519229 prefixEnd_1519229 115569585370302480481585 := by
  unfold tailWord_1519229
  simp only [CollatzResearch.WordTrace]
  refine ⟨55410833813100271501352741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36940555875400181000901827 55410833813100271501352741)
  ·
    refine ⟨10389531339956300906503639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55410833813100271501352741 10389531339956300906503639)
    ·
      refine ⟨15584297009934451359755459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10389531339956300906503639 15584297009934451359755459)
      ·
        refine ⟨23376445514901677039633189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15584297009934451359755459 23376445514901677039633189)
        ·
          refine ⟨4383083534044064444931223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23376445514901677039633189 4383083534044064444931223)
          ·
            refine ⟨6574625301066096667396835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383083534044064444931223 6574625301066096667396835)
            ·
              refine ⟨9861937951599145001095253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6574625301066096667396835 9861937951599145001095253)
              ·
                refine ⟨115569585370302480481585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9861937951599145001095253 115569585370302480481585)
                ·
                  rfl

theorem cell21_1519229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 8].length) (baseStart_1519229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519229 prefixEnd_1519229 := by exact prefixLift 1519229
  have htrace : WordTrace (prefixWord ++ tailWord_1519229) baseStart_1519229 baseEnd_1519229 := by
    simpa [prefixWord, tailWord_1519229, baseEnd_1519229] using wordTrace_append hprefix tailTrace_1519229
  have hstable : (prefixWord ++ tailWord_1519229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519229).length < 2 ^ (prefixWord ++ tailWord_1519229).sum := by decide
  have hdescent : baseEnd_1519229 < baseStart_1519229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519243 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 7]
def baseStart_1519243 : Nat := 118140960795 + 1519243 * 2 ^ 59
def prefixEnd_1519243 : Nat := 4983230072969 + 3 ^ 40 * 1519243 * 2
def baseEnd_1519243 : Nat := 346711951101646528211393

theorem tailTrace_1519243 : CollatzResearch.WordTrace tailWord_1519243 prefixEnd_1519243 346711951101646528211393 := by
  unfold tailWord_1519243
  simp only [CollatzResearch.WordTrace]
  refine ⟨55411344435049551892362383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36940896290033034594908255 55411344435049551892362383)
  ·
    refine ⟨83117016652574327838543575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55411344435049551892362383 83117016652574327838543575)
    ·
      refine ⟨124675524978861491757815363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83117016652574327838543575 124675524978861491757815363)
      ·
        refine ⟨187013287468292237636723045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124675524978861491757815363 187013287468292237636723045)
        ·
          refine ⟨35064991400304794556885571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187013287468292237636723045 35064991400304794556885571)
          ·
            refine ⟨52597487100457191835328357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35064991400304794556885571 52597487100457191835328357)
            ·
              refine ⟨9862028831335723469124067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52597487100457191835328357 9862028831335723469124067)
              ·
                refine ⟨14793043247003585203686101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9862028831335723469124067 14793043247003585203686101)
                ·
                  refine ⟨346711951101646528211393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14793043247003585203686101 346711951101646528211393)
                  ·
                    rfl

theorem cell21_1519243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_1519243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519243 prefixEnd_1519243 := by exact prefixLift 1519243
  have htrace : WordTrace (prefixWord ++ tailWord_1519243) baseStart_1519243 baseEnd_1519243 := by
    simpa [prefixWord, tailWord_1519243, baseEnd_1519243] using wordTrace_append hprefix tailTrace_1519243
  have hstable : (prefixWord ++ tailWord_1519243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519243).length < 2 ^ (prefixWord ++ tailWord_1519243).sum := by decide
  have hdescent : baseEnd_1519243 < baseStart_1519243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519319 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 7]
def baseStart_1519319 : Nat := 118140960795 + 1519319 * 2 ^ 59
def prefixEnd_1519319 : Nat := 4983230072969 + 3 ^ 40 * 1519319 * 2
def baseEnd_1519319 : Nat := 346729295337087284944571

theorem tailTrace_1519319 : CollatzResearch.WordTrace tailWord_1519319 prefixEnd_1519319 346729295337087284944571 := by
  unfold tailWord_1519319
  simp only [CollatzResearch.WordTrace]
  refine ⟨55414116382774216872129011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36942744255182811248086007 55414116382774216872129011)
  ·
    refine ⟨83121174574161325308193517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55414116382774216872129011 83121174574161325308193517)
    ·
      refine ⟨31170440465310496990572569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83121174574161325308193517 31170440465310496990572569)
      ·
        refine ⟨23377830348982872742929427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31170440465310496990572569 23377830348982872742929427)
        ·
          refine ⟨35066745523474309114394141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23377830348982872742929427 35066745523474309114394141)
          ·
            refine ⟨13150029571302865917897803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35066745523474309114394141 13150029571302865917897803)
            ·
              refine ⟨19725044356954298876846705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13150029571302865917897803 19725044356954298876846705)
              ·
                refine ⟨14793783267715724157635029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19725044356954298876846705 14793783267715724157635029)
                ·
                  refine ⟨346729295337087284944571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14793783267715724157635029 346729295337087284944571)
                  ·
                    rfl

theorem cell21_1519319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_1519319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519319 prefixEnd_1519319 := by exact prefixLift 1519319
  have htrace : WordTrace (prefixWord ++ tailWord_1519319) baseStart_1519319 baseEnd_1519319 := by
    simpa [prefixWord, tailWord_1519319, baseEnd_1519319] using wordTrace_append hprefix tailTrace_1519319
  have hstable : (prefixWord ++ tailWord_1519319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519319).length < 2 ^ (prefixWord ++ tailWord_1519319).sum := by decide
  have hdescent : baseEnd_1519319 < baseStart_1519319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519336 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_1519336 : Nat := 118140960795 + 1519336 * 2 ^ 59
def prefixEnd_1519336 : Nat := 4983230072969 + 3 ^ 40 * 1519336 * 2
def baseEnd_1519336 : Nat := 346733174968699033161203

theorem tailTrace_1519336 : CollatzResearch.WordTrace tailWord_1519336 prefixEnd_1519336 346733174968699033161203 := by
  unfold tailWord_1519336
  simp only [CollatzResearch.WordTrace]
  refine ⟨27707368211856314387748931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36943157615808419183665241 27707368211856314387748931)
  ·
    refine ⟨41561052317784471581623397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27707368211856314387748931 41561052317784471581623397)
    ·
      refine ⟨7792697309584588421554387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41561052317784471581623397 7792697309584588421554387)
      ·
        refine ⟨11689045964376882632331581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7792697309584588421554387 11689045964376882632331581)
        ·
          refine ⟨4383392236641330987124343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11689045964376882632331581 4383392236641330987124343)
          ·
            refine ⟨6575088354961996480686515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383392236641330987124343 6575088354961996480686515)
            ·
              refine ⟨9862632532442994721029773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6575088354961996480686515 9862632532442994721029773)
              ·
                refine ⟨3698487199666123020386165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9862632532442994721029773 3698487199666123020386165)
                ·
                  refine ⟨346733174968699033161203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3698487199666123020386165 346733174968699033161203)
                  ·
                    rfl

theorem cell21_1519336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_1519336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519336 prefixEnd_1519336 := by exact prefixLift 1519336
  have htrace : WordTrace (prefixWord ++ tailWord_1519336) baseStart_1519336 baseEnd_1519336 := by
    simpa [prefixWord, tailWord_1519336, baseEnd_1519336] using wordTrace_append hprefix tailTrace_1519336
  have hstable : (prefixWord ++ tailWord_1519336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519336).length < 2 ^ (prefixWord ++ tailWord_1519336).sum := by decide
  have hdescent : baseEnd_1519336 < baseStart_1519336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519370 : List Nat := [3, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_1519370 : Nat := 118140960795 + 1519370 * 2 ^ 59
def prefixEnd_1519370 : Nat := 4983230072969 + 3 ^ 40 * 1519370 * 2
def baseEnd_1519370 : Nat := 346740934231922529594467

theorem tailTrace_1519370 : CollatzResearch.WordTrace tailWord_1519370 prefixEnd_1519370 346740934231922529594467 := by
  unfold tailWord_1519370
  simp only [CollatzResearch.WordTrace]
  refine ⟨13853994126397363145558891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36943984337059635054823709 13853994126397363145558891)
  ·
    refine ⟨20780991189596044718338337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13853994126397363145558891 20780991189596044718338337)
    ·
      refine ⟨15585743392197033538753753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20780991189596044718338337 15585743392197033538753753)
      ·
        refine ⟨11689307544147775154065315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15585743392197033538753753 11689307544147775154065315)
        ·
          refine ⟨17533961316221662731097973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11689307544147775154065315 17533961316221662731097973)
          ·
            refine ⟨1643808873395780881040435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17533961316221662731097973 1643808873395780881040435)
            ·
              refine ⟨2465713310093671321560653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643808873395780881040435 2465713310093671321560653)
              ·
                refine ⟨924642491285126745585245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2465713310093671321560653 924642491285126745585245)
                ·
                  refine ⟨346740934231922529594467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924642491285126745585245 346740934231922529594467)
                  ·
                    rfl

theorem cell21_1519370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_1519370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519370 prefixEnd_1519370 := by exact prefixLift 1519370
  have htrace : WordTrace (prefixWord ++ tailWord_1519370) baseStart_1519370 baseEnd_1519370 := by
    simpa [prefixWord, tailWord_1519370, baseEnd_1519370] using wordTrace_append hprefix tailTrace_1519370
  have hstable : (prefixWord ++ tailWord_1519370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519370).length < 2 ^ (prefixWord ++ tailWord_1519370).sum := by decide
  have hdescent : baseEnd_1519370 < baseStart_1519370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519373 : List Nat := [1, 7, 2, 1, 1, 2, 7]
def baseStart_1519373 : Nat := 118140960795 + 1519373 * 2 ^ 59
def prefixEnd_1519373 : Nat := 4983230072969 + 3 ^ 40 * 1519373 * 2
def baseEnd_1519373 : Nat := 38526846541421687893829

theorem tailTrace_1519373 : CollatzResearch.WordTrace tailWord_1519373 prefixEnd_1519373 38526846541421687893829 := by
  unfold tailWord_1519373
  simp only [CollatzResearch.WordTrace]
  refine ⟨55416085924578584094594773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36944057283052389396396515 55416085924578584094594773)
  ·
    refine ⟨1298814513857310564717065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 55416085924578584094594773 1298814513857310564717065)
    ·
      refine ⟨974110885392982923537799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1298814513857310564717065 974110885392982923537799)
      ·
        refine ⟨1461166328089474385306699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974110885392982923537799 1461166328089474385306699)
        ·
          refine ⟨2191749492134211577960049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461166328089474385306699 2191749492134211577960049)
          ·
            refine ⟨1643812119100658683470037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2191749492134211577960049 1643812119100658683470037)
            ·
              refine ⟨38526846541421687893829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1643812119100658683470037 38526846541421687893829)
              ·
                rfl

theorem cell21_1519373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 7].length) (baseStart_1519373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519373 prefixEnd_1519373 := by exact prefixLift 1519373
  have htrace : WordTrace (prefixWord ++ tailWord_1519373) baseStart_1519373 baseEnd_1519373 := by
    simpa [prefixWord, tailWord_1519373, baseEnd_1519373] using wordTrace_append hprefix tailTrace_1519373
  have hstable : (prefixWord ++ tailWord_1519373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519373).length < 2 ^ (prefixWord ++ tailWord_1519373).sum := by decide
  have hdescent : baseEnd_1519373 < baseStart_1519373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519381 : List Nat := [1, 3, 2, 1, 2, 5, 7]
def baseStart_1519381 : Nat := 118140960795 + 1519381 * 2 ^ 59
def prefixEnd_1519381 : Nat := 4983230072969 + 3 ^ 40 * 1519381 * 2
def baseEnd_1519381 : Nat := 38527049397976550545679

theorem tailTrace_1519381 : CollatzResearch.WordTrace tailWord_1519381 prefixEnd_1519381 38527049397976550545679 := by
  unfold tailWord_1519381
  simp only [CollatzResearch.WordTrace]
  refine ⟨55416377708549601460885997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36944251805699734307257331 55416377708549601460885997)
  ·
    refine ⟨20781141640706100547832249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55416377708549601460885997 20781141640706100547832249)
    ·
      refine ⟨15585856230529575410874187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20781141640706100547832249 15585856230529575410874187)
      ·
        refine ⟨23378784345794363116311281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15585856230529575410874187 23378784345794363116311281)
        ·
          refine ⟨17534088259345772337233461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23378784345794363116311281 17534088259345772337233461)
          ·
            refine ⟨1643820774313666156615637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17534088259345772337233461 1643820774313666156615637)
            ·
              refine ⟨38527049397976550545679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1643820774313666156615637 38527049397976550545679)
              ·
                rfl

theorem cell21_1519381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 7].length) (baseStart_1519381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519381 prefixEnd_1519381 := by exact prefixLift 1519381
  have htrace : WordTrace (prefixWord ++ tailWord_1519381) baseStart_1519381 baseEnd_1519381 := by
    simpa [prefixWord, tailWord_1519381, baseEnd_1519381] using wordTrace_append hprefix tailTrace_1519381
  have hstable : (prefixWord ++ tailWord_1519381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519381).length < 2 ^ (prefixWord ++ tailWord_1519381).sum := by decide
  have hdescent : baseEnd_1519381 < baseStart_1519381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519564 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_1519564 : Nat := 118140960795 + 1519564 * 2 ^ 59
def prefixEnd_1519564 : Nat := 4983230072969 + 3 ^ 40 * 1519564 * 2
def baseEnd_1519564 : Nat := 346785207675021303360737

theorem tailTrace_1519564 : CollatzResearch.WordTrace tailWord_1519564 prefixEnd_1519564 346785207675021303360737 := by
  unfold tailWord_1519564
  simp only [CollatzResearch.WordTrace]
  refine ⟨27711526133443311857398873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36948701511257749143198497 27711526133443311857398873)
  ·
    refine ⟨20783644600082483893049155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27711526133443311857398873 20783644600082483893049155)
    ·
      refine ⟨31175466900123725839573733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20783644600082483893049155 31175466900123725839573733)
      ·
        refine ⟨5845400043773198594920075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31175466900123725839573733 5845400043773198594920075)
        ·
          refine ⟨8768100065659797892380113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845400043773198594920075 8768100065659797892380113)
          ·
            refine ⟨6576075049244848419285085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8768100065659797892380113 6576075049244848419285085)
            ·
              refine ⟨2466028143466818157231907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6576075049244848419285085 2466028143466818157231907)
              ·
                refine ⟨3699042215200227235847861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466028143466818157231907 3699042215200227235847861)
                ·
                  refine ⟨346785207675021303360737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3699042215200227235847861 346785207675021303360737)
                  ·
                    rfl

theorem cell21_1519564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_1519564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519564 prefixEnd_1519564 := by exact prefixLift 1519564
  have htrace : WordTrace (prefixWord ++ tailWord_1519564) baseStart_1519564 baseEnd_1519564 := by
    simpa [prefixWord, tailWord_1519564, baseEnd_1519564] using wordTrace_append hprefix tailTrace_1519564
  have hstable : (prefixWord ++ tailWord_1519564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519564).length < 2 ^ (prefixWord ++ tailWord_1519564).sum := by decide
  have hdescent : baseEnd_1519564 < baseStart_1519564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519570 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_1519570 : Nat := 118140960795 + 1519570 * 2 ^ 59
def prefixEnd_1519570 : Nat := 4983230072969 + 3 ^ 40 * 1519570 * 2
def baseEnd_1519570 : Nat := 346786576956766626260725

theorem tailTrace_1519570 : CollatzResearch.WordTrace tailWord_1519570 prefixEnd_1519570 346786576956766626260725 := by
  unfold tailWord_1519570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855817776216221684879041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36948847403243257826344109 13855817776216221684879041)
  ·
    refine ⟨10391863332162166263659281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13855817776216221684879041 10391863332162166263659281)
    ·
      refine ⟨7793897499121624697744461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10391863332162166263659281 7793897499121624697744461)
      ·
        refine ⟨2922711562170609261654173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7793897499121624697744461 2922711562170609261654173)
        ·
          refine ⟨1096016835813978473120315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2922711562170609261654173 1096016835813978473120315)
          ·
            refine ⟨1644025253720967709680473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096016835813978473120315 1644025253720967709680473)
            ·
              refine ⟨1233018940290725782260355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644025253720967709680473 1233018940290725782260355)
              ·
                refine ⟨1849528410436088673390533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233018940290725782260355 1849528410436088673390533)
                ·
                  refine ⟨346786576956766626260725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1849528410436088673390533 346786576956766626260725)
                  ·
                    rfl

theorem cell21_1519570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_1519570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519570 prefixEnd_1519570 := by exact prefixLift 1519570
  have htrace : WordTrace (prefixWord ++ tailWord_1519570) baseStart_1519570 baseEnd_1519570 := by
    simpa [prefixWord, tailWord_1519570, baseEnd_1519570] using wordTrace_append hprefix tailTrace_1519570
  have hstable : (prefixWord ++ tailWord_1519570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519570).length < 2 ^ (prefixWord ++ tailWord_1519570).sum := by decide
  have hdescent : baseEnd_1519570 < baseStart_1519570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519626 : List Nat := [3, 1, 2, 2, 4, 2, 1, 6]
def baseStart_1519626 : Nat := 118140960795 + 1519626 * 2 ^ 59
def prefixEnd_1519626 : Nat := 4983230072969 + 3 ^ 40 * 1519626 * 2
def baseEnd_1519626 : Nat := 115599785639907657775759

theorem tailTrace_1519626 : CollatzResearch.WordTrace tailWord_1519626 prefixEnd_1519626 115599785639907657775759 := by
  unfold tailWord_1519626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13856328398165502075888683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36950209061774672202369821 13856328398165502075888683)
  ·
    refine ⟨20784492597248253113833025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13856328398165502075888683 20784492597248253113833025)
    ·
      refine ⟨15588369447936189835374769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20784492597248253113833025 15588369447936189835374769)
      ·
        refine ⟨11691277085952142376531077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15588369447936189835374769 11691277085952142376531077)
        ·
          refine ⟨2192114453616026695599577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11691277085952142376531077 2192114453616026695599577)
          ·
            refine ⟨1644085840212020021699683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2192114453616026695599577 1644085840212020021699683)
            ·
              refine ⟨2466128760318030032549525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644085840212020021699683 2466128760318030032549525)
              ·
                refine ⟨115599785639907657775759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2466128760318030032549525 115599785639907657775759)
                ·
                  rfl

theorem cell21_1519626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_1519626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519626 prefixEnd_1519626 := by exact prefixLift 1519626
  have htrace : WordTrace (prefixWord ++ tailWord_1519626) baseStart_1519626 baseEnd_1519626 := by
    simpa [prefixWord, tailWord_1519626, baseEnd_1519626] using wordTrace_append hprefix tailTrace_1519626
  have hstable : (prefixWord ++ tailWord_1519626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519626).length < 2 ^ (prefixWord ++ tailWord_1519626).sum := by decide
  have hdescent : baseEnd_1519626 < baseStart_1519626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519730 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_1519730 : Nat := 118140960795 + 1519730 * 2 ^ 59
def prefixEnd_1519730 : Nat := 4983230072969 + 3 ^ 40 * 1519730 * 2
def baseEnd_1519730 : Nat := 346823091136641903593731

theorem tailTrace_1519730 : CollatzResearch.WordTrace tailWord_1519730 prefixEnd_1519730 346823091136641903593731 := by
  unfold tailWord_1519730
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857276696071308516335161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36952737856190156043560429 13857276696071308516335161)
  ·
    refine ⟨10392957522053481387251371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13857276696071308516335161 10392957522053481387251371)
    ·
      refine ⟨15589436283080222080877057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10392957522053481387251371 15589436283080222080877057)
      ·
        refine ⟨11692077212310166560657793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15589436283080222080877057 11692077212310166560657793)
        ·
          refine ⟨8769057909232624920493345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11692077212310166560657793 8769057909232624920493345)
          ·
            refine ⟨6576793431924468690370009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8769057909232624920493345 6576793431924468690370009)
            ·
              refine ⟨4932595073943351517777507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6576793431924468690370009 4932595073943351517777507)
              ·
                refine ⟨7398892610915027276666261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4932595073943351517777507 7398892610915027276666261)
                ·
                  refine ⟨346823091136641903593731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7398892610915027276666261 346823091136641903593731)
                  ·
                    rfl

theorem cell21_1519730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_1519730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519730 prefixEnd_1519730 := by exact prefixLift 1519730
  have htrace : WordTrace (prefixWord ++ tailWord_1519730) baseStart_1519730 baseEnd_1519730 := by
    simpa [prefixWord, tailWord_1519730, baseEnd_1519730] using wordTrace_append hprefix tailTrace_1519730
  have hstable : (prefixWord ++ tailWord_1519730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519730).length < 2 ^ (prefixWord ++ tailWord_1519730).sum := by decide
  have hdescent : baseEnd_1519730 < baseStart_1519730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519747 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 4]
def baseStart_1519747 : Nat := 118140960795 + 1519747 * 2 ^ 59
def prefixEnd_1519747 : Nat := 4983230072969 + 3 ^ 40 * 1519747 * 2
def baseEnd_1519747 : Nat := 346826970768253651810363

theorem tailTrace_1519747 : CollatzResearch.WordTrace tailWord_1519747 prefixEnd_1519747 346826970768253651810363 := by
  unfold tailWord_1519747
  simp only [CollatzResearch.WordTrace]
  refine ⟨55429726825223645968709495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36953151216815763979139663 55429726825223645968709495)
  ·
    refine ⟨83144590237835468953064243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55429726825223645968709495 83144590237835468953064243)
    ·
      refine ⟨124716885356753203429596365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83144590237835468953064243 124716885356753203429596365)
      ·
        refine ⟨46768832008782451286098637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124716885356753203429596365 46768832008782451286098637)
        ·
          refine ⟨17538312003293419232286989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46768832008782451286098637 17538312003293419232286989)
          ·
            refine ⟨6576867001235032212107621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17538312003293419232286989 6576867001235032212107621)
            ·
              refine ⟨1233162562731568539770179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6576867001235032212107621 1233162562731568539770179)
              ·
                refine ⟨1849743844097352809655269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233162562731568539770179 1849743844097352809655269)
                ·
                  refine ⟨346826970768253651810363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1849743844097352809655269 346826970768253651810363)
                  ·
                    rfl

theorem cell21_1519747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 4].length) (baseStart_1519747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519747 prefixEnd_1519747 := by exact prefixLift 1519747
  have htrace : WordTrace (prefixWord ++ tailWord_1519747) baseStart_1519747 baseEnd_1519747 := by
    simpa [prefixWord, tailWord_1519747, baseEnd_1519747] using wordTrace_append hprefix tailTrace_1519747
  have hstable : (prefixWord ++ tailWord_1519747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519747).length < 2 ^ (prefixWord ++ tailWord_1519747).sum := by decide
  have hdescent : baseEnd_1519747 < baseStart_1519747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519809 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 5]
def baseStart_1519809 : Nat := 118140960795 + 1519809 * 2 ^ 59
def prefixEnd_1519809 : Nat := 4983230072969 + 3 ^ 40 * 1519809 * 2
def baseEnd_1519809 : Nat := 346841120012955321776903

theorem tailTrace_1519809 : CollatzResearch.WordTrace tailWord_1519809 prefixEnd_1519809 346841120012955321776903 := by
  unfold tailWord_1519809
  simp only [CollatzResearch.WordTrace]
  refine ⟨55431988150999030557466481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36954658767332687038310987 55431988150999030557466481)
  ·
    refine ⟨41573991113249272918099861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55431988150999030557466481 41573991113249272918099861)
    ·
      refine ⟨1948780833433559668035931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41573991113249272918099861 1948780833433559668035931)
      ·
        refine ⟨2923171250150339502053897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948780833433559668035931 2923171250150339502053897)
        ·
          refine ⟨2192378437612754626540423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2923171250150339502053897 2192378437612754626540423)
          ·
            refine ⟨3288567656419131939810635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192378437612754626540423 3288567656419131939810635)
            ·
              refine ⟨4932851484628697909715953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3288567656419131939810635 4932851484628697909715953)
              ·
                refine ⟨3699638613471523432286965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4932851484628697909715953 3699638613471523432286965)
                ·
                  refine ⟨346841120012955321776903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3699638613471523432286965 346841120012955321776903)
                  ·
                    rfl

theorem cell21_1519809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_1519809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519809 prefixEnd_1519809 := by exact prefixLift 1519809
  have htrace : WordTrace (prefixWord ++ tailWord_1519809) baseStart_1519809 baseEnd_1519809 := by
    simpa [prefixWord, tailWord_1519809, baseEnd_1519809] using wordTrace_append hprefix tailTrace_1519809
  have hstable : (prefixWord ++ tailWord_1519809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519809).length < 2 ^ (prefixWord ++ tailWord_1519809).sum := by decide
  have hdescent : baseEnd_1519809 < baseStart_1519809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519837 : List Nat := [1, 4, 3, 2, 1, 2, 8]
def baseStart_1519837 : Nat := 118140960795 + 1519837 * 2 ^ 59
def prefixEnd_1519837 : Nat := 4983230072969 + 3 ^ 40 * 1519837 * 2
def baseEnd_1519837 : Nat := 38538612221603721701131

theorem tailTrace_1519837 : CollatzResearch.WordTrace tailWord_1519837 prefixEnd_1519837 38538612221603721701131 := by
  unfold tailWord_1519837
  simp only [CollatzResearch.WordTrace]
  refine ⟨55433009394897591339485765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36955339596598394226323843 55433009394897591339485765)
  ·
    refine ⟨10393689261543298376153581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55433009394897591339485765 10393689261543298376153581)
    ·
      refine ⟨3897633473078736891057593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10393689261543298376153581 3897633473078736891057593)
      ·
        refine ⟨2923225104809052668293195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3897633473078736891057593 2923225104809052668293195)
        ·
          refine ⟨4384837657213579002439793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923225104809052668293195 4384837657213579002439793)
          ·
            refine ⟨3288628242910184251829845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4384837657213579002439793 3288628242910184251829845)
            ·
              refine ⟨38538612221603721701131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3288628242910184251829845 38538612221603721701131)
              ·
                rfl

theorem cell21_1519837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 8].length) (baseStart_1519837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519837 prefixEnd_1519837 := by exact prefixLift 1519837
  have htrace : WordTrace (prefixWord ++ tailWord_1519837) baseStart_1519837 baseEnd_1519837 := by
    simpa [prefixWord, tailWord_1519837, baseEnd_1519837] using wordTrace_append hprefix tailTrace_1519837
  have hstable : (prefixWord ++ tailWord_1519837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519837).length < 2 ^ (prefixWord ++ tailWord_1519837).sum := by decide
  have hdescent : baseEnd_1519837 < baseStart_1519837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519851 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 5]
def baseStart_1519851 : Nat := 118140960795 + 1519851 * 2 ^ 59
def prefixEnd_1519851 : Nat := 4983230072969 + 3 ^ 40 * 1519851 * 2
def baseEnd_1519851 : Nat := 346850704985172582076817

theorem tailTrace_1519851 : CollatzResearch.WordTrace tailWord_1519851 prefixEnd_1519851 346850704985172582076817 := by
  unfold tailWord_1519851
  simp only [CollatzResearch.WordTrace]
  refine ⟨55433520016846871730495407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36955680011231247820330271 55433520016846871730495407)
  ·
    refine ⟨83150280025270307595743111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55433520016846871730495407 83150280025270307595743111)
    ·
      refine ⟨124725420037905461393614667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83150280025270307595743111 124725420037905461393614667)
      ·
        refine ⟨187088130056858192090422001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124725420037905461393614667 187088130056858192090422001)
        ·
          refine ⟨140316097542643644067816501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187088130056858192090422001 140316097542643644067816501)
          ·
            refine ⟨13154634144622841631357797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140316097542643644067816501 13154634144622841631357797)
            ·
              refine ⟨2466493902116782805879587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13154634144622841631357797 2466493902116782805879587)
              ·
                refine ⟨3699740853175174208819381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466493902116782805879587 3699740853175174208819381)
                ·
                  refine ⟨346850704985172582076817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3699740853175174208819381 346850704985172582076817)
                  ·
                    rfl

theorem cell21_1519851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_1519851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519851 prefixEnd_1519851 := by exact prefixLift 1519851
  have htrace : WordTrace (prefixWord ++ tailWord_1519851) baseStart_1519851 baseEnd_1519851 := by
    simpa [prefixWord, tailWord_1519851, baseEnd_1519851] using wordTrace_append hprefix tailTrace_1519851
  have hstable : (prefixWord ++ tailWord_1519851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519851).length < 2 ^ (prefixWord ++ tailWord_1519851).sum := by decide
  have hdescent : baseEnd_1519851 < baseStart_1519851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1519902 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1519902 : Nat := 118140960795 + 1519902 * 2 ^ 59
def prefixEnd_1519902 : Nat := 4983230072969 + 3 ^ 40 * 1519902 * 2
def baseEnd_1519902 : Nat := 346862343880007826726713

theorem tailTrace_1519902 : CollatzResearch.WordTrace tailWord_1519902 prefixEnd_1519902 346862343880007826726713 := by
  unfold tailWord_1519902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929422517457763430075245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36956920093108071627067973 6929422517457763430075245)
  ·
    refine ⟨2598533444046661286278217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6929422517457763430075245 2598533444046661286278217)
    ·
      refine ⟨1948900083034995964708663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2598533444046661286278217 1948900083034995964708663)
      ·
        refine ⟨2923350124552493947062995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948900083034995964708663 2923350124552493947062995)
        ·
          refine ⟨4385025186828740920594493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923350124552493947062995 4385025186828740920594493)
          ·
            refine ⟨1644384445060777845222935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4385025186828740920594493 1644384445060777845222935)
            ·
              refine ⟨2466576667591166767834403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644384445060777845222935 2466576667591166767834403)
              ·
                refine ⟨3699865001386750151751605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466576667591166767834403 3699865001386750151751605)
                ·
                  refine ⟨346862343880007826726713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3699865001386750151751605 346862343880007826726713)
                  ·
                    rfl

theorem cell21_1519902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1519902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1519902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1519902 prefixEnd_1519902 := by exact prefixLift 1519902
  have htrace : WordTrace (prefixWord ++ tailWord_1519902) baseStart_1519902 baseEnd_1519902 := by
    simpa [prefixWord, tailWord_1519902, baseEnd_1519902] using wordTrace_append hprefix tailTrace_1519902
  have hstable : (prefixWord ++ tailWord_1519902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1519902).length < 2 ^ (prefixWord ++ tailWord_1519902).sum := by decide
  have hdescent : baseEnd_1519902 < baseStart_1519902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1519902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520082 : List Nat := [3, 2, 2, 4, 1, 1, 2, 6]
def baseStart_1520082 : Nat := 118140960795 + 1520082 * 2 ^ 59
def prefixEnd_1520082 : Nat := 4983230072969 + 3 ^ 40 * 1520082 * 2
def baseEnd_1520082 : Nat := 115634474110789171242115

theorem tailTrace_1520082 : CollatzResearch.WordTrace tailWord_1520082 prefixEnd_1520082 115634474110789171242115 := by
  unfold tailWord_1520082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13860486319752499545538625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36961296852673332121436333 13860486319752499545538625)
  ·
    refine ⟨10395364739814374659153969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13860486319752499545538625 10395364739814374659153969)
    ·
      refine ⟨7796523554860780994365477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10395364739814374659153969 7796523554860780994365477)
      ·
        refine ⟨1461848166536396436443527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7796523554860780994365477 1461848166536396436443527)
        ·
          refine ⟨2192772249804594654665291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461848166536396436443527 2192772249804594654665291)
          ·
            refine ⟨3289158374706891981997937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192772249804594654665291 3289158374706891981997937)
            ·
              refine ⟨2466868781030168986498453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3289158374706891981997937 2466868781030168986498453)
              ·
                refine ⟨115634474110789171242115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2466868781030168986498453 115634474110789171242115)
                ·
                  rfl

theorem cell21_1520082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_1520082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520082 prefixEnd_1520082 := by exact prefixLift 1520082
  have htrace : WordTrace (prefixWord ++ tailWord_1520082) baseStart_1520082 baseEnd_1520082 := by
    simpa [prefixWord, tailWord_1520082, baseEnd_1520082] using wordTrace_append hprefix tailTrace_1520082
  have hstable : (prefixWord ++ tailWord_1520082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520082).length < 2 ^ (prefixWord ++ tailWord_1520082).sum := by decide
  have hdescent : baseEnd_1520082 < baseStart_1520082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520107 : List Nat := [1, 1, 1, 1, 2, 3, 3, 9]
def baseStart_1520107 : Nat := 118140960795 + 1520107 * 2 ^ 59
def prefixEnd_1520107 : Nat := 4983230072969 + 3 ^ 40 * 1520107 * 2
def baseEnd_1520107 : Nat := 115636375890991008603209

theorem tailTrace_1520107 : CollatzResearch.WordTrace tailWord_1520107 prefixEnd_1520107 115636375890991008603209 := by
  unfold tailWord_1520107
  simp only [CollatzResearch.WordTrace]
  refine ⟨55442857103919427451814575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36961904735946284967876383 55442857103919427451814575)
  ·
    refine ⟨83164285655879141177721863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55442857103919427451814575 83164285655879141177721863)
    ·
      refine ⟨124746428483818711766582795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83164285655879141177721863 124746428483818711766582795)
      ·
        refine ⟨187119642725728067649874193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124746428483818711766582795 187119642725728067649874193)
        ·
          refine ⟨140339732044296050737405645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187119642725728067649874193 140339732044296050737405645)
          ·
            refine ⟨52627399516611019026527117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140339732044296050737405645 52627399516611019026527117)
            ·
              refine ⟨19735274818729132134947669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52627399516611019026527117 19735274818729132134947669)
              ·
                refine ⟨115636375890991008603209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19735274818729132134947669 115636375890991008603209)
                ·
                  rfl

theorem cell21_1520107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 9].length) (baseStart_1520107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520107 prefixEnd_1520107 := by exact prefixLift 1520107
  have htrace : WordTrace (prefixWord ++ tailWord_1520107) baseStart_1520107 baseEnd_1520107 := by
    simpa [prefixWord, tailWord_1520107, baseEnd_1520107] using wordTrace_append hprefix tailTrace_1520107
  have hstable : (prefixWord ++ tailWord_1520107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520107).length < 2 ^ (prefixWord ++ tailWord_1520107).sum := by decide
  have hdescent : baseEnd_1520107 < baseStart_1520107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520130 : List Nat := [3, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1520130 : Nat := 118140960795 + 1520130 * 2 ^ 59
def prefixEnd_1520130 : Nat := 4983230072969 + 3 ^ 40 * 1520130 * 2
def baseEnd_1520130 : Nat := 346914376586330096926247

theorem tailTrace_1520130 : CollatzResearch.WordTrace tailWord_1520130 prefixEnd_1520130 346914376586330096926247 := by
  unfold tailWord_1520130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13860923995709025594975461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36962463988557401586601229 13860923995709025594975461)
  ·
    refine ⟨2598923249195442299057899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13860923995709025594975461 2598923249195442299057899)
    ·
      refine ⟨3898384873793163448586849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2598923249195442299057899 3898384873793163448586849)
      ·
        refine ⟨2923788655344872586440137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3898384873793163448586849 2923788655344872586440137)
        ·
          refine ⟨2192841491508654439830103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2923788655344872586440137 2192841491508654439830103)
          ·
            refine ⟨3289262237262981659745155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192841491508654439830103 3289262237262981659745155)
            ·
              refine ⟨4933893355894472489617733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289262237262981659745155 4933893355894472489617733)
              ·
                refine ⟨925105004230213591803325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4933893355894472489617733 925105004230213591803325)
                ·
                  refine ⟨346914376586330096926247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925105004230213591803325 346914376586330096926247)
                  ·
                    rfl

theorem cell21_1520130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1520130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520130 prefixEnd_1520130 := by exact prefixLift 1520130
  have htrace : WordTrace (prefixWord ++ tailWord_1520130) baseStart_1520130 baseEnd_1520130 := by
    simpa [prefixWord, tailWord_1520130, baseEnd_1520130] using wordTrace_append hprefix tailTrace_1520130
  have hstable : (prefixWord ++ tailWord_1520130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520130).length < 2 ^ (prefixWord ++ tailWord_1520130).sum := by decide
  have hdescent : baseEnd_1520130 < baseStart_1520130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520183 : List Nat := [1, 1, 3, 1, 2, 3, 10]
def baseStart_1520183 : Nat := 118140960795 + 1520183 * 2 ^ 59
def prefixEnd_1520183 : Nat := 4983230072969 + 3 ^ 40 * 1520183 * 2
def baseEnd_1520183 : Nat := 38547385767601531393645

theorem tailTrace_1520183 : CollatzResearch.WordTrace tailWord_1520183 prefixEnd_1520183 38547385767601531393645 := by
  unfold tailWord_1520183
  simp only [CollatzResearch.WordTrace]
  refine ⟨55445629051644092431581203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36963752701096061621054135 55445629051644092431581203)
  ·
    refine ⟨83168443577466138647371805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55445629051644092431581203 83168443577466138647371805)
    ·
      refine ⟨31188166341549801992764427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83168443577466138647371805 31188166341549801992764427)
      ·
        refine ⟨46782249512324702989146641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31188166341549801992764427 46782249512324702989146641)
        ·
          refine ⟨35086687134243527241859981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46782249512324702989146641 35086687134243527241859981)
          ·
            refine ⟨13157507675341322715697493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35086687134243527241859981 13157507675341322715697493)
            ·
              refine ⟨38547385767601531393645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13157507675341322715697493 38547385767601531393645)
              ·
                rfl

theorem cell21_1520183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 10].length) (baseStart_1520183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520183 prefixEnd_1520183 := by exact prefixLift 1520183
  have htrace : WordTrace (prefixWord ++ tailWord_1520183) baseStart_1520183 baseEnd_1520183 := by
    simpa [prefixWord, tailWord_1520183, baseEnd_1520183] using wordTrace_append hprefix tailTrace_1520183
  have hstable : (prefixWord ++ tailWord_1520183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520183).length < 2 ^ (prefixWord ++ tailWord_1520183).sum := by decide
  have hdescent : baseEnd_1520183 < baseStart_1520183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520186 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_1520186 : Nat := 118140960795 + 1520186 * 2 ^ 59
def prefixEnd_1520186 : Nat := 4983230072969 + 3 ^ 40 * 1520186 * 2
def baseEnd_1520186 : Nat := 346927156549286443992799

theorem tailTrace_1520186 : CollatzResearch.WordTrace tailWord_1520186 prefixEnd_1520186 346927156549286443992799 := by
  unfold tailWord_1520186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13861434617658305985985103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36963825647088815962626941 13861434617658305985985103)
  ·
    refine ⟨20792151926487458978977655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13861434617658305985985103 20792151926487458978977655)
    ·
      refine ⟨31188227889731188468466483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20792151926487458978977655 31188227889731188468466483)
      ·
        refine ⟨46782341834596782702699725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31188227889731188468466483 46782341834596782702699725)
        ·
          refine ⟨17543378187973793513512397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46782341834596782702699725 17543378187973793513512397)
          ·
            refine ⟨6578766820490172567567149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17543378187973793513512397 6578766820490172567567149)
            ·
              refine ⟨2467037557683814712837681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6578766820490172567567149 2467037557683814712837681)
              ·
                refine ⟨1850278168262861034628261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467037557683814712837681 1850278168262861034628261)
                ·
                  refine ⟨346927156549286443992799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850278168262861034628261 346927156549286443992799)
                  ·
                    rfl

theorem cell21_1520186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_1520186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520186 prefixEnd_1520186 := by exact prefixLift 1520186
  have htrace : WordTrace (prefixWord ++ tailWord_1520186) baseStart_1520186 baseEnd_1520186 := by
    simpa [prefixWord, tailWord_1520186, baseEnd_1520186] using wordTrace_append hprefix tailTrace_1520186
  have hstable : (prefixWord ++ tailWord_1520186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520186).length < 2 ^ (prefixWord ++ tailWord_1520186).sum := by decide
  have hdescent : baseEnd_1520186 < baseStart_1520186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520259 : List Nat := [1, 1, 1, 3, 3, 1, 3, 8]
def baseStart_1520259 : Nat := 118140960795 + 1520259 * 2 ^ 59
def prefixEnd_1520259 : Nat := 4983230072969 + 3 ^ 40 * 1520259 * 2
def baseEnd_1520259 : Nat := 115647938714618179758661

theorem tailTrace_1520259 : CollatzResearch.WordTrace tailWord_1520259 prefixEnd_1520259 115647938714618179758661 := by
  unfold tailWord_1520259
  simp only [CollatzResearch.WordTrace]
  refine ⟨55448400999368757411347831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36965600666245838274231887 55448400999368757411347831)
  ·
    refine ⟨83172601499053136117021747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55448400999368757411347831 83172601499053136117021747)
    ·
      refine ⟨124758902248579704175532621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83172601499053136117021747 124758902248579704175532621)
      ·
        refine ⟨46784588343217389065824733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124758902248579704175532621 46784588343217389065824733)
        ·
          refine ⟨17544220628706520899684275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46784588343217389065824733 17544220628706520899684275)
          ·
            refine ⟨26316330943059781349526413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17544220628706520899684275 26316330943059781349526413)
            ·
              refine ⟨9868624103647418006072405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26316330943059781349526413 9868624103647418006072405)
              ·
                refine ⟨115647938714618179758661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9868624103647418006072405 115647938714618179758661)
                ·
                  rfl

theorem cell21_1520259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 8].length) (baseStart_1520259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520259 prefixEnd_1520259 := by exact prefixLift 1520259
  have htrace : WordTrace (prefixWord ++ tailWord_1520259) baseStart_1520259 baseEnd_1520259 := by
    simpa [prefixWord, tailWord_1520259, baseEnd_1520259] using wordTrace_append hprefix tailTrace_1520259
  have hstable : (prefixWord ++ tailWord_1520259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520259).length < 2 ^ (prefixWord ++ tailWord_1520259).sum := by decide
  have hdescent : baseEnd_1520259 < baseStart_1520259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520355 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 4]
def baseStart_1520355 : Nat := 118140960795 + 1520355 * 2 ^ 59
def prefixEnd_1520355 : Nat := 4983230072969 + 3 ^ 40 * 1520355 * 2
def baseEnd_1520355 : Nat := 346965724651779705675787

theorem tailTrace_1520355 : CollatzResearch.WordTrace tailWord_1520355 prefixEnd_1520355 346965724651779705675787 := by
  unfold tailWord_1520355
  simp only [CollatzResearch.WordTrace]
  refine ⟨55451902407020965806842519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36967934938013977204561679 55451902407020965806842519)
  ·
    refine ⟨83177853610531448710263779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55451902407020965806842519 83177853610531448710263779)
    ·
      refine ⟨124766780415797173065395669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83177853610531448710263779 124766780415797173065395669)
      ·
        refine ⟨2924221415995246243720211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 124766780415797173065395669 2924221415995246243720211)
        ·
          refine ⟨4386332123992869365580317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924221415995246243720211 4386332123992869365580317)
          ·
            refine ⟨1644874546497326012092619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4386332123992869365580317 1644874546497326012092619)
            ·
              refine ⟨2467311819745989018138929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644874546497326012092619 2467311819745989018138929)
              ·
                refine ⟨1850483864809491763604197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467311819745989018138929 1850483864809491763604197)
                ·
                  refine ⟨346965724651779705675787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850483864809491763604197 346965724651779705675787)
                  ·
                    rfl

theorem cell21_1520355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 4].length) (baseStart_1520355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520355 prefixEnd_1520355 := by exact prefixLift 1520355
  have htrace : WordTrace (prefixWord ++ tailWord_1520355) baseStart_1520355 baseEnd_1520355 := by
    simpa [prefixWord, tailWord_1520355, baseEnd_1520355] using wordTrace_append hprefix tailTrace_1520355
  have hstable : (prefixWord ++ tailWord_1520355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520355).length < 2 ^ (prefixWord ++ tailWord_1520355).sum := by decide
  have hdescent : baseEnd_1520355 < baseStart_1520355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520386 : List Nat := [3, 4, 1, 1, 1, 4, 2, 5]
def baseStart_1520386 : Nat := 118140960795 + 1520386 * 2 ^ 59
def prefixEnd_1520386 : Nat := 4983230072969 + 3 ^ 40 * 1520386 * 2
def baseEnd_1520386 : Nat := 115657599758043513553019

theorem tailTrace_1520386 : CollatzResearch.WordTrace tailWord_1520386 prefixEnd_1520386 115657599758043513553019 := by
  unfold tailWord_1520386
  simp only [CollatzResearch.WordTrace]
  refine ⟨13863258267477164525305253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36968688713272438734147341 13863258267477164525305253)
  ·
    refine ⟨2599360925151968348494735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13863258267477164525305253 2599360925151968348494735)
    ·
      refine ⟨3899041387727952522742103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2599360925151968348494735 3899041387727952522742103)
      ·
        refine ⟨5848562081591928784113155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899041387727952522742103 5848562081591928784113155)
        ·
          refine ⟨8772843122387893176169733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5848562081591928784113155 8772843122387893176169733)
          ·
            refine ⟨1644908085447729970531825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8772843122387893176169733 1644908085447729970531825)
            ·
              refine ⟨1233681064085797477898869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644908085447729970531825 1233681064085797477898869)
              ·
                refine ⟨115657599758043513553019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1233681064085797477898869 115657599758043513553019)
                ·
                  rfl

theorem cell21_1520386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_1520386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520386 prefixEnd_1520386 := by exact prefixLift 1520386
  have htrace : WordTrace (prefixWord ++ tailWord_1520386) baseStart_1520386 baseEnd_1520386 := by
    simpa [prefixWord, tailWord_1520386, baseEnd_1520386] using wordTrace_append hprefix tailTrace_1520386
  have hstable : (prefixWord ++ tailWord_1520386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520386).length < 2 ^ (prefixWord ++ tailWord_1520386).sum := by decide
  have hdescent : baseEnd_1520386 < baseStart_1520386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520473 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 4]
def baseStart_1520473 : Nat := 118140960795 + 1520473 * 2 ^ 59
def prefixEnd_1520473 : Nat := 4983230072969 + 3 ^ 40 * 1520473 * 2
def baseEnd_1520473 : Nat := 346992653859437722708879

theorem tailTrace_1520473 : CollatzResearch.WordTrace tailWord_1520473 prefixEnd_1520473 346992653859437722708879 := by
  unfold tailWord_1520473
  simp only [CollatzResearch.WordTrace]
  refine ⟨55456206220593471959638073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36970804147062314639758715 55456206220593471959638073)
  ·
    refine ⟨41592154665445103969728555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55456206220593471959638073 41592154665445103969728555)
    ·
      refine ⟨62388231998167655954592833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41592154665445103969728555 62388231998167655954592833)
      ·
        refine ⟨46791173998625741965944625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62388231998167655954592833 46791173998625741965944625)
        ·
          refine ⟨35093380498969306474458469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46791173998625741965944625 35093380498969306474458469)
          ·
            refine ⟨6580008843556744963960963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35093380498969306474458469 6580008843556744963960963)
            ·
              refine ⟨9870013265335117445941445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580008843556744963960963 9870013265335117445941445)
              ·
                refine ⟨1850627487250334521114021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9870013265335117445941445 1850627487250334521114021)
                ·
                  refine ⟨346992653859437722708879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850627487250334521114021 346992653859437722708879)
                  ·
                    rfl

theorem cell21_1520473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_1520473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520473 prefixEnd_1520473 := by exact prefixLift 1520473
  have htrace : WordTrace (prefixWord ++ tailWord_1520473) baseStart_1520473 baseEnd_1520473 := by
    simpa [prefixWord, tailWord_1520473, baseEnd_1520473] using wordTrace_append hprefix tailTrace_1520473
  have hstable : (prefixWord ++ tailWord_1520473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520473).length < 2 ^ (prefixWord ++ tailWord_1520473).sum := by decide
  have hdescent : baseEnd_1520473 < baseStart_1520473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520510 : List Nat := [4, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_1520510 : Nat := 118140960795 + 1520510 * 2 ^ 59
def prefixEnd_1520510 : Nat := 4983230072969 + 3 ^ 40 * 1520510 * 2
def baseEnd_1520510 : Nat := 347001097763533880592137

theorem tailTrace_1520510 : CollatzResearch.WordTrace tailWord_1520510 prefixEnd_1520510 347001097763533880592137 := by
  unfold tailWord_1520510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6932194465182428409841873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36971703814306284852489989 6932194465182428409841873)
  ·
    refine ⟨5199145848886821307381405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6932194465182428409841873 5199145848886821307381405)
    ·
      refine ⟨1949679693332557990268027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5199145848886821307381405 1949679693332557990268027)
      ·
        refine ⟨2924519539998836985402041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949679693332557990268027 2924519539998836985402041)
        ·
          refine ⟨2193389654999127739051531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2924519539998836985402041 2193389654999127739051531)
          ·
            refine ⟨3290084482498691608577297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193389654999127739051531 3290084482498691608577297)
            ·
              refine ⟨2467563361874018706432973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290084482498691608577297 2467563361874018706432973)
              ·
                refine ⟨925336260702757014912365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2467563361874018706432973 925336260702757014912365)
                ·
                  refine ⟨347001097763533880592137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925336260702757014912365 347001097763533880592137)
                  ·
                    rfl

theorem cell21_1520510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_1520510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520510 prefixEnd_1520510 := by exact prefixLift 1520510
  have htrace : WordTrace (prefixWord ++ tailWord_1520510) baseStart_1520510 baseEnd_1520510 := by
    simpa [prefixWord, tailWord_1520510, baseEnd_1520510] using wordTrace_append hprefix tailTrace_1520510
  have hstable : (prefixWord ++ tailWord_1520510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520510).length < 2 ^ (prefixWord ++ tailWord_1520510).sum := by decide
  have hdescent : baseEnd_1520510 < baseStart_1520510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520535 : List Nat := [1, 1, 3, 3, 1, 2, 1, 6, 3]
def baseStart_1520535 : Nat := 118140960795 + 1520535 * 2 ^ 59
def prefixEnd_1520535 : Nat := 4983230072969 + 3 ^ 40 * 1520535 * 2
def baseEnd_1520535 : Nat := 347006803104139392675419

theorem tailTrace_1520535 : CollatzResearch.WordTrace tailWord_1520535 prefixEnd_1520535 347006803104139392675419 := by
  unfold tailWord_1520535
  simp only [CollatzResearch.WordTrace]
  refine ⟨55458467546368856548395059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36972311697579237698930039 55458467546368856548395059)
  ·
    refine ⟨83187701319553284822592589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55458467546368856548395059 83187701319553284822592589)
    ·
      refine ⟨31195387994832481808472221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83187701319553284822592589 31195387994832481808472221)
      ·
        refine ⟨11698270498062180678177083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31195387994832481808472221 11698270498062180678177083)
        ·
          refine ⟨17547405747093271017265625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11698270498062180678177083 17547405747093271017265625)
          ·
            refine ⟨13160554310319953262949219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17547405747093271017265625 13160554310319953262949219)
            ·
              refine ⟨19740831465479929894423829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13160554310319953262949219 19740831465479929894423829)
              ·
                refine ⟨925351474944371713801117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19740831465479929894423829 925351474944371713801117)
                ·
                  refine ⟨347006803104139392675419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925351474944371713801117 347006803104139392675419)
                  ·
                    rfl

theorem cell21_1520535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 3].length) (baseStart_1520535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520535 prefixEnd_1520535 := by exact prefixLift 1520535
  have htrace : WordTrace (prefixWord ++ tailWord_1520535) baseStart_1520535 baseEnd_1520535 := by
    simpa [prefixWord, tailWord_1520535, baseEnd_1520535] using wordTrace_append hprefix tailTrace_1520535
  have hstable : (prefixWord ++ tailWord_1520535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520535).length < 2 ^ (prefixWord ++ tailWord_1520535).sum := by decide
  have hdescent : baseEnd_1520535 < baseStart_1520535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520684 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_1520684 : Nat := 118140960795 + 1520684 * 2 ^ 59
def prefixEnd_1520684 : Nat := 4983230072969 + 3 ^ 40 * 1520684 * 2
def baseEnd_1520684 : Nat := 347040806934148244691781

theorem tailTrace_1520684 : CollatzResearch.WordTrace tailWord_1520684 prefixEnd_1520684 347040806934148244691781 := by
  unfold tailWord_1520684
  simp only [CollatzResearch.WordTrace]
  refine ⟨27731951011414527497784553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36975934681886036663712737 27731951011414527497784553)
  ·
    refine ⟨20798963258560895623338415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27731951011414527497784553 20798963258560895623338415)
    ·
      refine ⟨31198444887841343435007623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20798963258560895623338415 31198444887841343435007623)
      ·
        refine ⟨46797667331762015152511435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31198444887841343435007623 46797667331762015152511435)
        ·
          refine ⟨70196500997643022728767153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46797667331762015152511435 70196500997643022728767153)
          ·
            refine ⟨52647375748232267046575365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70196500997643022728767153 52647375748232267046575365)
            ·
              refine ⟨9871382952793550071232881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52647375748232267046575365 9871382952793550071232881)
              ·
                refine ⟨7403537214595162553424661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9871382952793550071232881 7403537214595162553424661)
                ·
                  refine ⟨347040806934148244691781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7403537214595162553424661 347040806934148244691781)
                  ·
                    rfl

theorem cell21_1520684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_1520684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520684 prefixEnd_1520684 := by exact prefixLift 1520684
  have htrace : WordTrace (prefixWord ++ tailWord_1520684) baseStart_1520684 baseEnd_1520684 := by
    simpa [prefixWord, tailWord_1520684, baseEnd_1520684] using wordTrace_append hprefix tailTrace_1520684
  have hstable : (prefixWord ++ tailWord_1520684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520684).length < 2 ^ (prefixWord ++ tailWord_1520684).sum := by decide
  have hdescent : baseEnd_1520684 < baseStart_1520684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520701 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 6]
def baseStart_1520701 : Nat := 118140960795 + 1520701 * 2 ^ 59
def prefixEnd_1520701 : Nat := 4983230072969 + 3 ^ 40 * 1520701 * 2
def baseEnd_1520701 : Nat := 347044686565759992908413

theorem tailTrace_1520701 : CollatzResearch.WordTrace tailWord_1520701 prefixEnd_1520701 347044686565759992908413 := by
  unfold tailWord_1520701
  simp only [CollatzResearch.WordTrace]
  refine ⟨55464522063767466898937957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36976348042511644599291971 55464522063767466898937957)
  ·
    refine ⟨10399597886956400043550867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55464522063767466898937957 10399597886956400043550867)
    ·
      refine ⟨15599396830434600065326301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10399597886956400043550867 15599396830434600065326301)
      ·
        refine ⟨5849773811412975024497363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15599396830434600065326301 5849773811412975024497363)
        ·
          refine ⟨8774660717119462536746045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849773811412975024497363 8774660717119462536746045)
          ·
            refine ⟨3290497768919798451279767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8774660717119462536746045 3290497768919798451279767)
            ·
              refine ⟨4935746653379697676919651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290497768919798451279767 4935746653379697676919651)
              ·
                refine ⟨7403619980069546515379477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935746653379697676919651 7403619980069546515379477)
                ·
                  refine ⟨347044686565759992908413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7403619980069546515379477 347044686565759992908413)
                  ·
                    rfl

theorem cell21_1520701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_1520701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520701 prefixEnd_1520701 := by exact prefixLift 1520701
  have htrace : WordTrace (prefixWord ++ tailWord_1520701) baseStart_1520701 baseEnd_1520701 := by
    simpa [prefixWord, tailWord_1520701, baseEnd_1520701] using wordTrace_append hprefix tailTrace_1520701
  have hstable : (prefixWord ++ tailWord_1520701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520701).length < 2 ^ (prefixWord ++ tailWord_1520701).sum := by decide
  have hdescent : baseEnd_1520701 < baseStart_1520701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520718 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_1520718 : Nat := 118140960795 + 1520718 * 2 ^ 59
def prefixEnd_1520718 : Nat := 4983230072969 + 3 ^ 40 * 1520718 * 2
def baseEnd_1520718 : Nat := 347048566197371741125045

theorem tailTrace_1520718 : CollatzResearch.WordTrace tailWord_1520718 prefixEnd_1520718 347048566197371741125045 := by
  unfold tailWord_1520718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933142763088234850288351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36976761403137252534871205 6933142763088234850288351)
  ·
    refine ⟨10399714144632352275432527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6933142763088234850288351 10399714144632352275432527)
    ·
      refine ⟨15599571216948528413148791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10399714144632352275432527 15599571216948528413148791)
      ·
        refine ⟨23399356825422792619723187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15599571216948528413148791 23399356825422792619723187)
        ·
          refine ⟨35099035238134188929584781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23399356825422792619723187 35099035238134188929584781)
          ·
            refine ⟨13162138214300320848594293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35099035238134188929584781 13162138214300320848594293)
            ·
              refine ⟨1233950457590655079555715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13162138214300320848594293 1233950457590655079555715)
              ·
                refine ⟨1850925686385982619333573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233950457590655079555715 1850925686385982619333573)
                ·
                  refine ⟨347048566197371741125045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850925686385982619333573 347048566197371741125045)
                  ·
                    rfl

theorem cell21_1520718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_1520718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520718 prefixEnd_1520718 := by exact prefixLift 1520718
  have htrace : WordTrace (prefixWord ++ tailWord_1520718) baseStart_1520718 baseEnd_1520718 := by
    simpa [prefixWord, tailWord_1520718, baseEnd_1520718] using wordTrace_append hprefix tailTrace_1520718
  have hstable : (prefixWord ++ tailWord_1520718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520718).length < 2 ^ (prefixWord ++ tailWord_1520718).sum := by decide
  have hdescent : baseEnd_1520718 < baseStart_1520718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520729 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 7]
def baseStart_1520729 : Nat := 118140960795 + 1520729 * 2 ^ 59
def prefixEnd_1520729 : Nat := 4983230072969 + 3 ^ 40 * 1520729 * 2
def baseEnd_1520729 : Nat := 347051076547238166441689

theorem tailTrace_1520729 : CollatzResearch.WordTrace tailWord_1520729 prefixEnd_1520729 347051076547238166441689 := by
  unfold tailWord_1520729
  simp only [CollatzResearch.WordTrace]
  refine ⟨55465543307666027680957241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36977028871777351787304827 55465543307666027680957241)
  ·
    refine ⟨41599157480749520760717931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55465543307666027680957241 41599157480749520760717931)
    ·
      refine ⟨62398736221124281141076897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41599157480749520760717931 62398736221124281141076897)
      ·
        refine ⟨46799052165843210855807673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62398736221124281141076897 46799052165843210855807673)
        ·
          refine ⟨35099289124382408141855755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46799052165843210855807673 35099289124382408141855755)
          ·
            refine ⟨52648933686573612212783633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35099289124382408141855755 52648933686573612212783633)
            ·
              refine ⟨39486700264930209159587725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52648933686573612212783633 39486700264930209159587725)
              ·
                refine ⟨14807512599348828434845397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39486700264930209159587725 14807512599348828434845397)
                ·
                  refine ⟨347051076547238166441689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14807512599348828434845397 347051076547238166441689)
                  ·
                    rfl

theorem cell21_1520729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_1520729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520729 prefixEnd_1520729 := by exact prefixLift 1520729
  have htrace : WordTrace (prefixWord ++ tailWord_1520729) baseStart_1520729 baseEnd_1520729 := by
    simpa [prefixWord, tailWord_1520729, baseEnd_1520729] using wordTrace_append hprefix tailTrace_1520729
  have hstable : (prefixWord ++ tailWord_1520729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520729).length < 2 ^ (prefixWord ++ tailWord_1520729).sum := by decide
  have hdescent : baseEnd_1520729 < baseStart_1520729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520760 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_1520760 : Nat := 118140960795 + 1520760 * 2 ^ 59
def prefixEnd_1520760 : Nat := 4983230072969 + 3 ^ 40 * 1520760 * 2
def baseEnd_1520760 : Nat := 347058151169589001424959

theorem tailTrace_1520760 : CollatzResearch.WordTrace tailWord_1520760 prefixEnd_1520760 347058151169589001424959 := by
  unfold tailWord_1520760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27733336985276859987667867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36977782647035813316890489 27733336985276859987667867)
  ·
    refine ⟨41600005477915289981501801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27733336985276859987667867 41600005477915289981501801)
    ·
      refine ⟨31200004108436467486126351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41600005477915289981501801 31200004108436467486126351)
      ·
        refine ⟨46800006162654701229189527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31200004108436467486126351 46800006162654701229189527)
        ·
          refine ⟨70200009243982051843784291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46800006162654701229189527 70200009243982051843784291)
          ·
            refine ⟨105300013865973077765676437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70200009243982051843784291 105300013865973077765676437)
            ·
              refine ⟨4935938149967488020266083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105300013865973077765676437 4935938149967488020266083)
              ·
                refine ⟨7403907224951232030399125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935938149967488020266083 7403907224951232030399125)
                ·
                  refine ⟨347058151169589001424959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7403907224951232030399125 347058151169589001424959)
                  ·
                    rfl

theorem cell21_1520760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_1520760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520760 prefixEnd_1520760 := by exact prefixLift 1520760
  have htrace : WordTrace (prefixWord ++ tailWord_1520760) baseStart_1520760 baseEnd_1520760 := by
    simpa [prefixWord, tailWord_1520760, baseEnd_1520760] using wordTrace_append hprefix tailTrace_1520760
  have hstable : (prefixWord ++ tailWord_1520760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520760).length < 2 ^ (prefixWord ++ tailWord_1520760).sum := by decide
  have hdescent : baseEnd_1520760 < baseStart_1520760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520777 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 4]
def baseStart_1520777 : Nat := 118140960795 + 1520777 * 2 ^ 59
def prefixEnd_1520777 : Nat := 4983230072969 + 3 ^ 40 * 1520777 * 2
def baseEnd_1520777 : Nat := 347062030801200749641591

theorem tailTrace_1520777 : CollatzResearch.WordTrace tailWord_1520777 prefixEnd_1520777 347062030801200749641591 := by
  unfold tailWord_1520777
  simp only [CollatzResearch.WordTrace]
  refine ⟨55467294011492131878704585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36978196007661421252469723 55467294011492131878704585)
  ·
    refine ⟨41600470508619098909028439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55467294011492131878704585 41600470508619098909028439)
    ·
      refine ⟨62400705762928648363542659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41600470508619098909028439 62400705762928648363542659)
      ·
        refine ⟨93601058644392972545313989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62400705762928648363542659 93601058644392972545313989)
        ·
          refine ⟨17550198495823682352246373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93601058644392972545313989 17550198495823682352246373)
          ·
            refine ⟨3290662217966940441046195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17550198495823682352246373 3290662217966940441046195)
            ·
              refine ⟨4935993326950410661569293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290662217966940441046195 4935993326950410661569293)
              ·
                refine ⟨1850997497606403998088485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4935993326950410661569293 1850997497606403998088485)
                ·
                  refine ⟨347062030801200749641591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1850997497606403998088485 347062030801200749641591)
                  ·
                    rfl

theorem cell21_1520777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_1520777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520777 prefixEnd_1520777 := by exact prefixLift 1520777
  have htrace : WordTrace (prefixWord ++ tailWord_1520777) baseStart_1520777 baseEnd_1520777 := by
    simpa [prefixWord, tailWord_1520777, baseEnd_1520777] using wordTrace_append hprefix tailTrace_1520777
  have hstable : (prefixWord ++ tailWord_1520777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520777).length < 2 ^ (prefixWord ++ tailWord_1520777).sum := by decide
  have hdescent : baseEnd_1520777 < baseStart_1520777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520791 : List Nat := [1, 1, 3, 3, 3, 1, 2, 7]
def baseStart_1520791 : Nat := 118140960795 + 1520791 * 2 ^ 59
def prefixEnd_1520791 : Nat := 4983230072969 + 3 ^ 40 * 1520791 * 2
def baseEnd_1520791 : Nat := 115688408597313278802743

theorem tailTrace_1520791 : CollatzResearch.WordTrace tailWord_1520791 prefixEnd_1520791 115688408597313278802743 := by
  unfold tailWord_1520791
  simp only [CollatzResearch.WordTrace]
  refine ⟨55467804633441412269714227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36978536422294274846476151 55467804633441412269714227)
  ·
    refine ⟨83201706950162118404571341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55467804633441412269714227 83201706950162118404571341)
    ·
      refine ⟨31200640106310794401714253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83201706950162118404571341 31200640106310794401714253)
      ·
        refine ⟨11700240039866547900642845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31200640106310794401714253 11700240039866547900642845)
        ·
          refine ⟨4387590014949955462741067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11700240039866547900642845 4387590014949955462741067)
          ·
            refine ⟨6581385022424933194111601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387590014949955462741067 6581385022424933194111601)
            ·
              refine ⟨4936038766818699895583701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6581385022424933194111601 4936038766818699895583701)
              ·
                refine ⟨115688408597313278802743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4936038766818699895583701 115688408597313278802743)
                ·
                  rfl

theorem cell21_1520791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 7].length) (baseStart_1520791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520791 prefixEnd_1520791 := by exact prefixLift 1520791
  have htrace : WordTrace (prefixWord ++ tailWord_1520791) baseStart_1520791 baseEnd_1520791 := by
    simpa [prefixWord, tailWord_1520791, baseEnd_1520791] using wordTrace_append hprefix tailTrace_1520791
  have hstable : (prefixWord ++ tailWord_1520791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520791).length < 2 ^ (prefixWord ++ tailWord_1520791).sum := by decide
  have hdescent : baseEnd_1520791 < baseStart_1520791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520856 : List Nat := [2, 1, 2, 2, 5, 1, 2, 3, 3]
def baseStart_1520856 : Nat := 118140960795 + 1520856 * 2 ^ 59
def prefixEnd_1520856 : Nat := 4983230072969 + 3 ^ 40 * 1520856 * 2
def baseEnd_1520856 : Nat := 347080059677514167824763

theorem tailTrace_1520856 : CollatzResearch.WordTrace tailWord_1520856 prefixEnd_1520856 347080059677514167824763 := by
  unfold tailWord_1520856
  simp only [CollatzResearch.WordTrace]
  refine ⟨27735087689102964185415211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36980116918803952247220281 27735087689102964185415211)
  ·
    refine ⟨41602631533654446278122817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27735087689102964185415211 41602631533654446278122817)
    ·
      refine ⟨31201973650240834708592113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41602631533654446278122817 31201973650240834708592113)
      ·
        refine ⟨23401480237680626031444085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31201973650240834708592113 23401480237680626031444085)
        ·
          refine ⟨2193888772282558690447883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23401480237680626031444085 2193888772282558690447883)
          ·
            refine ⟨3290833158423838035671825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193888772282558690447883 3290833158423838035671825)
            ·
              refine ⟨2468124868817878526753869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3290833158423838035671825 2468124868817878526753869)
              ·
                refine ⟨925546825806704447532701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2468124868817878526753869 925546825806704447532701)
                ·
                  refine ⟨347080059677514167824763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925546825806704447532701 347080059677514167824763)
                  ·
                    rfl

theorem cell21_1520856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_1520856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520856 prefixEnd_1520856 := by exact prefixLift 1520856
  have htrace : WordTrace (prefixWord ++ tailWord_1520856) baseStart_1520856 baseEnd_1520856 := by
    simpa [prefixWord, tailWord_1520856, baseEnd_1520856] using wordTrace_append hprefix tailTrace_1520856
  have hstable : (prefixWord ++ tailWord_1520856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520856).length < 2 ^ (prefixWord ++ tailWord_1520856).sum := by decide
  have hdescent : baseEnd_1520856 < baseStart_1520856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520932 : List Nat := [2, 3, 1, 3, 1, 1, 5, 2, 3]
def baseStart_1520932 : Nat := 118140960795 + 1520932 * 2 ^ 59
def prefixEnd_1520932 : Nat := 4983230072969 + 3 ^ 40 * 1520932 * 2
def baseEnd_1520932 : Nat := 347097403912954924557941

theorem tailTrace_1520932 : CollatzResearch.WordTrace tailWord_1520932 prefixEnd_1520932 347097403912954924557941 := by
  unfold tailWord_1520932
  simp only [CollatzResearch.WordTrace]
  refine ⟨27736473662965296675298525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36981964883953728900398033 27736473662965296675298525)
  ·
    refine ⟨10401177623611986253236947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27736473662965296675298525 10401177623611986253236947)
    ·
      refine ⟨15601766435417979379855421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10401177623611986253236947 15601766435417979379855421)
      ·
        refine ⟨5850662413281742267445783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15601766435417979379855421 5850662413281742267445783)
        ·
          refine ⟨8775993619922613401168675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850662413281742267445783 8775993619922613401168675)
          ·
            refine ⟨13163990429883920101753013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8775993619922613401168675 13163990429883920101753013)
            ·
              refine ⟨1234124102801617509539345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13163990429883920101753013 1234124102801617509539345)
              ·
                refine ⟨925593077101213132154509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234124102801617509539345 925593077101213132154509)
                ·
                  refine ⟨347097403912954924557941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925593077101213132154509 347097403912954924557941)
                  ·
                    rfl

theorem cell21_1520932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_1520932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520932 prefixEnd_1520932 := by exact prefixLift 1520932
  have htrace : WordTrace (prefixWord ++ tailWord_1520932) baseStart_1520932 baseEnd_1520932 := by
    simpa [prefixWord, tailWord_1520932, baseEnd_1520932] using wordTrace_append hprefix tailTrace_1520932
  have hstable : (prefixWord ++ tailWord_1520932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520932).length < 2 ^ (prefixWord ++ tailWord_1520932).sum := by decide
  have hdescent : baseEnd_1520932 < baseStart_1520932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1520946 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1520946 : Nat := 118140960795 + 1520946 * 2 ^ 59
def prefixEnd_1520946 : Nat := 4983230072969 + 3 ^ 40 * 1520946 * 2
def baseEnd_1520946 : Nat := 347100598903694011324579

theorem tailTrace_1520946 : CollatzResearch.WordTrace tailWord_1520946 prefixEnd_1520946 347100598903694011324579 := by
  unfold tailWord_1520946
  simp only [CollatzResearch.WordTrace]
  refine ⟨13868364486969968435401673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36982305298586582494404461 13868364486969968435401673)
  ·
    refine ⟨10401273365227476326551255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13868364486969968435401673 10401273365227476326551255)
    ·
      refine ⟨15601910047841214489826883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10401273365227476326551255 15601910047841214489826883)
      ·
        refine ⟨23402865071761821734740325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15601910047841214489826883 23402865071761821734740325)
        ·
          refine ⟨4388037200955341575263811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23402865071761821734740325 4388037200955341575263811)
          ·
            refine ⟨6582055801433012362895717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388037200955341575263811 6582055801433012362895717)
            ·
              refine ⟨1234135462768689818042947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6582055801433012362895717 1234135462768689818042947)
              ·
                refine ⟨1851203194153034727064421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234135462768689818042947 1851203194153034727064421)
                ·
                  refine ⟨347100598903694011324579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851203194153034727064421 347100598903694011324579)
                  ·
                    rfl

theorem cell21_1520946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1520946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1520946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1520946 prefixEnd_1520946 := by exact prefixLift 1520946
  have htrace : WordTrace (prefixWord ++ tailWord_1520946) baseStart_1520946 baseEnd_1520946 := by
    simpa [prefixWord, tailWord_1520946, baseEnd_1520946] using wordTrace_append hprefix tailTrace_1520946
  have hstable : (prefixWord ++ tailWord_1520946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1520946).length < 2 ^ (prefixWord ++ tailWord_1520946).sum := by decide
  have hdescent : baseEnd_1520946 < baseStart_1520946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1520946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521005 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1521005 : Nat := 118140960795 + 1521005 * 2 ^ 59
def prefixEnd_1521005 : Nat := 4983230072969 + 3 ^ 40 * 1521005 * 2
def baseEnd_1521005 : Nat := 347114063507523019841125

theorem tailTrace_1521005 : CollatzResearch.WordTrace tailWord_1521005 prefixEnd_1521005 347114063507523019841125 := by
  unfold tailWord_1521005
  simp only [CollatzResearch.WordTrace]
  refine ⟨55475609854666126818004469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36983739903110751212002979 55475609854666126818004469)
  ·
    refine ⟨5200838423874949389187919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55475609854666126818004469 5200838423874949389187919)
    ·
      refine ⟨7801257635812424083781879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200838423874949389187919 7801257635812424083781879)
      ·
        refine ⟨11701886453718636125672819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7801257635812424083781879 11701886453718636125672819)
        ·
          refine ⟨17552829680577954188509229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11701886453718636125672819 17552829680577954188509229)
          ·
            refine ⟨6582311130216732820690961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17552829680577954188509229 6582311130216732820690961)
            ·
              refine ⟨4936733347662549615518221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6582311130216732820690961 4936733347662549615518221)
              ·
                refine ⟨1851275005373456105819333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4936733347662549615518221 1851275005373456105819333)
                ·
                  refine ⟨347114063507523019841125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851275005373456105819333 347114063507523019841125)
                  ·
                    rfl

theorem cell21_1521005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1521005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521005 prefixEnd_1521005 := by exact prefixLift 1521005
  have htrace : WordTrace (prefixWord ++ tailWord_1521005) baseStart_1521005 baseEnd_1521005 := by
    simpa [prefixWord, tailWord_1521005, baseEnd_1521005] using wordTrace_append hprefix tailTrace_1521005
  have hstable : (prefixWord ++ tailWord_1521005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521005).length < 2 ^ (prefixWord ++ tailWord_1521005).sum := by decide
  have hdescent : baseEnd_1521005 < baseStart_1521005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521019 : List Nat := [1, 1, 1, 1, 1, 6, 5, 5]
def baseStart_1521019 : Nat := 118140960795 + 1521019 * 2 ^ 59
def prefixEnd_1521019 : Nat := 4983230072969 + 3 ^ 40 * 1521019 * 2
def baseEnd_1521019 : Nat := 115705752832754035535921

theorem tailTrace_1521019 : CollatzResearch.WordTrace tailWord_1521019 prefixEnd_1521019 115705752832754035535921 := by
  unfold tailWord_1521019
  simp only [CollatzResearch.WordTrace]
  refine ⟨55476120476615407209014111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36984080317743604806009407 55476120476615407209014111)
  ·
    refine ⟨83214180714923110813521167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55476120476615407209014111 83214180714923110813521167)
    ·
      refine ⟨124821271072384666220281751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83214180714923110813521167 124821271072384666220281751)
      ·
        refine ⟨187231906608576999330422627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124821271072384666220281751 187231906608576999330422627)
        ·
          refine ⟨280847859912865498995633941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187231906608576999330422627 280847859912865498995633941)
          ·
            refine ⟨13164743433415570265420341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 280847859912865498995633941 13164743433415570265420341)
            ·
              refine ⟨1234194696882709712383157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13164743433415570265420341 1234194696882709712383157)
              ·
                refine ⟨115705752832754035535921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1234194696882709712383157 115705752832754035535921)
                ·
                  rfl

theorem cell21_1521019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 5].length) (baseStart_1521019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521019 prefixEnd_1521019 := by exact prefixLift 1521019
  have htrace : WordTrace (prefixWord ++ tailWord_1521019) baseStart_1521019 baseEnd_1521019 := by
    simpa [prefixWord, tailWord_1521019, baseEnd_1521019] using wordTrace_append hprefix tailTrace_1521019
  have hstable : (prefixWord ++ tailWord_1521019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521019).length < 2 ^ (prefixWord ++ tailWord_1521019).sum := by decide
  have hdescent : baseEnd_1521019 < baseStart_1521019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521050 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_1521050 : Nat := 118140960795 + 1521050 * 2 ^ 59
def prefixEnd_1521050 : Nat := 4983230072969 + 3 ^ 40 * 1521050 * 2
def baseEnd_1521050 : Nat := 347124333120612941591033

theorem tailTrace_1521050 : CollatzResearch.WordTrace tailWord_1521050 prefixEnd_1521050 347124333120612941591033 := by
  unfold tailWord_1521050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13869312784875774875848151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36984834093002066335595069 13869312784875774875848151)
  ·
    refine ⟨20803969177313662313772227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13869312784875774875848151 20803969177313662313772227)
    ·
      refine ⟨31205953765970493470658341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20803969177313662313772227 31205953765970493470658341)
      ·
        refine ⟨5851116331119467525748439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31205953765970493470658341 5851116331119467525748439)
        ·
          refine ⟨8776674496679201288622659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5851116331119467525748439 8776674496679201288622659)
          ·
            refine ⟨13165011745018801932933989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776674496679201288622659 13165011745018801932933989)
            ·
              refine ⟨2468439702191025362425123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13165011745018801932933989 2468439702191025362425123)
              ·
                refine ⟨3702659553286538043637685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468439702191025362425123 3702659553286538043637685)
                ·
                  refine ⟨347124333120612941591033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3702659553286538043637685 347124333120612941591033)
                  ·
                    rfl

theorem cell21_1521050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_1521050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521050 prefixEnd_1521050 := by exact prefixLift 1521050
  have htrace : WordTrace (prefixWord ++ tailWord_1521050) baseStart_1521050 baseEnd_1521050 := by
    simpa [prefixWord, tailWord_1521050, baseEnd_1521050] using wordTrace_append hprefix tailTrace_1521050
  have hstable : (prefixWord ++ tailWord_1521050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521050).length < 2 ^ (prefixWord ++ tailWord_1521050).sum := by decide
  have hdescent : baseEnd_1521050 < baseStart_1521050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521171 : List Nat := [1, 1, 1, 2, 1, 8, 1, 6]
def baseStart_1521171 : Nat := 118140960795 + 1521171 * 2 ^ 59
def prefixEnd_1521171 : Nat := 4983230072969 + 3 ^ 40 * 1521171 * 2
def baseEnd_1521171 : Nat := 115717315656381206691373

theorem tailTrace_1521171 : CollatzResearch.WordTrace tailWord_1521171 prefixEnd_1521171 115717315656381206691373 := by
  unfold tailWord_1521171
  simp only [CollatzResearch.WordTrace]
  refine ⟨55481664372064737168547367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36987776248043158112364911 55481664372064737168547367)
  ·
    refine ⟨83222496558097105752821051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55481664372064737168547367 83222496558097105752821051)
    ·
      refine ⟨124833744837145658629231577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83222496558097105752821051 124833744837145658629231577)
      ·
        refine ⟨93625308627859243971923683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124833744837145658629231577 93625308627859243971923683)
        ·
          refine ⟨140437962941788865957885525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93625308627859243971923683 140437962941788865957885525)
          ·
            refine ⟨1645757378224088272943971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 140437962941788865957885525 1645757378224088272943971)
            ·
              refine ⟨2468636067336132409415957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645757378224088272943971 2468636067336132409415957)
              ·
                refine ⟨115717315656381206691373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2468636067336132409415957 115717315656381206691373)
                ·
                  rfl

theorem cell21_1521171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 6].length) (baseStart_1521171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521171 prefixEnd_1521171 := by exact prefixLift 1521171
  have htrace : WordTrace (prefixWord ++ tailWord_1521171) baseStart_1521171 baseEnd_1521171 := by
    simpa [prefixWord, tailWord_1521171, baseEnd_1521171] using wordTrace_append hprefix tailTrace_1521171
  have hstable : (prefixWord ++ tailWord_1521171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521171).length < 2 ^ (prefixWord ++ tailWord_1521171).sum := by decide
  have hdescent : baseEnd_1521171 < baseStart_1521171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521185 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 7]
def baseStart_1521185 : Nat := 118140960795 + 1521185 * 2 ^ 59
def prefixEnd_1521185 : Nat := 4983230072969 + 3 ^ 40 * 1521185 * 2
def baseEnd_1521185 : Nat := 347155141959882706840757

theorem tailTrace_1521185 : CollatzResearch.WordTrace tailWord_1521185 prefixEnd_1521185 347155141959882706840757 := by
  unfold tailWord_1521185
  simp only [CollatzResearch.WordTrace]
  refine ⟨55482174994014017559557009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36988116662676011706371339 55482174994014017559557009)
  ·
    refine ⟨41611631245510513169667757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55482174994014017559557009 41611631245510513169667757)
    ·
      refine ⟨15604361717066442438625409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41611631245510513169667757 15604361717066442438625409)
      ·
        refine ⟨11703271287799831828969057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15604361717066442438625409 11703271287799831828969057)
        ·
          refine ⟨8777453465849873871726793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11703271287799831828969057 8777453465849873871726793)
          ·
            refine ⟨6583090099387405403795095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8777453465849873871726793 6583090099387405403795095)
            ·
              refine ⟨9874635149081108105692643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6583090099387405403795095 9874635149081108105692643)
              ·
                refine ⟨14811952723621662158538965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9874635149081108105692643 14811952723621662158538965)
                ·
                  refine ⟨347155141959882706840757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14811952723621662158538965 347155141959882706840757)
                  ·
                    rfl

theorem cell21_1521185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_1521185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521185 prefixEnd_1521185 := by exact prefixLift 1521185
  have htrace : WordTrace (prefixWord ++ tailWord_1521185) baseStart_1521185 baseEnd_1521185 := by
    simpa [prefixWord, tailWord_1521185, baseEnd_1521185] using wordTrace_append hprefix tailTrace_1521185
  have hstable : (prefixWord ++ tailWord_1521185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521185).length < 2 ^ (prefixWord ++ tailWord_1521185).sum := by decide
  have hdescent : baseEnd_1521185 < baseStart_1521185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521230 : List Nat := [4, 1, 1, 1, 1, 2, 1, 10]
def baseStart_1521230 : Nat := 118140960795 + 1521230 * 2 ^ 59
def prefixEnd_1521230 : Nat := 4983230072969 + 3 ^ 40 * 1521230 * 2
def baseEnd_1521230 : Nat := 115721803857657542863555

theorem tailTrace_1521230 : CollatzResearch.WordTrace tailWord_1521230 prefixEnd_1521230 115721803857657542863555 := by
  unfold tailWord_1521230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6935477034856373780618143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36989210852567326829963429 6935477034856373780618143)
  ·
    refine ⟨10403215552284560670927215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6935477034856373780618143 10403215552284560670927215)
    ·
      refine ⟨15604823328426841006390823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10403215552284560670927215 15604823328426841006390823)
      ·
        refine ⟨23407234992640261509586235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15604823328426841006390823 23407234992640261509586235)
        ·
          refine ⟨35110852488960392264379353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23407234992640261509586235 35110852488960392264379353)
          ·
            refine ⟨26333139366720294198284515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35110852488960392264379353 26333139366720294198284515)
            ·
              refine ⟨39499709050080441297426773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26333139366720294198284515 39499709050080441297426773)
              ·
                refine ⟨115721803857657542863555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39499709050080441297426773 115721803857657542863555)
                ·
                  rfl

theorem cell21_1521230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_1521230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521230 prefixEnd_1521230 := by exact prefixLift 1521230
  have htrace : WordTrace (prefixWord ++ tailWord_1521230) baseStart_1521230 baseEnd_1521230 := by
    simpa [prefixWord, tailWord_1521230, baseEnd_1521230] using wordTrace_append hprefix tailTrace_1521230
  have hstable : (prefixWord ++ tailWord_1521230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521230).length < 2 ^ (prefixWord ++ tailWord_1521230).sum := by decide
  have hdescent : baseEnd_1521230 < baseStart_1521230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521233 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 4]
def baseStart_1521233 : Nat := 118140960795 + 1521233 * 2 ^ 59
def prefixEnd_1521233 : Nat := 4983230072969 + 3 ^ 40 * 1521233 * 2
def baseEnd_1521233 : Nat := 347166096213845290040659

theorem tailTrace_1521233 : CollatzResearch.WordTrace tailWord_1521233 prefixEnd_1521233 347166096213845290040659 := by
  unfold tailWord_1521233
  simp only [CollatzResearch.WordTrace]
  refine ⟨55483925697840121757304353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36989283798560081171536235 55483925697840121757304353)
  ·
    refine ⟨41612944273380091317978265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55483925697840121757304353 41612944273380091317978265)
    ·
      refine ⟨31209708205035068488483699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41612944273380091317978265 31209708205035068488483699)
      ·
        refine ⟨46814562307552602732725549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31209708205035068488483699 46814562307552602732725549)
        ·
          refine ⟨17555460865332226024772081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46814562307552602732725549 17555460865332226024772081)
          ·
            refine ⟨13166595648999169518579061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17555460865332226024772081 13166595648999169518579061)
            ·
              refine ⟨1234368342093672142366787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13166595648999169518579061 1234368342093672142366787)
              ·
                refine ⟨1851552513140508213550181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234368342093672142366787 1851552513140508213550181)
                ·
                  refine ⟨347166096213845290040659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851552513140508213550181 347166096213845290040659)
                  ·
                    rfl

theorem cell21_1521233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_1521233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521233 prefixEnd_1521233 := by exact prefixLift 1521233
  have htrace : WordTrace (prefixWord ++ tailWord_1521233) baseStart_1521233 baseEnd_1521233 := by
    simpa [prefixWord, tailWord_1521233, baseEnd_1521233] using wordTrace_append hprefix tailTrace_1521233
  have hstable : (prefixWord ++ tailWord_1521233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521233).length < 2 ^ (prefixWord ++ tailWord_1521233).sum := by decide
  have hdescent : baseEnd_1521233 < baseStart_1521233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521275 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 6]
def baseStart_1521275 : Nat := 118140960795 + 1521275 * 2 ^ 59
def prefixEnd_1521275 : Nat := 4983230072969 + 3 ^ 40 * 1521275 * 2
def baseEnd_1521275 : Nat := 347175681186062550340573

theorem tailTrace_1521275 : CollatzResearch.WordTrace tailWord_1521275 prefixEnd_1521275 347175681186062550340573 := by
  unfold tailWord_1521275
  simp only [CollatzResearch.WordTrace]
  refine ⟨55485457563687962930333279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36990305042458641953555519 55485457563687962930333279)
  ·
    refine ⟨83228186345531944395499919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55485457563687962930333279 83228186345531944395499919)
    ·
      refine ⟨124842279518297916593249879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83228186345531944395499919 124842279518297916593249879)
      ·
        refine ⟨187263419277446874889874819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124842279518297916593249879 187263419277446874889874819)
        ·
          refine ⟨280895128916170312334812229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187263419277446874889874819 280895128916170312334812229)
          ·
            refine ⟨52667836671781933562777293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280895128916170312334812229 52667836671781933562777293)
            ·
              refine ⟨19750438751918225086041485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52667836671781933562777293 19750438751918225086041485)
              ·
                refine ⟨7406414531969334407265557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19750438751918225086041485 7406414531969334407265557)
                ·
                  refine ⟨347175681186062550340573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7406414531969334407265557 347175681186062550340573)
                  ·
                    rfl

theorem cell21_1521275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_1521275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521275 prefixEnd_1521275 := by exact prefixLift 1521275
  have htrace : WordTrace (prefixWord ++ tailWord_1521275) baseStart_1521275 baseEnd_1521275 := by
    simpa [prefixWord, tailWord_1521275, baseEnd_1521275] using wordTrace_append hprefix tailTrace_1521275
  have hstable : (prefixWord ++ tailWord_1521275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521275).length < 2 ^ (prefixWord ++ tailWord_1521275).sum := by decide
  have hdescent : baseEnd_1521275 < baseStart_1521275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521292 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_1521292 : Nat := 118140960795 + 1521292 * 2 ^ 59
def prefixEnd_1521292 : Nat := 4983230072969 + 3 ^ 40 * 1521292 * 2
def baseEnd_1521292 : Nat := 347179560817674298557205

theorem tailTrace_1521292 : CollatzResearch.WordTrace tailWord_1521292 prefixEnd_1521292 347179560817674298557205 := by
  unfold tailWord_1521292
  simp only [CollatzResearch.WordTrace]
  refine ⟨27743038802313187416851065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36990718403084249889134753 27743038802313187416851065)
  ·
    refine ⟨20807279101734890562638299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27743038802313187416851065 20807279101734890562638299)
    ·
      refine ⟨31210918652602335843957449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20807279101734890562638299 31210918652602335843957449)
      ·
        refine ⟨23408188989451751882968087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31210918652602335843957449 23408188989451751882968087)
        ·
          refine ⟨35112283484177627824452131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23408188989451751882968087 35112283484177627824452131)
          ·
            refine ⟨52668425226266441736678197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35112283484177627824452131 52668425226266441736678197)
            ·
              refine ⟨4937664864962478912813581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52668425226266441736678197 4937664864962478912813581)
              ·
                refine ⟨1851624324360929592305093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4937664864962478912813581 1851624324360929592305093)
                ·
                  refine ⟨347179560817674298557205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851624324360929592305093 347179560817674298557205)
                  ·
                    rfl

theorem cell21_1521292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_1521292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521292 prefixEnd_1521292 := by exact prefixLift 1521292
  have htrace : WordTrace (prefixWord ++ tailWord_1521292) baseStart_1521292 baseEnd_1521292 := by
    simpa [prefixWord, tailWord_1521292, baseEnd_1521292] using wordTrace_append hprefix tailTrace_1521292
  have hstable : (prefixWord ++ tailWord_1521292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521292).length < 2 ^ (prefixWord ++ tailWord_1521292).sum := by decide
  have hdescent : baseEnd_1521292 < baseStart_1521292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521354 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_1521354 : Nat := 118140960795 + 1521354 * 2 ^ 59
def prefixEnd_1521354 : Nat := 4983230072969 + 3 ^ 40 * 1521354 * 2
def baseEnd_1521354 : Nat := 347193710062375968523745

theorem tailTrace_1521354 : CollatzResearch.WordTrace tailWord_1521354 prefixEnd_1521354 347193710062375968523745 := by
  unfold tailWord_1521354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13872084732600439855614779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36992225953601172948306077 13872084732600439855614779)
  ·
    refine ⟨20808127098900659783422169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13872084732600439855614779 20808127098900659783422169)
    ·
      refine ⟨15606095324175494837566627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20808127098900659783422169 15606095324175494837566627)
      ·
        refine ⟨23409142986263242256349941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15606095324175494837566627 23409142986263242256349941)
        ·
          refine ⟨2194607154962178961532807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23409142986263242256349941 2194607154962178961532807)
          ·
            refine ⟨3291910732443268442299211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194607154962178961532807 3291910732443268442299211)
            ·
              refine ⟨4937866098664902663448817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291910732443268442299211 4937866098664902663448817)
              ·
                refine ⟨3703399573998676997586613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937866098664902663448817 3703399573998676997586613)
                ·
                  refine ⟨347193710062375968523745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3703399573998676997586613 347193710062375968523745)
                  ·
                    rfl

theorem cell21_1521354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_1521354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521354 prefixEnd_1521354 := by exact prefixLift 1521354
  have htrace : WordTrace (prefixWord ++ tailWord_1521354) baseStart_1521354 baseEnd_1521354 := by
    simpa [prefixWord, tailWord_1521354, baseEnd_1521354] using wordTrace_append hprefix tailTrace_1521354
  have hstable : (prefixWord ++ tailWord_1521354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521354).length < 2 ^ (prefixWord ++ tailWord_1521354).sum := by decide
  have hdescent : baseEnd_1521354 < baseStart_1521354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521357 : List Nat := [1, 6, 2, 1, 1, 2, 3, 5]
def baseStart_1521357 : Nat := 118140960795 + 1521357 * 2 ^ 59
def prefixEnd_1521357 : Nat := 4983230072969 + 3 ^ 40 * 1521357 * 2
def baseEnd_1521357 : Nat := 115731464901082876657913

theorem tailTrace_1521357 : CollatzResearch.WordTrace tailWord_1521357 prefixEnd_1521357 115731464901082876657913 := by
  unfold tailWord_1521357
  simp only [CollatzResearch.WordTrace]
  refine ⟨55488448349390890934818325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36992298899593927289878883 55488448349390890934818325)
  ·
    refine ⟨2601021016377698012569609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55488448349390890934818325 2601021016377698012569609)
    ·
      refine ⟨1950765762283273509427207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2601021016377698012569609 1950765762283273509427207)
      ·
        refine ⟨2926148643424910264140811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950765762283273509427207 2926148643424910264140811)
        ·
          refine ⟨4389222965137365396211217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926148643424910264140811 4389222965137365396211217)
          ·
            refine ⟨3291917223853024047158413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4389222965137365396211217 3291917223853024047158413)
            ·
              refine ⟨1234468958944884017684405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3291917223853024047158413 1234468958944884017684405)
              ·
                refine ⟨115731464901082876657913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1234468958944884017684405 115731464901082876657913)
                ·
                  rfl

theorem cell21_1521357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 5].length) (baseStart_1521357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521357 prefixEnd_1521357 := by exact prefixLift 1521357
  have htrace : WordTrace (prefixWord ++ tailWord_1521357) baseStart_1521357 baseEnd_1521357 := by
    simpa [prefixWord, tailWord_1521357, baseEnd_1521357] using wordTrace_append hprefix tailTrace_1521357
  have hstable : (prefixWord ++ tailWord_1521357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521357).length < 2 ^ (prefixWord ++ tailWord_1521357).sum := by decide
  have hdescent : baseEnd_1521357 < baseStart_1521357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521444 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1521444 : Nat := 118140960795 + 1521444 * 2 ^ 59
def prefixEnd_1521444 : Nat := 4983230072969 + 3 ^ 40 * 1521444 * 2
def baseEnd_1521444 : Nat := 347214249288555812023561

theorem tailTrace_1521444 : CollatzResearch.WordTrace tailWord_1521444 prefixEnd_1521444 347214249288555812023561 := by
  unfold tailWord_1521444
  simp only [CollatzResearch.WordTrace]
  refine ⟨27745810750037852396617693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36994414333383803195490257 27745810750037852396617693)
  ·
    refine ⟨10404679031264194648731635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27745810750037852396617693 10404679031264194648731635)
    ·
      refine ⟨15607018546896291973097453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10404679031264194648731635 15607018546896291973097453)
      ·
        refine ⟨5852631955086109489911545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15607018546896291973097453 5852631955086109489911545)
        ·
          refine ⟨4389473966314582117433659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5852631955086109489911545 4389473966314582117433659)
          ·
            refine ⟨6584210949471873176150489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389473966314582117433659 6584210949471873176150489)
            ·
              refine ⟨4938158212103904882112867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6584210949471873176150489 4938158212103904882112867)
              ·
                refine ⟨7407237318155857323169301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938158212103904882112867 7407237318155857323169301)
                ·
                  refine ⟨347214249288555812023561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7407237318155857323169301 347214249288555812023561)
                  ·
                    rfl

theorem cell21_1521444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1521444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521444 prefixEnd_1521444 := by exact prefixLift 1521444
  have htrace : WordTrace (prefixWord ++ tailWord_1521444) baseStart_1521444 baseEnd_1521444 := by
    simpa [prefixWord, tailWord_1521444, baseEnd_1521444] using wordTrace_append hprefix tailTrace_1521444
  have hstable : (prefixWord ++ tailWord_1521444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521444).length < 2 ^ (prefixWord ++ tailWord_1521444).sum := by decide
  have hdescent : baseEnd_1521444 < baseStart_1521444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521458 : List Nat := [3, 2, 1, 1, 3, 2, 1, 8]
def baseStart_1521458 : Nat := 118140960795 + 1521458 * 2 ^ 59
def prefixEnd_1521458 : Nat := 4983230072969 + 3 ^ 40 * 1521458 * 2
def baseEnd_1521458 : Nat := 115739148093098299596733

theorem tailTrace_1521458 : CollatzResearch.WordTrace tailWord_1521458 prefixEnd_1521458 115739148093098299596733 := by
  unfold tailWord_1521458
  simp only [CollatzResearch.WordTrace]
  refine ⟨13873033030506246296061257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36994754748016656789496685 13873033030506246296061257)
  ·
    refine ⟨10404774772879684722045943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13873033030506246296061257 10404774772879684722045943)
    ·
      refine ⟨15607162159319527083068915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10404774772879684722045943 15607162159319527083068915)
      ·
        refine ⟨23410743238979290624603373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15607162159319527083068915 23410743238979290624603373)
        ·
          refine ⟨8779028714617233984226265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23410743238979290624603373 8779028714617233984226265)
          ·
            refine ⟨6584271535962925488169699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8779028714617233984226265 6584271535962925488169699)
            ·
              refine ⟨9876407303944388232254549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6584271535962925488169699 9876407303944388232254549)
              ·
                refine ⟨115739148093098299596733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9876407303944388232254549 115739148093098299596733)
                ·
                  rfl

theorem cell21_1521458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_1521458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521458 prefixEnd_1521458 := by exact prefixLift 1521458
  have htrace : WordTrace (prefixWord ++ tailWord_1521458) baseStart_1521458 baseEnd_1521458 := by
    simpa [prefixWord, tailWord_1521458, baseEnd_1521458] using wordTrace_append hprefix tailTrace_1521458
  have hstable : (prefixWord ++ tailWord_1521458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521458).length < 2 ^ (prefixWord ++ tailWord_1521458).sum := by decide
  have hdescent : baseEnd_1521458 < baseStart_1521458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521461 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 4]
def baseStart_1521461 : Nat := 118140960795 + 1521461 * 2 ^ 59
def prefixEnd_1521461 : Nat := 4983230072969 + 3 ^ 40 * 1521461 * 2
def baseEnd_1521461 : Nat := 347218128920167560240193

theorem tailTrace_1521461 : CollatzResearch.WordTrace tailWord_1521461 prefixEnd_1521461 347218128920167560240193 := by
  unfold tailWord_1521461
  simp only [CollatzResearch.WordTrace]
  refine ⟨55492241541014116696604237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36994827694009411131069491 55492241541014116696604237)
  ·
    refine ⟨20809590577880293761226589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55492241541014116696604237 20809590577880293761226589)
    ·
      refine ⟨7803596466705110160459971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20809590577880293761226589 7803596466705110160459971)
      ·
        refine ⟨11705394700057665240689957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7803596466705110160459971 11705394700057665240689957)
        ·
          refine ⟨2194761506260812232629367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11705394700057665240689957 2194761506260812232629367)
          ·
            refine ⟨3292142259391218348944051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194761506260812232629367 3292142259391218348944051)
            ·
              refine ⟨4938213389086827523416077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292142259391218348944051 4938213389086827523416077)
              ·
                refine ⟨1851830020907560321281029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4938213389086827523416077 1851830020907560321281029)
                ·
                  refine ⟨347218128920167560240193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851830020907560321281029 347218128920167560240193)
                  ·
                    rfl

theorem cell21_1521461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_1521461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521461 prefixEnd_1521461 := by exact prefixLift 1521461
  have htrace : WordTrace (prefixWord ++ tailWord_1521461) baseStart_1521461 baseEnd_1521461 := by
    simpa [prefixWord, tailWord_1521461, baseEnd_1521461] using wordTrace_append hprefix tailTrace_1521461
  have hstable : (prefixWord ++ tailWord_1521461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521461).length < 2 ^ (prefixWord ++ tailWord_1521461).sum := by decide
  have hdescent : baseEnd_1521461 < baseStart_1521461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521548 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_1521548 : Nat := 118140960795 + 1521548 * 2 ^ 59
def prefixEnd_1521548 : Nat := 4983230072969 + 3 ^ 40 * 1521548 * 2
def baseEnd_1521548 : Nat := 347237983505474742290015

theorem tailTrace_1521548 : CollatzResearch.WordTrace tailWord_1521548 prefixEnd_1521548 347237983505474742290015 := by
  unfold tailWord_1521548
  simp only [CollatzResearch.WordTrace]
  refine ⟨27747707345849465277510649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36996943127799287036680865 27747707345849465277510649)
  ·
    refine ⟨20810780509387098958132987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27747707345849465277510649 20810780509387098958132987)
    ·
      refine ⟨31216170764080648437199481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20810780509387098958132987 31216170764080648437199481)
      ·
        refine ⟨23412128073060486327899611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31216170764080648437199481 23412128073060486327899611)
        ·
          refine ⟨35118192109590729491849417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23412128073060486327899611 35118192109590729491849417)
          ·
            refine ⟨26338644082193047118887063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35118192109590729491849417 26338644082193047118887063)
            ·
              refine ⟨39507966123289570678330595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26338644082193047118887063 39507966123289570678330595)
              ·
                refine ⟨59261949184934356017495893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39507966123289570678330595 59261949184934356017495893)
                ·
                  refine ⟨347237983505474742290015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59261949184934356017495893 347237983505474742290015)
                  ·
                    rfl

theorem cell21_1521548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_1521548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521548 prefixEnd_1521548 := by exact prefixLift 1521548
  have htrace : WordTrace (prefixWord ++ tailWord_1521548) baseStart_1521548 baseEnd_1521548 := by
    simpa [prefixWord, tailWord_1521548, baseEnd_1521548] using wordTrace_append hprefix tailTrace_1521548
  have hstable : (prefixWord ++ tailWord_1521548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521548).length < 2 ^ (prefixWord ++ tailWord_1521548).sum := by decide
  have hdescent : baseEnd_1521548 < baseStart_1521548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521554 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_1521554 : Nat := 118140960795 + 1521554 * 2 ^ 59
def prefixEnd_1521554 : Nat := 4983230072969 + 3 ^ 40 * 1521554 * 2
def baseEnd_1521554 : Nat := 347239352787220065190003

theorem tailTrace_1521554 : CollatzResearch.WordTrace tailWord_1521554 prefixEnd_1521554 347239352787220065190003 := by
  unfold tailWord_1521554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13873908382419298394934929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36997089019784795719826477 13873908382419298394934929)
  ·
    refine ⟨10405431286814473796201197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13873908382419298394934929 10405431286814473796201197)
    ·
      refine ⟨3902036732555427673575449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10405431286814473796201197 3902036732555427673575449)
      ·
        refine ⟨2926527549416570755181587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3902036732555427673575449 2926527549416570755181587)
        ·
          refine ⟨4389791324124856132772381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926527549416570755181587 4389791324124856132772381)
          ·
            refine ⟨1646171746546821049789643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4389791324124856132772381 1646171746546821049789643)
            ·
              refine ⟨2469257619820231574684465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646171746546821049789643 2469257619820231574684465)
              ·
                refine ⟨1851943214865173681013349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469257619820231574684465 1851943214865173681013349)
                ·
                  refine ⟨347239352787220065190003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851943214865173681013349 347239352787220065190003)
                  ·
                    rfl

theorem cell21_1521554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_1521554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521554 prefixEnd_1521554 := by exact prefixLift 1521554
  have htrace : WordTrace (prefixWord ++ tailWord_1521554) baseStart_1521554 baseEnd_1521554 := by
    simpa [prefixWord, tailWord_1521554, baseEnd_1521554] using wordTrace_append hprefix tailTrace_1521554
  have hstable : (prefixWord ++ tailWord_1521554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521554).length < 2 ^ (prefixWord ++ tailWord_1521554).sum := by decide
  have hdescent : baseEnd_1521554 < baseStart_1521554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521565 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 5]
def baseStart_1521565 : Nat := 118140960795 + 1521565 * 2 ^ 59
def prefixEnd_1521565 : Nat := 4983230072969 + 3 ^ 40 * 1521565 * 2
def baseEnd_1521565 : Nat := 347241863137086490506647

theorem tailTrace_1521565 : CollatzResearch.WordTrace tailWord_1521565 prefixEnd_1521565 347241863137086490506647 := by
  unfold tailWord_1521565
  simp only [CollatzResearch.WordTrace]
  refine ⟨55496034732637342458390149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36997356488424894972260099 55496034732637342458390149)
  ·
    refine ⟨10405506512369501710948153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55496034732637342458390149 10405506512369501710948153)
    ·
      refine ⟨7804129884277126283211115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10405506512369501710948153 7804129884277126283211115)
      ·
        refine ⟨11706194826415689424816673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7804129884277126283211115 11706194826415689424816673)
        ·
          refine ⟨8779646119811767068612505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11706194826415689424816673 8779646119811767068612505)
          ·
            refine ⟨6584734589858825301459379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8779646119811767068612505 6584734589858825301459379)
            ·
              refine ⟨9877101884788237952189069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6584734589858825301459379 9877101884788237952189069)
              ·
                refine ⟨3703913206795589232070901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9877101884788237952189069 3703913206795589232070901)
                ·
                  refine ⟨347241863137086490506647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3703913206795589232070901 347241863137086490506647)
                  ·
                    rfl

theorem cell21_1521565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_1521565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521565 prefixEnd_1521565 := by exact prefixLift 1521565
  have htrace : WordTrace (prefixWord ++ tailWord_1521565) baseStart_1521565 baseEnd_1521565 := by
    simpa [prefixWord, tailWord_1521565, baseEnd_1521565] using wordTrace_append hprefix tailTrace_1521565
  have hstable : (prefixWord ++ tailWord_1521565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521565).length < 2 ^ (prefixWord ++ tailWord_1521565).sum := by decide
  have hdescent : baseEnd_1521565 < baseStart_1521565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521669 : List Nat := [1, 3, 1, 1, 2, 13]
def baseStart_1521669 : Nat := 118140960795 + 1521669 * 2 ^ 59
def prefixEnd_1521669 : Nat := 4983230072969 + 3 ^ 40 * 1521669 * 2
def baseEnd_1521669 : Nat := 12861688790889089658263

theorem tailTrace_1521669 : CollatzResearch.WordTrace tailWord_1521669 prefixEnd_1521669 12861688790889089658263 := by
  unfold tailWord_1521669
  simp only [CollatzResearch.WordTrace]
  refine ⟨55499827924260568220176061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36999885282840378813450707 55499827924260568220176061)
  ·
    refine ⟨20812435471597713082566023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55499827924260568220176061 20812435471597713082566023)
    ·
      refine ⟨31218653207396569623849035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20812435471597713082566023 31218653207396569623849035)
      ·
        refine ⟨46827979811094854435773553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31218653207396569623849035 46827979811094854435773553)
        ·
          refine ⟨35120984858321140826830165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46827979811094854435773553 35120984858321140826830165)
          ·
            refine ⟨12861688790889089658263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 35120984858321140826830165 12861688790889089658263)
            ·
              rfl

theorem cell21_1521669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 13].length) (baseStart_1521669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521669 prefixEnd_1521669 := by exact prefixLift 1521669
  have htrace : WordTrace (prefixWord ++ tailWord_1521669) baseStart_1521669 baseEnd_1521669 := by
    simpa [prefixWord, tailWord_1521669, baseEnd_1521669] using wordTrace_append hprefix tailTrace_1521669
  have hstable : (prefixWord ++ tailWord_1521669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521669).length < 2 ^ (prefixWord ++ tailWord_1521669).sum := by decide
  have hdescent : baseEnd_1521669 < baseStart_1521669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521672 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_1521672 : Nat := 118140960795 + 1521672 * 2 ^ 59
def prefixEnd_1521672 : Nat := 4983230072969 + 3 ^ 40 * 1521672 * 2
def baseEnd_1521672 : Nat := 347266281994878082223095

theorem tailTrace_1521672 : CollatzResearch.WordTrace tailWord_1521672 prefixEnd_1521672 347266281994878082223095 := by
  unfold tailWord_1521672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27749968671624849866267635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36999958228833133155023513 27749968671624849866267635)
  ·
    refine ⟨41624953007437274799401453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27749968671624849866267635 41624953007437274799401453)
    ·
      refine ⟨15609357377788978049775545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41624953007437274799401453 15609357377788978049775545)
      ·
        refine ⟨11707018033341733537331659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15609357377788978049775545 11707018033341733537331659)
        ·
          refine ⟨17560527050012600305997489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11707018033341733537331659 17560527050012600305997489)
          ·
            refine ⟨13170395287509450229498117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17560527050012600305997489 13170395287509450229498117)
            ·
              refine ⟨2469449116408021918030897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13170395287509450229498117 2469449116408021918030897)
              ·
                refine ⟨1852086837306016438523173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469449116408021918030897 1852086837306016438523173)
                ·
                  refine ⟨347266281994878082223095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852086837306016438523173 347266281994878082223095)
                  ·
                    rfl

theorem cell21_1521672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_1521672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521672 prefixEnd_1521672 := by exact prefixLift 1521672
  have htrace : WordTrace (prefixWord ++ tailWord_1521672) baseStart_1521672 baseEnd_1521672 := by
    simpa [prefixWord, tailWord_1521672, baseEnd_1521672] using wordTrace_append hprefix tailTrace_1521672
  have hstable : (prefixWord ++ tailWord_1521672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521672).length < 2 ^ (prefixWord ++ tailWord_1521672).sum := by decide
  have hdescent : baseEnd_1521672 < baseStart_1521672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521731 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 4]
def baseStart_1521731 : Nat := 118140960795 + 1521731 * 2 ^ 59
def prefixEnd_1521731 : Nat := 4983230072969 + 3 ^ 40 * 1521731 * 2
def baseEnd_1521731 : Nat := 347279746598707090739641

theorem tailTrace_1521731 : CollatzResearch.WordTrace tailWord_1521731 prefixEnd_1521731 347279746598707090739641 := by
  unfold tailWord_1521731
  simp only [CollatzResearch.WordTrace]
  refine ⟨55502089250035952808933047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37001392833357301872622031 55502089250035952808933047)
  ·
    refine ⟨83253133875053929213399571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55502089250035952808933047 83253133875053929213399571)
    ·
      refine ⟨124879700812580893820099357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83253133875053929213399571 124879700812580893820099357)
      ·
        refine ⟨46829887804717835182537259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124879700812580893820099357 46829887804717835182537259)
        ·
          refine ⟨70244831707076752773805889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46829887804717835182537259 70244831707076752773805889)
          ·
            refine ⟨52683623780307564580354417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70244831707076752773805889 52683623780307564580354417)
            ·
              refine ⟨39512717835230673435265813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52683623780307564580354417 39512717835230673435265813)
              ·
                refine ⟨1852158648526437817278085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39512717835230673435265813 1852158648526437817278085)
                ·
                  refine ⟨347279746598707090739641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852158648526437817278085 347279746598707090739641)
                  ·
                    rfl

theorem cell21_1521731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 4].length) (baseStart_1521731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521731 prefixEnd_1521731 := by exact prefixLift 1521731
  have htrace : WordTrace (prefixWord ++ tailWord_1521731) baseStart_1521731 baseEnd_1521731 := by
    simpa [prefixWord, tailWord_1521731, baseEnd_1521731] using wordTrace_append hprefix tailTrace_1521731
  have hstable : (prefixWord ++ tailWord_1521731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521731).length < 2 ^ (prefixWord ++ tailWord_1521731).sum := by decide
  have hdescent : baseEnd_1521731 < baseStart_1521731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521745 : List Nat := [1, 2, 2, 1, 3, 1, 1, 10]
def baseStart_1521745 : Nat := 118140960795 + 1521745 * 2 ^ 59
def prefixEnd_1521745 : Nat := 4983230072969 + 3 ^ 40 * 1521745 * 2
def baseEnd_1521745 : Nat := 115760980529815392502093

theorem tailTrace_1521745 : CollatzResearch.WordTrace tailWord_1521745 prefixEnd_1521745 115760980529815392502093 := by
  unfold tailWord_1521745
  simp only [CollatzResearch.WordTrace]
  refine ⟨55502599871985233199942689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37001733247990155466628459 55502599871985233199942689)
  ·
    refine ⟨41626949903988924899957017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55502599871985233199942689 41626949903988924899957017)
    ·
      refine ⟨31220212427991693674967763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41626949903988924899957017 31220212427991693674967763)
      ·
        refine ⟨46830318641987540512451645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31220212427991693674967763 46830318641987540512451645)
        ·
          refine ⟨17561369490745327692169367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46830318641987540512451645 17561369490745327692169367)
          ·
            refine ⟨26342054236117991538254051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17561369490745327692169367 26342054236117991538254051)
            ·
              refine ⟨39513081354176987307381077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26342054236117991538254051 39513081354176987307381077)
              ·
                refine ⟨115760980529815392502093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39513081354176987307381077 115760980529815392502093)
                ·
                  rfl

theorem cell21_1521745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 10].length) (baseStart_1521745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521745 prefixEnd_1521745 := by exact prefixLift 1521745
  have htrace : WordTrace (prefixWord ++ tailWord_1521745) baseStart_1521745 baseEnd_1521745 := by
    simpa [prefixWord, tailWord_1521745, baseEnd_1521745] using wordTrace_append hprefix tailTrace_1521745
  have hstable : (prefixWord ++ tailWord_1521745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521745).length < 2 ^ (prefixWord ++ tailWord_1521745).sum := by decide
  have hdescent : baseEnd_1521745 < baseStart_1521745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521841 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 4]
def baseStart_1521841 : Nat := 118140960795 + 1521841 * 2 ^ 59
def prefixEnd_1521841 : Nat := 4983230072969 + 3 ^ 40 * 1521841 * 2
def baseEnd_1521841 : Nat := 347304850097371343906083

theorem tailTrace_1521841 : CollatzResearch.WordTrace tailWord_1521841 prefixEnd_1521841 347304850097371343906083 := by
  unfold tailWord_1521841
  simp only [CollatzResearch.WordTrace]
  refine ⟨55506101279637441595437377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37004067519758294396958251 55506101279637441595437377)
  ·
    refine ⟨41629575959728081196578033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55506101279637441595437377 41629575959728081196578033)
    ·
      refine ⟨31222181969796060897433525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41629575959728081196578033 31222181969796060897433525)
      ·
        refine ⟨2927079559668380709134393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31222181969796060897433525 2927079559668380709134393)
        ·
          refine ⟨2195309669751285531850795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2927079559668380709134393 2195309669751285531850795)
          ·
            refine ⟨3292964504626928297776193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195309669751285531850795 3292964504626928297776193)
            ·
              refine ⟨2469723378470196223332145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292964504626928297776193 2469723378470196223332145)
              ·
                refine ⟨1852292533852647167499109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469723378470196223332145 1852292533852647167499109)
                ·
                  refine ⟨347304850097371343906083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852292533852647167499109 347304850097371343906083)
                  ·
                    rfl

theorem cell21_1521841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_1521841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521841 prefixEnd_1521841 := by exact prefixLift 1521841
  have htrace : WordTrace (prefixWord ++ tailWord_1521841) baseStart_1521841 baseEnd_1521841 := by
    simpa [prefixWord, tailWord_1521841, baseEnd_1521841] using wordTrace_append hprefix tailTrace_1521841
  have hstable : (prefixWord ++ tailWord_1521841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521841).length < 2 ^ (prefixWord ++ tailWord_1521841).sum := by decide
  have hdescent : baseEnd_1521841 < baseStart_1521841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521858 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1521858 : Nat := 118140960795 + 1521858 * 2 ^ 59
def prefixEnd_1521858 : Nat := 4983230072969 + 3 ^ 40 * 1521858 * 2
def baseEnd_1521858 : Nat := 347308729728983092122715

theorem tailTrace_1521858 : CollatzResearch.WordTrace tailWord_1521858 prefixEnd_1521858 347308729728983092122715 := by
  unfold tailWord_1521858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876680330143963374701557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37004480880383902332537485 13876680330143963374701557)
  ·
    refine ⟨1300938780950996566378271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13876680330143963374701557 1300938780950996566378271)
    ·
      refine ⟨1951408171426494849567407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300938780950996566378271 1951408171426494849567407)
      ·
        refine ⟨2927112257139742274351111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951408171426494849567407 2927112257139742274351111)
        ·
          refine ⟨4390668385709613411526667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927112257139742274351111 4390668385709613411526667)
          ·
            refine ⟨6586002578564420117290001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390668385709613411526667 6586002578564420117290001)
            ·
              refine ⟨4939501933923315087967501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6586002578564420117290001 4939501933923315087967501)
              ·
                refine ⟨1852313225221243157987813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4939501933923315087967501 1852313225221243157987813)
                ·
                  refine ⟨347308729728983092122715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852313225221243157987813 347308729728983092122715)
                  ·
                    rfl

theorem cell21_1521858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1521858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521858 prefixEnd_1521858 := by exact prefixLift 1521858
  have htrace : WordTrace (prefixWord ++ tailWord_1521858) baseStart_1521858 baseEnd_1521858 := by
    simpa [prefixWord, tailWord_1521858, baseEnd_1521858] using wordTrace_append hprefix tailTrace_1521858
  have hstable : (prefixWord ++ tailWord_1521858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521858).length < 2 ^ (prefixWord ++ tailWord_1521858).sum := by decide
  have hdescent : baseEnd_1521858 < baseStart_1521858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1521976 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_1521976 : Nat := 118140960795 + 1521976 * 2 ^ 59
def prefixEnd_1521976 : Nat := 4983230072969 + 3 ^ 40 * 1521976 * 2
def baseEnd_1521976 : Nat := 347335658936641109155807

theorem tailTrace_1521976 : CollatzResearch.WordTrace tailWord_1521976 prefixEnd_1521976 347335658936641109155807 := by
  unfold tailWord_1521976
  simp only [CollatzResearch.WordTrace]
  refine ⟨27755512567074179825800891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37007350089432239767734521 27755512567074179825800891)
  ·
    refine ⟨41633268850611269738701337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27755512567074179825800891 41633268850611269738701337)
    ·
      refine ⟨31224951637958452304026003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41633268850611269738701337 31224951637958452304026003)
      ·
        refine ⟨46837427456937678456039005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31224951637958452304026003 46837427456937678456039005)
        ·
          refine ⟨17564035296351629421014627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46837427456937678456039005 17564035296351629421014627)
          ·
            refine ⟨26346052944527444131521941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17564035296351629421014627 26346052944527444131521941)
            ·
              refine ⟨1234971231774723943665091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26346052944527444131521941 1234971231774723943665091)
              ·
                refine ⟨1852456847662085915497637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234971231774723943665091 1852456847662085915497637)
                ·
                  refine ⟨347335658936641109155807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852456847662085915497637 347335658936641109155807)
                  ·
                    rfl

theorem cell21_1521976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_1521976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1521976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1521976 prefixEnd_1521976 := by exact prefixLift 1521976
  have htrace : WordTrace (prefixWord ++ tailWord_1521976) baseStart_1521976 baseEnd_1521976 := by
    simpa [prefixWord, tailWord_1521976, baseEnd_1521976] using wordTrace_append hprefix tailTrace_1521976
  have hstable : (prefixWord ++ tailWord_1521976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1521976).length < 2 ^ (prefixWord ++ tailWord_1521976).sum := by decide
  have hdescent : baseEnd_1521976 < baseStart_1521976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1521976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522080 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_1522080 : Nat := 118140960795 + 1522080 * 2 ^ 59
def prefixEnd_1522080 : Nat := 4983230072969 + 3 ^ 40 * 1522080 * 2
def baseEnd_1522080 : Nat := 347359393153560039422261

theorem tailTrace_1522080 : CollatzResearch.WordTrace tailWord_1522080 prefixEnd_1522080 347359393153560039422261 := by
  unfold tailWord_1522080
  simp only [CollatzResearch.WordTrace]
  refine ⟨27757409162885792706693847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37009878883847723608925129 27757409162885792706693847)
  ·
    refine ⟨41636113744328689060040771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27757409162885792706693847 41636113744328689060040771)
    ·
      refine ⟨62454170616493033590061157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41636113744328689060040771 62454170616493033590061157)
      ·
        refine ⟨11710156990592443798136467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62454170616493033590061157 11710156990592443798136467)
        ·
          refine ⟨17565235485888665697204701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11710156990592443798136467 17565235485888665697204701)
          ·
            refine ⟨6586963307208249636451763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17565235485888665697204701 6586963307208249636451763)
            ·
              refine ⟨9880444960812374454677645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586963307208249636451763 9880444960812374454677645)
              ·
                refine ⟨3705166860304640420504117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9880444960812374454677645 3705166860304640420504117)
                ·
                  refine ⟨347359393153560039422261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3705166860304640420504117 347359393153560039422261)
                  ·
                    rfl

theorem cell21_1522080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_1522080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522080 prefixEnd_1522080 := by exact prefixLift 1522080
  have htrace : WordTrace (prefixWord ++ tailWord_1522080) baseStart_1522080 baseEnd_1522080 := by
    simpa [prefixWord, tailWord_1522080, baseEnd_1522080] using wordTrace_append hprefix tailTrace_1522080
  have hstable : (prefixWord ++ tailWord_1522080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522080).length < 2 ^ (prefixWord ++ tailWord_1522080).sum := by decide
  have hdescent : baseEnd_1522080 < baseStart_1522080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522100 : List Nat := [2, 5, 2, 2, 1, 1, 1, 7]
def baseStart_1522100 : Nat := 118140960795 + 1522100 * 2 ^ 59
def prefixEnd_1522100 : Nat := 4983230072969 + 3 ^ 40 * 1522100 * 2
def baseEnd_1522100 : Nat := 115787985808681483029629

theorem tailTrace_1522100 : CollatzResearch.WordTrace tailWord_1522100 prefixEnd_1522100 115787985808681483029629 := by
  unfold tailWord_1522100
  simp only [CollatzResearch.WordTrace]
  refine ⟨27757773892849564414557877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37010365190466085886077169 27757773892849564414557877)
  ·
    refine ⟨2602291302454646663864801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27757773892849564414557877 2602291302454646663864801)
    ·
      refine ⟨1951718476840984997898601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2602291302454646663864801 1951718476840984997898601)
      ·
        refine ⟨1463788857630738748423951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1951718476840984997898601 1463788857630738748423951)
        ·
          refine ⟨2195683286446108122635927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463788857630738748423951 2195683286446108122635927)
          ·
            refine ⟨3293524929669162183953891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195683286446108122635927 3293524929669162183953891)
            ·
              refine ⟨4940287394503743275930837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293524929669162183953891 4940287394503743275930837)
              ·
                refine ⟨115787985808681483029629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4940287394503743275930837 115787985808681483029629)
                ·
                  rfl

theorem cell21_1522100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_1522100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522100 prefixEnd_1522100 := by exact prefixLift 1522100
  have htrace : WordTrace (prefixWord ++ tailWord_1522100) baseStart_1522100 baseEnd_1522100 := by
    simpa [prefixWord, tailWord_1522100, baseEnd_1522100] using wordTrace_append hprefix tailTrace_1522100
  have hstable : (prefixWord ++ tailWord_1522100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522100).length < 2 ^ (prefixWord ++ tailWord_1522100).sum := by decide
  have hdescent : baseEnd_1522100 < baseStart_1522100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522170 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_1522170 : Nat := 118140960795 + 1522170 * 2 ^ 59
def prefixEnd_1522170 : Nat := 4983230072969 + 3 ^ 40 * 1522170 * 2
def baseEnd_1522170 : Nat := 347379932379739882922077

theorem tailTrace_1522170 : CollatzResearch.WordTrace tailWord_1522170 prefixEnd_1522170 347379932379739882922077 := by
  unfold tailWord_1522170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13879525223861382696040991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37012067263630353856109309 13879525223861382696040991)
  ·
    refine ⟨20819287835792074044061487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13879525223861382696040991 20819287835792074044061487)
    ·
      refine ⟨31228931753688111066092231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20819287835792074044061487 31228931753688111066092231)
      ·
        refine ⟨46843397630532166599138347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31228931753688111066092231 46843397630532166599138347)
        ·
          refine ⟨70265096445798249898707521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46843397630532166599138347 70265096445798249898707521)
          ·
            refine ⟨52698822334348687424030641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70265096445798249898707521 52698822334348687424030641)
            ·
              refine ⟨39524116750761515568022981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52698822334348687424030641 39524116750761515568022981)
              ·
                refine ⟨7410771890767784169004309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39524116750761515568022981 7410771890767784169004309)
                ·
                  refine ⟨347379932379739882922077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7410771890767784169004309 347379932379739882922077)
                  ·
                    rfl

theorem cell21_1522170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_1522170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522170 prefixEnd_1522170 := by exact prefixLift 1522170
  have htrace : WordTrace (prefixWord ++ tailWord_1522170) baseStart_1522170 baseEnd_1522170 := by
    simpa [prefixWord, tailWord_1522170, baseEnd_1522170] using wordTrace_append hprefix tailTrace_1522170
  have hstable : (prefixWord ++ tailWord_1522170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522170).length < 2 ^ (prefixWord ++ tailWord_1522170).sum := by decide
  have hdescent : baseEnd_1522170 < baseStart_1522170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522173 : List Nat := [1, 4, 1, 1, 1, 3, 2, 5, 3]
def baseStart_1522173 : Nat := 118140960795 + 1522173 * 2 ^ 59
def prefixEnd_1522173 : Nat := 4983230072969 + 3 ^ 40 * 1522173 * 2
def baseEnd_1522173 : Nat := 347380617020612544372071

theorem tailTrace_1522173 : CollatzResearch.WordTrace tailWord_1522173 prefixEnd_1522173 347380617020612544372071 := by
  unfold tailWord_1522173
  simp only [CollatzResearch.WordTrace]
  refine ⟨55518210314434662296523173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37012140209623108197682115 55518210314434662296523173)
  ·
    refine ⟨10409664433956499180598095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55518210314434662296523173 10409664433956499180598095)
    ·
      refine ⟨15614496650934748770897143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10409664433956499180598095 15614496650934748770897143)
      ·
        refine ⟨23421744976402123156345715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15614496650934748770897143 23421744976402123156345715)
        ·
          refine ⟨35132617464603184734518573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23421744976402123156345715 35132617464603184734518573)
          ·
            refine ⟨13174731549226194275444465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35132617464603184734518573 13174731549226194275444465)
            ·
              refine ⟨9881048661919645706583349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13174731549226194275444465 9881048661919645706583349)
              ·
                refine ⟨926348312054966784992189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9881048661919645706583349 926348312054966784992189)
                ·
                  refine ⟨347380617020612544372071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926348312054966784992189 347380617020612544372071)
                  ·
                    rfl

theorem cell21_1522173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_1522173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522173 prefixEnd_1522173 := by exact prefixLift 1522173
  have htrace : WordTrace (prefixWord ++ tailWord_1522173) baseStart_1522173 baseEnd_1522173 := by
    simpa [prefixWord, tailWord_1522173, baseEnd_1522173] using wordTrace_append hprefix tailTrace_1522173
  have hstable : (prefixWord ++ tailWord_1522173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522173).length < 2 ^ (prefixWord ++ tailWord_1522173).sum := by decide
  have hdescent : baseEnd_1522173 < baseStart_1522173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522182 : List Nat := [6, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1522182 : Nat := 118140960795 + 1522182 * 2 ^ 59
def prefixEnd_1522182 : Nat := 4983230072969 + 3 ^ 40 * 1522182 * 2
def baseEnd_1522182 : Nat := 347382670943230528722053

theorem tailTrace_1522182 : CollatzResearch.WordTrace tailWord_1522182 prefixEnd_1522182 347382670943230528722053 := by
  unfold tailWord_1522182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734954330356314276050025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37012359047601371222400533 1734954330356314276050025)
  ·
    refine ⟨1301215747767235707037519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1734954330356314276050025 1301215747767235707037519)
    ·
      refine ⟨1951823621650853560556279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301215747767235707037519 1951823621650853560556279)
      ·
        refine ⟨2927735432476280340834419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951823621650853560556279 2927735432476280340834419)
        ·
          refine ⟨4391603148714420511251629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927735432476280340834419 4391603148714420511251629)
          ·
            refine ⟨1646851180767907691719361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4391603148714420511251629 1646851180767907691719361)
            ·
              refine ⟨1235138385575930768789521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646851180767907691719361 1235138385575930768789521)
              ·
                refine ⟨926353789181948076592141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235138385575930768789521 926353789181948076592141)
                ·
                  refine ⟨347382670943230528722053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926353789181948076592141 347382670943230528722053)
                  ·
                    rfl

theorem cell21_1522182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1522182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522182 prefixEnd_1522182 := by exact prefixLift 1522182
  have htrace : WordTrace (prefixWord ++ tailWord_1522182) baseStart_1522182 baseEnd_1522182 := by
    simpa [prefixWord, tailWord_1522182, baseEnd_1522182] using wordTrace_append hprefix tailTrace_1522182
  have hstable : (prefixWord ++ tailWord_1522182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522182).length < 2 ^ (prefixWord ++ tailWord_1522182).sum := by decide
  have hdescent : baseEnd_1522182 < baseStart_1522182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522187 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 4]
def baseStart_1522187 : Nat := 118140960795 + 1522187 * 2 ^ 59
def prefixEnd_1522187 : Nat := 4983230072969 + 3 ^ 40 * 1522187 * 2
def baseEnd_1522187 : Nat := 347383812011351631138709

theorem tailTrace_1522187 : CollatzResearch.WordTrace tailWord_1522187 prefixEnd_1522187 347383812011351631138709 := by
  unfold tailWord_1522187
  simp only [CollatzResearch.WordTrace]
  refine ⟨55518720936383942687532815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37012480624255961791688543 55518720936383942687532815)
  ·
    refine ⟨83278081404575914031299223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55518720936383942687532815 83278081404575914031299223)
    ·
      refine ⟨124917122106863871046948835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83278081404575914031299223 124917122106863871046948835)
      ·
        refine ⟨187375683160295806570423253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124917122106863871046948835 187375683160295806570423253)
        ·
          refine ⟨4391617574069432966494295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 187375683160295806570423253 4391617574069432966494295)
          ·
            refine ⟨6587426361104149449741443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4391617574069432966494295 6587426361104149449741443)
            ·
              refine ⟨9881139541656224174612165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6587426361104149449741443 9881139541656224174612165)
              ·
                refine ⟨1852713664060542032739781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9881139541656224174612165 1852713664060542032739781)
                ·
                  refine ⟨347383812011351631138709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852713664060542032739781 347383812011351631138709)
                  ·
                    rfl

theorem cell21_1522187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 4].length) (baseStart_1522187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522187 prefixEnd_1522187 := by exact prefixLift 1522187
  have htrace : WordTrace (prefixWord ++ tailWord_1522187) baseStart_1522187 baseEnd_1522187 := by
    simpa [prefixWord, tailWord_1522187, baseEnd_1522187] using wordTrace_append hprefix tailTrace_1522187
  have hstable : (prefixWord ++ tailWord_1522187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522187).length < 2 ^ (prefixWord ++ tailWord_1522187).sum := by decide
  have hdescent : baseEnd_1522187 < baseStart_1522187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522190 : List Nat := [4, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_1522190 : Nat := 118140960795 + 1522190 * 2 ^ 59
def prefixEnd_1522190 : Nat := 4983230072969 + 3 ^ 40 * 1522190 * 2
def baseEnd_1522190 : Nat := 347384496652224292588703

theorem tailTrace_1522190 : CollatzResearch.WordTrace tailWord_1522190 prefixEnd_1522190 347384496652224292588703 := by
  unfold tailWord_1522190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6939853794421634274986503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37012553570248716133261349 6939853794421634274986503)
  ·
    refine ⟨10409780691632451412479755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6939853794421634274986503 10409780691632451412479755)
    ·
      refine ⟨15614671037448677118719633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10409780691632451412479755 15614671037448677118719633)
      ·
        refine ⟨11711003278086507839039725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15614671037448677118719633 11711003278086507839039725)
        ·
          refine ⟨4391626229282440439639897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11711003278086507839039725 4391626229282440439639897)
          ·
            refine ⟨3293719671961830329729923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4391626229282440439639897 3293719671961830329729923)
            ·
              refine ⟨4940579507942745494594885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293719671961830329729923 4940579507942745494594885)
              ·
                refine ⟨926358657739264780236541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4940579507942745494594885 926358657739264780236541)
                ·
                  refine ⟨347384496652224292588703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926358657739264780236541 347384496652224292588703)
                  ·
                    rfl

theorem cell21_1522190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_1522190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522190 prefixEnd_1522190 := by exact prefixLift 1522190
  have htrace : WordTrace (prefixWord ++ tailWord_1522190) baseStart_1522190 baseEnd_1522190 := by
    simpa [prefixWord, tailWord_1522190, baseEnd_1522190] using wordTrace_append hprefix tailTrace_1522190
  have hstable : (prefixWord ++ tailWord_1522190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522190).length < 2 ^ (prefixWord ++ tailWord_1522190).sum := by decide
  have hdescent : baseEnd_1522190 < baseStart_1522190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522238 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_1522238 : Nat := 118140960795 + 1522238 * 2 ^ 59
def prefixEnd_1522238 : Nat := 4983230072969 + 3 ^ 40 * 1522238 * 2
def baseEnd_1522238 : Nat := 347395450906186875788605

theorem tailTrace_1522238 : CollatzResearch.WordTrace tailWord_1522238 prefixEnd_1522238 347395450906186875788605 := by
  unfold tailWord_1522238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6940072632399897299704921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37013720706132785598426245 6940072632399897299704921)
  ·
    refine ⟨5205054474299922974778691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6940072632399897299704921 5205054474299922974778691)
    ·
      refine ⟨7807581711449884462168037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5205054474299922974778691 7807581711449884462168037)
      ·
        refine ⟨1463921570896853336656507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7807581711449884462168037 1463921570896853336656507)
        ·
          refine ⟨2195882356345280004984761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463921570896853336656507 2195882356345280004984761)
          ·
            refine ⟨1646911767258960003738571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195882356345280004984761 1646911767258960003738571)
            ·
              refine ⟨2470367650888440005607857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646911767258960003738571 2470367650888440005607857)
              ·
                refine ⟨1852775738166330004205893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2470367650888440005607857 1852775738166330004205893)
                ·
                  refine ⟨347395450906186875788605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852775738166330004205893 347395450906186875788605)
                  ·
                    rfl

theorem cell21_1522238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_1522238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522238 prefixEnd_1522238 := by exact prefixLift 1522238
  have htrace : WordTrace (prefixWord ++ tailWord_1522238) baseStart_1522238 baseEnd_1522238 := by
    simpa [prefixWord, tailWord_1522238, baseEnd_1522238] using wordTrace_append hprefix tailTrace_1522238
  have hstable : (prefixWord ++ tailWord_1522238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522238).length < 2 ^ (prefixWord ++ tailWord_1522238).sum := by decide
  have hdescent : baseEnd_1522238 < baseStart_1522238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1522314 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_1522314 : Nat := 118140960795 + 1522314 * 2 ^ 59
def prefixEnd_1522314 : Nat := 4983230072969 + 3 ^ 40 * 1522314 * 2
def baseEnd_1522314 : Nat := 347412795141627632521783

theorem tailTrace_1522314 : CollatzResearch.WordTrace tailWord_1522314 prefixEnd_1522314 347412795141627632521783 := by
  unfold tailWord_1522314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13880838251730960844351499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37015568671282562251603997 13880838251730960844351499)
  ·
    refine ⟨20821257377596441266527249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13880838251730960844351499 20821257377596441266527249)
    ·
      refine ⟨15615943033197330949895437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20821257377596441266527249 15615943033197330949895437)
      ·
        refine ⟨5855978637448999106210789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15615943033197330949895437 5855978637448999106210789)
        ·
          refine ⟨1097995994521687332414523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5855978637448999106210789 1097995994521687332414523)
          ·
            refine ⟨1646993991782530998621785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097995994521687332414523 1646993991782530998621785)
            ·
              refine ⟨1235245493836898248966339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646993991782530998621785 1235245493836898248966339)
              ·
                refine ⟨1852868240755347373449509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235245493836898248966339 1852868240755347373449509)
                ·
                  refine ⟨347412795141627632521783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852868240755347373449509 347412795141627632521783)
                  ·
                    rfl

theorem cell21_1522314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_1522314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1522314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1522314 prefixEnd_1522314 := by exact prefixLift 1522314
  have htrace : WordTrace (prefixWord ++ tailWord_1522314) baseStart_1522314 baseEnd_1522314 := by
    simpa [prefixWord, tailWord_1522314, baseEnd_1522314] using wordTrace_append hprefix tailTrace_1522314
  have hstable : (prefixWord ++ tailWord_1522314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1522314).length < 2 ^ (prefixWord ++ tailWord_1522314).sum := by decide
  have hdescent : baseEnd_1522314 < baseStart_1522314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1522314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
