import V185TrunkScan23Chunk0380

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2252417 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2252417 : Nat := 118140960795 + 2252417 * 2 ^ 59
def prefixEnd_2252417 : Nat := 4983230072969 + 3 ^ 40 * 2252417 * 2
def baseEnd_2252417 : Nat := 1156572555358219141828829

theorem tailTrace_2252417 : CollatzResearch.WordTrace tailWord_2252417 prefixEnd_2252417 1156572555358219141828829 := by
  unfold tailWord_2252417
  simp only [CollatzResearch.WordTrace]
  refine ⟨82152397080885366042595505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54768264720590244028397003 82152397080885366042595505)
  ·
    refine ⟨61614297810664024531946629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82152397080885366042595505 61614297810664024531946629)
    ·
      refine ⟨11552680839499504599739993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61614297810664024531946629 11552680839499504599739993)
      ·
        refine ⟨8664510629624628449804995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11552680839499504599739993 8664510629624628449804995)
        ·
          refine ⟨12996765944436942674707493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8664510629624628449804995 12996765944436942674707493)
          ·
            refine ⟨2436893614581926751507655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12996765944436942674707493 2436893614581926751507655)
            ·
              refine ⟨3655340421872890127261483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436893614581926751507655 3655340421872890127261483)
              ·
                refine ⟨5483010632809335190892225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3655340421872890127261483 5483010632809335190892225)
                ·
                  refine ⟨4112257974607001393169169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5483010632809335190892225 4112257974607001393169169)
                  ·
                    refine ⟨3084193480955251044876877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4112257974607001393169169 3084193480955251044876877)
                    ·
                      refine ⟨1156572555358219141828829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3084193480955251044876877 1156572555358219141828829)
                      ·
                        rfl

theorem cell23_2252417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2252417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252417 prefixEnd_2252417 := by exact prefixLift 2252417
  have htrace : WordTrace (prefixWord ++ tailWord_2252417) baseStart_2252417 baseEnd_2252417 := by
    simpa [prefixWord, tailWord_2252417, baseEnd_2252417] using wordTrace_append hprefix tailTrace_2252417
  have hstable : (prefixWord ++ tailWord_2252417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252417).length < 2 ^ (prefixWord ++ tailWord_2252417).sum := by decide
  have hdescent : baseEnd_2252417 < baseStart_2252417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252453 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_2252453 : Nat := 118140960795 + 2252453 * 2 ^ 59
def prefixEnd_2252453 : Nat := 4983230072969 + 3 ^ 40 * 2252453 * 2
def baseEnd_2252453 : Nat := 1156591040661781000978663

theorem tailTrace_2252453 : CollatzResearch.WordTrace tailWord_2252453 prefixEnd_2252453 1156591040661781000978663 := by
  unfold tailWord_2252453
  simp only [CollatzResearch.WordTrace]
  refine ⟨82153710108754944190906013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54769140072503296127270675 82153710108754944190906013)
  ·
    refine ⟨30807641290783104071589755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82153710108754944190906013 30807641290783104071589755)
    ·
      refine ⟨46211461936174656107384633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30807641290783104071589755 46211461936174656107384633)
      ·
        refine ⟨34658596452130992080538475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46211461936174656107384633 34658596452130992080538475)
        ·
          refine ⟨51987894678196488120807713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34658596452130992080538475 51987894678196488120807713)
          ·
            refine ⟨38990921008647366090605785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51987894678196488120807713 38990921008647366090605785)
            ·
              refine ⟨29243190756485524567954339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38990921008647366090605785 29243190756485524567954339)
              ·
                refine ⟨43864786134728286851931509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29243190756485524567954339 43864786134728286851931509)
                ·
                  refine ⟨4112323700130776892368579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43864786134728286851931509 4112323700130776892368579)
                  ·
                    refine ⟨6168485550196165338552869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4112323700130776892368579 6168485550196165338552869)
                    ·
                      refine ⟨1156591040661781000978663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6168485550196165338552869 1156591040661781000978663)
                      ·
                        rfl

theorem cell23_2252453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_2252453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252453 prefixEnd_2252453 := by exact prefixLift 2252453
  have htrace : WordTrace (prefixWord ++ tailWord_2252453) baseStart_2252453 baseEnd_2252453 := by
    simpa [prefixWord, tailWord_2252453, baseEnd_2252453] using wordTrace_append hprefix tailTrace_2252453
  have hstable : (prefixWord ++ tailWord_2252453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252453).length < 2 ^ (prefixWord ++ tailWord_2252453).sum := by decide
  have hdescent : baseEnd_2252453 < baseStart_2252453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252500 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2252500 : Nat := 118140960795 + 2252500 * 2 ^ 59
def prefixEnd_2252500 : Nat := 4983230072969 + 3 ^ 40 * 2252500 * 2
def baseEnd_2252500 : Nat := 1156615174252542317090947

theorem tailTrace_2252500 : CollatzResearch.WordTrace tailWord_2252500 prefixEnd_2252500 1156615174252542317090947 := by
  unfold tailWord_2252500
  simp only [CollatzResearch.WordTrace]
  refine ⟨41077712169792335608933477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54770282893056447478577969 41077712169792335608933477)
  ·
    refine ⟨7702071031836062926675027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41077712169792335608933477 7702071031836062926675027)
    ·
      refine ⟨11553106547754094390012541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7702071031836062926675027 11553106547754094390012541)
      ·
        refine ⟨4332414955407785396254703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11553106547754094390012541 4332414955407785396254703)
        ·
          refine ⟨6498622433111678094382055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332414955407785396254703 6498622433111678094382055)
          ·
            refine ⟨9747933649667517141573083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6498622433111678094382055 9747933649667517141573083)
            ·
              refine ⟨14621900474501275712359625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9747933649667517141573083 14621900474501275712359625)
              ·
                refine ⟨10966425355875956784269719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14621900474501275712359625 10966425355875956784269719)
                ·
                  refine ⟨16449638033813935176404579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10966425355875956784269719 16449638033813935176404579)
                  ·
                    refine ⟨24674457050720902764606869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16449638033813935176404579 24674457050720902764606869)
                    ·
                      refine ⟨1156615174252542317090947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24674457050720902764606869 1156615174252542317090947)
                      ·
                        rfl

theorem cell23_2252500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2252500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252500 prefixEnd_2252500 := by exact prefixLift 2252500
  have htrace : WordTrace (prefixWord ++ tailWord_2252500) baseStart_2252500 baseEnd_2252500 := by
    simpa [prefixWord, tailWord_2252500, baseEnd_2252500] using wordTrace_append hprefix tailTrace_2252500
  have hstable : (prefixWord ++ tailWord_2252500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252500).length < 2 ^ (prefixWord ++ tailWord_2252500).sum := by decide
  have hdescent : baseEnd_2252500 < baseStart_2252500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252547 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 1, 3, 2]
def baseStart_2252547 : Nat := 118140960795 + 2252547 * 2 ^ 59
def prefixEnd_2252547 : Nat := 4983230072969 + 3 ^ 40 * 2252547 * 2
def baseEnd_2252547 : Nat := 1156639307843303633203231

theorem tailTrace_2252547 : CollatzResearch.WordTrace tailWord_2252547 prefixEnd_2252547 1156639307843303633203231 := by
  unfold tailWord_2252547
  simp only [CollatzResearch.WordTrace]
  refine ⟨82157138570414398244827895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54771425713609598829885263 82157138570414398244827895)
  ·
    refine ⟨123235707855621597367241843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82157138570414398244827895 123235707855621597367241843)
    ·
      refine ⟨184853561783432396050862765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123235707855621597367241843 184853561783432396050862765)
      ·
        refine ⟨69320085668787148519073537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184853561783432396050862765 69320085668787148519073537)
        ·
          refine ⟨51990064251590361389305153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69320085668787148519073537 51990064251590361389305153)
          ·
            refine ⟨38992548188692771041978865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51990064251590361389305153 38992548188692771041978865)
            ·
              refine ⟨29244411141519578281484149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38992548188692771041978865 29244411141519578281484149)
              ·
                refine ⟨2741663544517460463889139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29244411141519578281484149 2741663544517460463889139)
                ·
                  refine ⟨4112495316776190695833709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741663544517460463889139 4112495316776190695833709)
                  ·
                    refine ⟨1542185743791071510937641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4112495316776190695833709 1542185743791071510937641)
                    ·
                      refine ⟨1156639307843303633203231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542185743791071510937641 1156639307843303633203231)
                      ·
                        rfl

theorem cell23_2252547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_2252547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252547 prefixEnd_2252547 := by exact prefixLift 2252547
  have htrace : WordTrace (prefixWord ++ tailWord_2252547) baseStart_2252547 baseEnd_2252547 := by
    simpa [prefixWord, tailWord_2252547, baseEnd_2252547] using wordTrace_append hprefix tailTrace_2252547
  have hstable : (prefixWord ++ tailWord_2252547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252547).length < 2 ^ (prefixWord ++ tailWord_2252547).sum := by decide
  have hdescent : baseEnd_2252547 < baseStart_2252547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252553 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 2, 6]
def baseStart_2252553 : Nat := 118140960795 + 2252553 * 2 ^ 59
def prefixEnd_2252553 : Nat := 4983230072969 + 3 ^ 40 * 2252553 * 2
def baseEnd_2252553 : Nat := 385547462909076869909401

theorem tailTrace_2252553 : CollatzResearch.WordTrace tailWord_2252553 prefixEnd_2252553 385547462909076869909401 := by
  unfold tailWord_2252553
  simp only [CollatzResearch.WordTrace]
  refine ⟨82157357408392661269546313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54771571605595107513030875 82157357408392661269546313)
  ·
    refine ⟨61618018056294495952159735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82157357408392661269546313 61618018056294495952159735)
    ·
      refine ⟨92427027084441743928239603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61618018056294495952159735 92427027084441743928239603)
      ·
        refine ⟨138640540626662615892359405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92427027084441743928239603 138640540626662615892359405)
        ·
          refine ⟨51990202734998480959634777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138640540626662615892359405 51990202734998480959634777)
          ·
            refine ⟨38992652051248860719726083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51990202734998480959634777 38992652051248860719726083)
            ·
              refine ⟨58488978076873291079589125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38992652051248860719726083 58488978076873291079589125)
              ·
                refine ⟨10966683389413742077422961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58488978076873291079589125 10966683389413742077422961)
                ·
                  refine ⟨8225012542060306558067221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10966683389413742077422961 8225012542060306558067221)
                  ·
                    refine ⟨385547462909076869909401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8225012542060306558067221 385547462909076869909401)
                    ·
                      rfl

theorem cell23_2252553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_2252553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252553 prefixEnd_2252553 := by exact prefixLift 2252553
  have htrace : WordTrace (prefixWord ++ tailWord_2252553) baseStart_2252553 baseEnd_2252553 := by
    simpa [prefixWord, tailWord_2252553, baseEnd_2252553] using wordTrace_append hprefix tailTrace_2252553
  have hstable : (prefixWord ++ tailWord_2252553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252553).length < 2 ^ (prefixWord ++ tailWord_2252553).sum := by decide
  have hdescent : baseEnd_2252553 < baseStart_2252553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252554 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_2252554 : Nat := 118140960795 + 2252554 * 2 ^ 59
def prefixEnd_2252554 : Nat := 4983230072969 + 3 ^ 40 * 2252554 * 2
def baseEnd_2252554 : Nat := 1156642902207885105815699

theorem tailTrace_2252554 : CollatzResearch.WordTrace tailWord_2252554 prefixEnd_2252554 1156642902207885105815699 := by
  unfold tailWord_2252554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20539348470347259610083179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54771595920926025626888477 20539348470347259610083179)
  ·
    refine ⟨30809022705520889415124769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20539348470347259610083179 30809022705520889415124769)
    ·
      refine ⟨23106767029140667061343577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30809022705520889415124769 23106767029140667061343577)
      ·
        refine ⟨17330075271855500296007683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23106767029140667061343577 17330075271855500296007683)
        ·
          refine ⟨25995112907783250444011525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17330075271855500296007683 25995112907783250444011525)
          ·
            refine ⟨4874083670209359458252161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25995112907783250444011525 4874083670209359458252161)
            ·
              refine ⟨3655562752657019593689121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4874083670209359458252161 3655562752657019593689121)
              ·
                refine ⟨2741672064492764695266841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655562752657019593689121 2741672064492764695266841)
                ·
                  refine ⟨2056254048369573521450131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741672064492764695266841 2056254048369573521450131)
                  ·
                    refine ⟨3084381072554360282175197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056254048369573521450131 3084381072554360282175197)
                    ·
                      refine ⟨1156642902207885105815699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3084381072554360282175197 1156642902207885105815699)
                      ·
                        rfl

theorem cell23_2252554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_2252554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252554 prefixEnd_2252554 := by exact prefixLift 2252554
  have htrace : WordTrace (prefixWord ++ tailWord_2252554) baseStart_2252554 baseEnd_2252554 := by
    simpa [prefixWord, tailWord_2252554, baseEnd_2252554] using wordTrace_append hprefix tailTrace_2252554
  have hstable : (prefixWord ++ tailWord_2252554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252554).length < 2 ^ (prefixWord ++ tailWord_2252554).sum := by decide
  have hdescent : baseEnd_2252554 < baseStart_2252554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252563 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 5]
def baseStart_2252563 : Nat := 118140960795 + 2252563 * 2 ^ 59
def prefixEnd_2252563 : Nat := 4983230072969 + 3 ^ 40 * 2252563 * 2
def baseEnd_2252563 : Nat := 1156647523533775570603157

theorem tailTrace_2252563 : CollatzResearch.WordTrace tailWord_2252563 prefixEnd_2252563 1156647523533775570603157 := by
  unfold tailWord_2252563
  simp only [CollatzResearch.WordTrace]
  refine ⟨82157722138356432977410343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54771814758904288651606895 82157722138356432977410343)
  ·
    refine ⟨123236583207534649466115515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82157722138356432977410343 123236583207534649466115515)
    ·
      refine ⟨184854874811301974199173273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123236583207534649466115515 184854874811301974199173273)
      ·
        refine ⟨138641156108476480649379955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184854874811301974199173273 138641156108476480649379955)
        ·
          refine ⟨207961734162714720974069933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138641156108476480649379955 207961734162714720974069933)
          ·
            refine ⟨77985650311018020365276225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207961734162714720974069933 77985650311018020365276225)
            ·
              refine ⟨58489237733263515273957169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77985650311018020365276225 58489237733263515273957169)
              ·
                refine ⟨43866928299947636455467877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58489237733263515273957169 43866928299947636455467877)
                ·
                  refine ⟨8225049056240181835400227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43866928299947636455467877 8225049056240181835400227)
                  ·
                    refine ⟨12337573584360272753100341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8225049056240181835400227 12337573584360272753100341)
                    ·
                      refine ⟨1156647523533775570603157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12337573584360272753100341 1156647523533775570603157)
                      ·
                        rfl

theorem cell23_2252563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_2252563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252563 prefixEnd_2252563 := by exact prefixLift 2252563
  have htrace : WordTrace (prefixWord ++ tailWord_2252563) baseStart_2252563 baseEnd_2252563 := by
    simpa [prefixWord, tailWord_2252563, baseEnd_2252563] using wordTrace_append hprefix tailTrace_2252563
  have hstable : (prefixWord ++ tailWord_2252563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252563).length < 2 ^ (prefixWord ++ tailWord_2252563).sum := by decide
  have hdescent : baseEnd_2252563 < baseStart_2252563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252570 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_2252570 : Nat := 118140960795 + 2252570 * 2 ^ 59
def prefixEnd_2252570 : Nat := 4983230072969 + 3 ^ 40 * 2252570 * 2
def baseEnd_2252570 : Nat := 385550372632785681071875

theorem tailTrace_2252570 : CollatzResearch.WordTrace tailWord_2252570 prefixEnd_2252570 385550372632785681071875 := by
  unfold tailWord_2252570
  simp only [CollatzResearch.WordTrace]
  refine ⟨20539494362332768293228791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54771984966220715448610109 20539494362332768293228791)
  ·
    refine ⟨30809241543499152439843187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20539494362332768293228791 30809241543499152439843187)
    ·
      refine ⟨46213862315248728659764781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30809241543499152439843187 46213862315248728659764781)
      ·
        refine ⟨17330198368218273247411793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46213862315248728659764781 17330198368218273247411793)
        ·
          refine ⟨12997648776163704935558845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17330198368218273247411793 12997648776163704935558845)
          ·
            refine ⟨4874118291061389350834567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12997648776163704935558845 4874118291061389350834567)
            ·
              refine ⟨7311177436592084026251851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4874118291061389350834567 7311177436592084026251851)
              ·
                refine ⟨10966766154888126039377777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7311177436592084026251851 10966766154888126039377777)
                ·
                  refine ⟨8225074616166094529533333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10966766154888126039377777 8225074616166094529533333)
                  ·
                    refine ⟨385550372632785681071875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8225074616166094529533333 385550372632785681071875)
                    ·
                      rfl

theorem cell23_2252570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_2252570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252570 prefixEnd_2252570 := by exact prefixLift 2252570
  have htrace : WordTrace (prefixWord ++ tailWord_2252570) baseStart_2252570 baseEnd_2252570 := by
    simpa [prefixWord, tailWord_2252570, baseEnd_2252570] using wordTrace_append hprefix tailTrace_2252570
  have hstable : (prefixWord ++ tailWord_2252570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252570).length < 2 ^ (prefixWord ++ tailWord_2252570).sum := by decide
  have hdescent : baseEnd_2252570 < baseStart_2252570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252577 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_2252577 : Nat := 118140960795 + 2252577 * 2 ^ 59
def prefixEnd_2252577 : Nat := 4983230072969 + 3 ^ 40 * 2252577 * 2
def baseEnd_2252577 : Nat := 1156654712262938515828093

theorem tailTrace_2252577 : CollatzResearch.WordTrace tailWord_2252577 prefixEnd_2252577 1156654712262938515828093 := by
  unfold tailWord_2252577
  simp only [CollatzResearch.WordTrace]
  refine ⟨82158232760305713368419985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54772155173537142245613323 82158232760305713368419985)
  ·
    refine ⟨61618674570229285026314989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82158232760305713368419985 61618674570229285026314989)
    ·
      refine ⟨23107002963835981884868121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61618674570229285026314989 23107002963835981884868121)
      ·
        refine ⟨17330252222876986413651091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23107002963835981884868121 17330252222876986413651091)
        ·
          refine ⟨25995378334315479620476637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17330252222876986413651091 25995378334315479620476637)
          ·
            refine ⟨9748266875368304857678739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25995378334315479620476637 9748266875368304857678739)
            ·
              refine ⟨14622400313052457286518109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9748266875368304857678739 14622400313052457286518109)
              ·
                refine ⟨5483400117394671482444291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14622400313052457286518109 5483400117394671482444291)
                ·
                  refine ⟨8225100176092007223666437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5483400117394671482444291 8225100176092007223666437)
                  ·
                    refine ⟨1542206283017251354437457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8225100176092007223666437 1542206283017251354437457)
                    ·
                      refine ⟨1156654712262938515828093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542206283017251354437457 1156654712262938515828093)
                      ·
                        rfl

theorem cell23_2252577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_2252577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252577 prefixEnd_2252577 := by exact prefixLift 2252577
  have htrace : WordTrace (prefixWord ++ tailWord_2252577) baseStart_2252577 baseEnd_2252577 := by
    simpa [prefixWord, tailWord_2252577, baseEnd_2252577] using wordTrace_append hprefix tailTrace_2252577
  have hstable : (prefixWord ++ tailWord_2252577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252577).length < 2 ^ (prefixWord ++ tailWord_2252577).sum := by decide
  have hdescent : baseEnd_2252577 < baseStart_2252577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252598 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2252598 : Nat := 118140960795 + 2252598 * 2 ^ 59
def prefixEnd_2252598 : Nat := 4983230072969 + 3 ^ 40 * 2252598 * 2
def baseEnd_2252598 : Nat := 1156665495356682933665497

theorem tailTrace_2252598 : CollatzResearch.WordTrace tailWord_2252598 prefixEnd_2252598 1156665495356682933665497 := by
  unfold tailWord_2252598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134937418326852122183403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54772665795486422636622965 5134937418326852122183403)
  ·
    refine ⟨7702406127490278183275105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5134937418326852122183403 7702406127490278183275105)
    ·
      refine ⟨5776804595617708637456329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7702406127490278183275105 5776804595617708637456329)
      ·
        refine ⟨4332603446713281478092247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5776804595617708637456329 4332603446713281478092247)
        ·
          refine ⟨6498905170069922217138371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332603446713281478092247 6498905170069922217138371)
          ·
            refine ⟨9748357755104883325707557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6498905170069922217138371 9748357755104883325707557)
            ·
              refine ⟨1827817079082165623570167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9748357755104883325707557 1827817079082165623570167)
              ·
                refine ⟨2741725618623248435355251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827817079082165623570167 2741725618623248435355251)
                ·
                  refine ⟨4112588427934872653032877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741725618623248435355251 4112588427934872653032877)
                  ·
                    refine ⟨1542220660475577244887329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4112588427934872653032877 1542220660475577244887329)
                    ·
                      refine ⟨1156665495356682933665497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542220660475577244887329 1156665495356682933665497)
                      ·
                        rfl

theorem cell23_2252598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2252598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252598 prefixEnd_2252598 := by exact prefixLift 2252598
  have htrace : WordTrace (prefixWord ++ tailWord_2252598) baseStart_2252598 baseEnd_2252598 := by
    simpa [prefixWord, tailWord_2252598, baseEnd_2252598] using wordTrace_append hprefix tailTrace_2252598
  have hstable : (prefixWord ++ tailWord_2252598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252598).length < 2 ^ (prefixWord ++ tailWord_2252598).sum := by decide
  have hdescent : baseEnd_2252598 < baseStart_2252598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252611 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 2, 2, 2]
def baseStart_2252611 : Nat := 118140960795 + 2252611 * 2 ^ 59
def prefixEnd_2252611 : Nat := 4983230072969 + 3 ^ 40 * 2252611 * 2
def baseEnd_2252611 : Nat := 1156672170605191382802937

theorem tailTrace_2252611 : CollatzResearch.WordTrace tailWord_2252611 prefixEnd_2252611 1156672170605191382802937 := by
  unfold tailWord_2252611
  simp only [CollatzResearch.WordTrace]
  refine ⟨82159472842182537175157687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54772981894788358116771791 82159472842182537175157687)
  ·
    refine ⟨123239209263273805762736531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82159472842182537175157687 123239209263273805762736531)
    ·
      refine ⟨184858813894910708644104797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123239209263273805762736531 184858813894910708644104797)
      ·
        refine ⟨69322055210591515741539299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184858813894910708644104797 69322055210591515741539299)
        ·
          refine ⟨103983082815887273612308949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69322055210591515741539299 103983082815887273612308949)
          ·
            refine ⟨2437103503497357975288491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103983082815887273612308949 2437103503497357975288491)
            ·
              refine ⟨3655655255246036962932737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437103503497357975288491 3655655255246036962932737)
              ·
                refine ⟨2741741441434527722199553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655655255246036962932737 2741741441434527722199553)
                ·
                  refine ⟨2056306081075895791649665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741741441434527722199553 2056306081075895791649665)
                  ·
                    refine ⟨1542229560806921843737249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2056306081075895791649665 1542229560806921843737249)
                    ·
                      refine ⟨1156672170605191382802937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542229560806921843737249 1156672170605191382802937)
                      ·
                        rfl

theorem cell23_2252611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_2252611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252611 prefixEnd_2252611 := by exact prefixLift 2252611
  have htrace : WordTrace (prefixWord ++ tailWord_2252611) baseStart_2252611 baseEnd_2252611 := by
    simpa [prefixWord, tailWord_2252611, baseEnd_2252611] using wordTrace_append hprefix tailTrace_2252611
  have hstable : (prefixWord ++ tailWord_2252611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252611).length < 2 ^ (prefixWord ++ tailWord_2252611).sum := by decide
  have hdescent : baseEnd_2252611 < baseStart_2252611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252628 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_2252628 : Nat := 118140960795 + 2252628 * 2 ^ 59
def prefixEnd_2252628 : Nat := 4983230072969 + 3 ^ 40 * 2252628 * 2
def baseEnd_2252628 : Nat := 1156680899776317816290359

theorem tailTrace_2252628 : CollatzResearch.WordTrace tailWord_2252628 prefixEnd_2252628 1156680899776317816290359 := by
  unfold tailWord_2252628
  simp only [CollatzResearch.WordTrace]
  refine ⟨41080046441560474539263269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54773395255413966052351025 41080046441560474539263269)
  ·
    refine ⟨7702508707792588976111863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41080046441560474539263269 7702508707792588976111863)
    ·
      refine ⟨11553763061688883464167795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7702508707792588976111863 11553763061688883464167795)
      ·
        refine ⟨17330644592533325196251693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11553763061688883464167795 17330644592533325196251693)
        ·
          refine ⟨6498991722199996948594385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17330644592533325196251693 6498991722199996948594385)
          ·
            refine ⟨4874243791649997711445789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6498991722199996948594385 4874243791649997711445789)
            ·
              refine ⟨1827841421868749141792171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4874243791649997711445789 1827841421868749141792171)
              ·
                refine ⟨2741762132803123712688257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827841421868749141792171 2741762132803123712688257)
                ·
                  refine ⟨2056321599602342784516193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741762132803123712688257 2056321599602342784516193)
                  ·
                    refine ⟨1542241199701757088387145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2056321599602342784516193 1542241199701757088387145)
                    ·
                      refine ⟨1156680899776317816290359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542241199701757088387145 1156680899776317816290359)
                      ·
                        rfl

theorem cell23_2252628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_2252628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252628 prefixEnd_2252628 := by exact prefixLift 2252628
  have htrace : WordTrace (prefixWord ++ tailWord_2252628) baseStart_2252628 baseEnd_2252628 := by
    simpa [prefixWord, tailWord_2252628, baseEnd_2252628] using wordTrace_append hprefix tailTrace_2252628
  have hstable : (prefixWord ++ tailWord_2252628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252628).length < 2 ^ (prefixWord ++ tailWord_2252628).sum := by decide
  have hdescent : baseEnd_2252628 < baseStart_2252628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252727 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 3, 5, 2]
def baseStart_2252727 : Nat := 118140960795 + 2252727 * 2 ^ 59
def prefixEnd_2252727 : Nat := 4983230072969 + 3 ^ 40 * 2252727 * 2
def baseEnd_2252727 : Nat := 1156731734361112928952403

theorem tailTrace_2252727 : CollatzResearch.WordTrace tailWord_2252727 prefixEnd_2252727 1156731734361112928952403 := by
  unfold tailWord_2252727
  simp only [CollatzResearch.WordTrace]
  refine ⟨82163703709762288986380435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54775802473174859324253623 82163703709762288986380435)
  ·
    refine ⟨123245555564643433479570653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82163703709762288986380435 123245555564643433479570653)
    ·
      refine ⟨46217083336741287554838995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123245555564643433479570653 46217083336741287554838995)
      ·
        refine ⟨69325625005111931332258493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46217083336741287554838995 69325625005111931332258493)
        ·
          refine ⟨25997109376916974249596935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69325625005111931332258493 25997109376916974249596935)
          ·
            refine ⟨38995664065375461374395403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25997109376916974249596935 38995664065375461374395403)
            ·
              refine ⟨58493496098063192061593105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38995664065375461374395403 58493496098063192061593105)
              ·
                refine ⟨43870122073547394046194829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58493496098063192061593105 43870122073547394046194829)
                ·
                  refine ⟨16451295777580272767323061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43870122073547394046194829 16451295777580272767323061)
                  ·
                    refine ⟨1542308979148150571936537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16451295777580272767323061 1542308979148150571936537)
                    ·
                      refine ⟨1156731734361112928952403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542308979148150571936537 1156731734361112928952403)
                      ·
                        rfl

theorem cell23_2252727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_2252727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252727 prefixEnd_2252727 := by exact prefixLift 2252727
  have htrace : WordTrace (prefixWord ++ tailWord_2252727) baseStart_2252727 baseEnd_2252727 := by
    simpa [prefixWord, tailWord_2252727, baseEnd_2252727] using wordTrace_append hprefix tailTrace_2252727
  have hstable : (prefixWord ++ tailWord_2252727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252727).length < 2 ^ (prefixWord ++ tailWord_2252727).sum := by decide
  have hdescent : baseEnd_2252727 < baseStart_2252727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252767 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 1, 6]
def baseStart_2252767 : Nat := 118140960795 + 2252767 * 2 ^ 59
def prefixEnd_2252767 : Nat := 4983230072969 + 3 ^ 40 * 2252767 * 2
def baseEnd_2252767 : Nat := 385584091195764257484073

theorem tailTrace_2252767 : CollatzResearch.WordTrace tailWord_2252767 prefixEnd_2252767 385584091195764257484073 := by
  unfold tailWord_2252767
  simp only [CollatzResearch.WordTrace]
  refine ⟨82165162629617375817836555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54776775086411583878557703 82165162629617375817836555)
  ·
    refine ⟨123247743944426063726754833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82165162629617375817836555 123247743944426063726754833)
    ·
      refine ⟨92435807958319547795066125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123247743944426063726754833 92435807958319547795066125)
      ·
        refine ⟨34663427984369830423149797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92435807958319547795066125 34663427984369830423149797)
        ·
          refine ⟨6499392747069343204340587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34663427984369830423149797 6499392747069343204340587)
          ·
            refine ⟨9749089120604014806510881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6499392747069343204340587 9749089120604014806510881)
            ·
              refine ⟨7311816840453011104883161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9749089120604014806510881 7311816840453011104883161)
              ·
                refine ⟨5483862630339758328662371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7311816840453011104883161 5483862630339758328662371)
                ·
                  refine ⟨8225793945509637492993557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5483862630339758328662371 8225793945509637492993557)
                  ·
                    refine ⟨385584091195764257484073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8225793945509637492993557 385584091195764257484073)
                    ·
                      rfl

theorem cell23_2252767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_2252767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252767 prefixEnd_2252767 := by exact prefixLift 2252767
  have htrace : WordTrace (prefixWord ++ tailWord_2252767) baseStart_2252767 baseEnd_2252767 := by
    simpa [prefixWord, tailWord_2252767, baseEnd_2252767] using wordTrace_append hprefix tailTrace_2252767
  have hstable : (prefixWord ++ tailWord_2252767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252767).length < 2 ^ (prefixWord ++ tailWord_2252767).sum := by decide
  have hdescent : baseEnd_2252767 < baseStart_2252767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252771 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 1, 5]
def baseStart_2252771 : Nat := 118140960795 + 2252771 * 2 ^ 59
def prefixEnd_2252771 : Nat := 4983230072969 + 3 ^ 40 * 2252771 * 2
def baseEnd_2252771 : Nat := 385584775836636918934067

theorem tailTrace_2252771 : CollatzResearch.WordTrace tailWord_2252771 prefixEnd_2252771 385584775836636918934067 := by
  unfold tailWord_2252771
  simp only [CollatzResearch.WordTrace]
  refine ⟨82165308521602884500982167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54776872347735256333988111 82165308521602884500982167)
  ·
    refine ⟨123247962782404326751473251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82165308521602884500982167 123247962782404326751473251)
    ·
      refine ⟨184871944173606490127209877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123247962782404326751473251 184871944173606490127209877)
      ·
        refine ⟨8665872383137804224712963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 184871944173606490127209877 8665872383137804224712963)
        ·
          refine ⟨12998808574706706337069445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8665872383137804224712963 12998808574706706337069445)
          ·
            refine ⟨2437276607757507438200521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12998808574706706337069445 2437276607757507438200521)
            ·
              refine ⟨1827957455818130578650391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437276607757507438200521 1827957455818130578650391)
              ·
                refine ⟨2741936183727195867975587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827957455818130578650391 2741936183727195867975587)
                ·
                  refine ⟨4112904275590793801963381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741936183727195867975587 4112904275590793801963381)
                  ·
                    refine ⟨385584775836636918934067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4112904275590793801963381 385584775836636918934067)
                    ·
                      rfl

theorem cell23_2252771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 5].length) (baseStart_2252771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252771 prefixEnd_2252771 := by exact prefixLift 2252771
  have htrace : WordTrace (prefixWord ++ tailWord_2252771) baseStart_2252771 baseEnd_2252771 := by
    simpa [prefixWord, tailWord_2252771, baseEnd_2252771] using wordTrace_append hprefix tailTrace_2252771
  have hstable : (prefixWord ++ tailWord_2252771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252771).length < 2 ^ (prefixWord ++ tailWord_2252771).sum := by decide
  have hdescent : baseEnd_2252771 < baseStart_2252771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252784 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 2, 4]
def baseStart_2252784 : Nat := 118140960795 + 2252784 * 2 ^ 59
def prefixEnd_2252784 : Nat := 4983230072969 + 3 ^ 40 * 2252784 * 2
def baseEnd_2252784 : Nat := 385587000919473068646547

theorem tailTrace_2252784 : CollatzResearch.WordTrace tailWord_2252784 prefixEnd_2252784 385587000919473068646547 := by
  unfold tailWord_2252784
  simp only [CollatzResearch.WordTrace]
  refine ⟨41082891335277893860602703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54777188447037191814136937 41082891335277893860602703)
  ·
    refine ⟨61624337002916840790904055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41082891335277893860602703 61624337002916840790904055)
    ·
      refine ⟨92436505504375261186356083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61624337002916840790904055 92436505504375261186356083)
      ·
        refine ⟨138654758256562891779534125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92436505504375261186356083 138654758256562891779534125)
        ·
          refine ⟨51995534346211084417325297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138654758256562891779534125 51995534346211084417325297)
          ·
            refine ⟨38996650759658313312993973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51995534346211084417325297 38996650759658313312993973)
            ·
              refine ⟨3655936008717966873093185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38996650759658313312993973 3655936008717966873093185)
              ·
                refine ⟨2741952006538475154819889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655936008717966873093185 2741952006538475154819889)
                ·
                  refine ⟨2056464004903856366114917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741952006538475154819889 2056464004903856366114917)
                  ·
                    refine ⟨385587000919473068646547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2056464004903856366114917 385587000919473068646547)
                    ·
                      rfl

theorem cell23_2252784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 4].length) (baseStart_2252784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252784 prefixEnd_2252784 := by exact prefixLift 2252784
  have htrace : WordTrace (prefixWord ++ tailWord_2252784) baseStart_2252784 baseEnd_2252784 := by
    simpa [prefixWord, tailWord_2252784, baseEnd_2252784] using wordTrace_append hprefix tailTrace_2252784
  have hstable : (prefixWord ++ tailWord_2252784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252784).length < 2 ^ (prefixWord ++ tailWord_2252784).sum := by decide
  have hdescent : baseEnd_2252784 < baseStart_2252784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252800 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_2252800 : Nat := 118140960795 + 2252800 * 2 ^ 59
def prefixEnd_2252800 : Nat := 4983230072969 + 3 ^ 40 * 2252800 * 2
def baseEnd_2252800 : Nat := 1156769218448891143339567

theorem tailTrace_2252800 : CollatzResearch.WordTrace tailWord_2252800 prefixEnd_2252800 1156769218448891143339567 := by
  unfold tailWord_2252800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41083183119248911226893927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54777577492331881635858569 41083183119248911226893927)
  ·
    refine ⟨61624774678873366840340891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41083183119248911226893927 61624774678873366840340891)
    ·
      refine ⟨92437162018310050260511337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61624774678873366840340891 92437162018310050260511337)
      ·
        refine ⟨69327871513732537695383503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92437162018310050260511337 69327871513732537695383503)
        ·
          refine ⟨103991807270598806543075255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69327871513732537695383503 103991807270598806543075255)
          ·
            refine ⟨155987710905898209814612883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103991807270598806543075255 155987710905898209814612883)
            ·
              refine ⟨233981566358847314721919325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155987710905898209814612883 233981566358847314721919325)
              ·
                refine ⟨87743087384567743020719747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233981566358847314721919325 87743087384567743020719747)
                ·
                  refine ⟨131614631076851614531079621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87743087384567743020719747 131614631076851614531079621)
                  ·
                    refine ⟨24677743326909677724577429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131614631076851614531079621 24677743326909677724577429)
                    ·
                      refine ⟨1156769218448891143339567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24677743326909677724577429 1156769218448891143339567)
                      ·
                        rfl

theorem cell23_2252800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_2252800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252800 prefixEnd_2252800 := by exact prefixLift 2252800
  have htrace : WordTrace (prefixWord ++ tailWord_2252800) baseStart_2252800 baseEnd_2252800 := by
    simpa [prefixWord, tailWord_2252800, baseEnd_2252800] using wordTrace_append hprefix tailTrace_2252800
  have hstable : (prefixWord ++ tailWord_2252800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252800).length < 2 ^ (prefixWord ++ tailWord_2252800).sum := by decide
  have hdescent : baseEnd_2252800 < baseStart_2252800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252801 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2252801 : Nat := 118140960795 + 2252801 * 2 ^ 59
def prefixEnd_2252801 : Nat := 4983230072969 + 3 ^ 40 * 2252801 * 2
def baseEnd_2252801 : Nat := 385589910643181879809021

theorem tailTrace_2252801 : CollatzResearch.WordTrace tailWord_2252801 prefixEnd_2252801 385589910643181879809021 := by
  unfold tailWord_2252801
  simp only [CollatzResearch.WordTrace]
  refine ⟨82166402711494199624574257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54777601807662799749716171 82166402711494199624574257)
  ·
    refine ⟨61624802033620649718430693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82166402711494199624574257 61624802033620649718430693)
    ·
      refine ⟨11554650381303871822205755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61624802033620649718430693 11554650381303871822205755)
      ·
        refine ⟨17331975571955807733308633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11554650381303871822205755 17331975571955807733308633)
        ·
          refine ⟨12998981678966855799981475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17331975571955807733308633 12998981678966855799981475)
          ·
            refine ⟨19498472518450283699972213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12998981678966855799981475 19498472518450283699972213)
            ·
              refine ⟨1827981798604714096872395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19498472518450283699972213 1827981798604714096872395)
              ·
                refine ⟨2741972697907071145308593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827981798604714096872395 2741972697907071145308593)
                ·
                  refine ⟨2056479523430303358981445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741972697907071145308593 2056479523430303358981445)
                  ·
                    refine ⟨385589910643181879809021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2056479523430303358981445 385589910643181879809021)
                    ·
                      rfl

theorem cell23_2252801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2252801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252801 prefixEnd_2252801 := by exact prefixLift 2252801
  have htrace : WordTrace (prefixWord ++ tailWord_2252801) baseStart_2252801 baseEnd_2252801 := by
    simpa [prefixWord, tailWord_2252801, baseEnd_2252801] using wordTrace_append hprefix tailTrace_2252801
  have hstable : (prefixWord ++ tailWord_2252801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252801).length < 2 ^ (prefixWord ++ tailWord_2252801).sum := by decide
  have hdescent : baseEnd_2252801 < baseStart_2252801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252824 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2252824 : Nat := 118140960795 + 2252824 * 2 ^ 59
def prefixEnd_2252824 : Nat := 4983230072969 + 3 ^ 40 * 2252824 * 2
def baseEnd_2252824 : Nat := 1156781541984599049439457

theorem tailTrace_2252824 : CollatzResearch.WordTrace tailWord_2252824 prefixEnd_2252824 1156781541984599049439457 := by
  unfold tailWord_2252824
  simp only [CollatzResearch.WordTrace]
  refine ⟨41083620795205437276330763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54778161060273916368441017 41083620795205437276330763)
  ·
    refine ⟨61625431192808155914496145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41083620795205437276330763 61625431192808155914496145)
    ·
      refine ⟨46219073394606116935872109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61625431192808155914496145 46219073394606116935872109)
      ·
        refine ⟨17332152522977293850952041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46219073394606116935872109 17332152522977293850952041)
        ·
          refine ⟨12999114392232970388214031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17332152522977293850952041 12999114392232970388214031)
          ·
            refine ⟨19498671588349455582321047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12999114392232970388214031 19498671588349455582321047)
            ·
              refine ⟨29248007382524183373481571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19498671588349455582321047 29248007382524183373481571)
              ·
                refine ⟨43872011073786275060222357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29248007382524183373481571 43872011073786275060222357)
                ·
                  refine ⟨2056500519083731643447923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43872011073786275060222357 2056500519083731643447923)
                  ·
                    refine ⟨3084750778625597465171885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056500519083731643447923 3084750778625597465171885)
                    ·
                      refine ⟨1156781541984599049439457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3084750778625597465171885 1156781541984599049439457)
                      ·
                        rfl

theorem cell23_2252824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2252824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252824 prefixEnd_2252824 := by exact prefixLift 2252824
  have htrace : WordTrace (prefixWord ++ tailWord_2252824) baseStart_2252824 baseEnd_2252824 := by
    simpa [prefixWord, tailWord_2252824, baseEnd_2252824] using wordTrace_append hprefix tailTrace_2252824
  have hstable : (prefixWord ++ tailWord_2252824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252824).length < 2 ^ (prefixWord ++ tailWord_2252824).sum := by decide
  have hdescent : baseEnd_2252824 < baseStart_2252824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252842 : List Nat := [3, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_2252842 : Nat := 118140960795 + 2252842 * 2 ^ 59
def prefixEnd_2252842 : Nat := 4983230072969 + 3 ^ 40 * 2252842 * 2
def baseEnd_2252842 : Nat := 1156790784636379979014375

theorem tailTrace_2252842 : CollatzResearch.WordTrace tailWord_2252842 prefixEnd_2252842 1156790784636379979014375 := by
  unfold tailWord_2252842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20541974526086415906704195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54778598736230442417877853 20541974526086415906704195)
  ·
    refine ⟨30812961789129623860056293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20541974526086415906704195 30812961789129623860056293)
    ·
      refine ⟨5777430335461804473760555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30812961789129623860056293 5777430335461804473760555)
      ·
        refine ⟨8666145503192706710640833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5777430335461804473760555 8666145503192706710640833)
        ·
          refine ⟨6499609127394530032980625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8666145503192706710640833 6499609127394530032980625)
          ·
            refine ⟨4874706845545897524735469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6499609127394530032980625 4874706845545897524735469)
            ·
              refine ⟨1828015067079711571775801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4874706845545897524735469 1828015067079711571775801)
              ·
                refine ⟨1371011300309783678831851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828015067079711571775801 1371011300309783678831851)
                ·
                  refine ⟨2056516950464675518247777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371011300309783678831851 2056516950464675518247777)
                  ·
                    refine ⟨1542387712848506638685833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2056516950464675518247777 1542387712848506638685833)
                    ·
                      refine ⟨1156790784636379979014375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542387712848506638685833 1156790784636379979014375)
                      ·
                        rfl

theorem cell23_2252842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_2252842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252842 prefixEnd_2252842 := by exact prefixLift 2252842
  have htrace : WordTrace (prefixWord ++ tailWord_2252842) baseStart_2252842 baseEnd_2252842 := by
    simpa [prefixWord, tailWord_2252842, baseEnd_2252842] using wordTrace_append hprefix tailTrace_2252842
  have hstable : (prefixWord ++ tailWord_2252842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252842).length < 2 ^ (prefixWord ++ tailWord_2252842).sum := by decide
  have hdescent : baseEnd_2252842 < baseStart_2252842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252852 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2252852 : Nat := 118140960795 + 2252852 * 2 ^ 59
def prefixEnd_2252852 : Nat := 4983230072969 + 3 ^ 40 * 2252852 * 2
def baseEnd_2252852 : Nat := 385598639814308313296443

theorem tailTrace_2252852 : CollatzResearch.WordTrace tailWord_2252852 prefixEnd_2252852 385598639814308313296443 := by
  unfold tailWord_2252852
  simp only [CollatzResearch.WordTrace]
  refine ⟨41084131417154717667340405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54778841889539623556453873 41084131417154717667340405)
  ·
    refine ⟨3851637320358254781313163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41084131417154717667340405 3851637320358254781313163)
    ·
      refine ⟨5777455980537382171969745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3851637320358254781313163 5777455980537382171969745)
      ·
        refine ⟨4333091985403036628977309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5777455980537382171969745 4333091985403036628977309)
        ·
          refine ⟨1624909494526138735866491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4333091985403036628977309 1624909494526138735866491)
          ·
            refine ⟨2437364241789208103799737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624909494526138735866491 2437364241789208103799737)
            ·
              refine ⟨1828023181341906077849803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437364241789208103799737 1828023181341906077849803)
              ·
                refine ⟨2742034772012859116774705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828023181341906077849803 2742034772012859116774705)
                ·
                  refine ⟨2056526079009644337581029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742034772012859116774705 2056526079009644337581029)
                  ·
                    refine ⟨385598639814308313296443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2056526079009644337581029 385598639814308313296443)
                    ·
                      rfl

theorem cell23_2252852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2252852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252852 prefixEnd_2252852 := by exact prefixLift 2252852
  have htrace : WordTrace (prefixWord ++ tailWord_2252852) baseStart_2252852 baseEnd_2252852 := by
    simpa [prefixWord, tailWord_2252852, baseEnd_2252852] using wordTrace_append hprefix tailTrace_2252852
  have hstable : (prefixWord ++ tailWord_2252852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252852).length < 2 ^ (prefixWord ++ tailWord_2252852).sum := by decide
  have hdescent : baseEnd_2252852 < baseStart_2252852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252867 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 3]
def baseStart_2252867 : Nat := 118140960795 + 2252867 * 2 ^ 59
def prefixEnd_2252867 : Nat := 4983230072969 + 3 ^ 40 * 2252867 * 2
def baseEnd_2252867 : Nat := 1156803621652742381201759

theorem tailTrace_2252867 : CollatzResearch.WordTrace tailWord_2252867 prefixEnd_2252867 1156803621652742381201759 := by
  unfold tailWord_2252867
  simp only [CollatzResearch.WordTrace]
  refine ⟨82168809929255092896476855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54779206619503395264317903 82168809929255092896476855)
  ·
    refine ⟨123253214893882639344715283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82168809929255092896476855 123253214893882639344715283)
    ·
      refine ⟨184879822340823959017072925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123253214893882639344715283 184879822340823959017072925)
      ·
        refine ⟨69329933377808984631402347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184879822340823959017072925 69329933377808984631402347)
        ·
          refine ⟨103994900066713476947103521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69329933377808984631402347 103994900066713476947103521)
          ·
            refine ⟨77996175050035107710327641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103994900066713476947103521 77996175050035107710327641)
            ·
              refine ⟨58497131287526330782745731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77996175050035107710327641 58497131287526330782745731)
              ·
                refine ⟨87745696931289496174118597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58497131287526330782745731 87745696931289496174118597)
                ·
                  refine ⟨16452318174616780532647237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87745696931289496174118597 16452318174616780532647237)
                  ·
                    refine ⟨3084809657740646349871357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16452318174616780532647237 3084809657740646349871357)
                    ·
                      refine ⟨1156803621652742381201759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3084809657740646349871357 1156803621652742381201759)
                      ·
                        rfl

theorem cell23_2252867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_2252867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252867 prefixEnd_2252867 := by exact prefixLift 2252867
  have htrace : WordTrace (prefixWord ++ tailWord_2252867) baseStart_2252867 baseEnd_2252867 := by
    simpa [prefixWord, tailWord_2252867, baseEnd_2252867] using wordTrace_append hprefix tailTrace_2252867
  have hstable : (prefixWord ++ tailWord_2252867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252867).length < 2 ^ (prefixWord ++ tailWord_2252867).sum := by decide
  have hdescent : baseEnd_2252867 < baseStart_2252867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2252914 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2252914 : Nat := 118140960795 + 2252914 * 2 ^ 59
def prefixEnd_2252914 : Nat := 4983230072969 + 3 ^ 40 * 2252914 * 2
def baseEnd_2252914 : Nat := 1156827755243503697314043

theorem tailTrace_2252914 : CollatzResearch.WordTrace tailWord_2252914 prefixEnd_2252914 1156827755243503697314043 := by
  unfold tailWord_2252914
  simp only [CollatzResearch.WordTrace]
  refine ⟨20542631040021204980859449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54780349440056546615625197 20542631040021204980859449)
  ·
    refine ⟨15406973280015903735644587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20542631040021204980859449 15406973280015903735644587)
    ·
      refine ⟨23110459920023855603466881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15406973280015903735644587 23110459920023855603466881)
      ·
        refine ⟨17332844940017891702600161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23110459920023855603466881 17332844940017891702600161)
        ·
          refine ⟨12999633705013418776950121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17332844940017891702600161 12999633705013418776950121)
          ·
            refine ⟨9749725278760064082712591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12999633705013418776950121 9749725278760064082712591)
            ·
              refine ⟨14624587918140096124068887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9749725278760064082712591 14624587918140096124068887)
              ·
                refine ⟨21936881877210144186103331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14624587918140096124068887 21936881877210144186103331)
                ·
                  refine ⟨32905322815815216279154997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21936881877210144186103331 32905322815815216279154997)
                  ·
                    refine ⟨3084874013982676526170781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32905322815815216279154997 3084874013982676526170781)
                    ·
                      refine ⟨1156827755243503697314043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3084874013982676526170781 1156827755243503697314043)
                      ·
                        rfl

theorem cell23_2252914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2252914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2252914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2252914 prefixEnd_2252914 := by exact prefixLift 2252914
  have htrace : WordTrace (prefixWord ++ tailWord_2252914) baseStart_2252914 baseEnd_2252914 := by
    simpa [prefixWord, tailWord_2252914, baseEnd_2252914] using wordTrace_append hprefix tailTrace_2252914
  have hstable : (prefixWord ++ tailWord_2252914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2252914).length < 2 ^ (prefixWord ++ tailWord_2252914).sum := by decide
  have hdescent : baseEnd_2252914 < baseStart_2252914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2252914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253024 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 3, 5]
def baseStart_2253024 : Nat := 118140960795 + 2253024 * 2 ^ 59
def prefixEnd_2253024 : Nat := 4983230072969 + 3 ^ 40 * 2253024 * 2
def baseEnd_2253024 : Nat := 385628079371832755646179

theorem tailTrace_2253024 : CollatzResearch.WordTrace tailWord_2253024 prefixEnd_2253024 385628079371832755646179 := by
  unfold tailWord_2253024
  simp only [CollatzResearch.WordTrace]
  refine ⟨41087268094843154354971063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54783024126457539139961417 41087268094843154354971063)
  ·
    refine ⟨61630902142264731532456595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41087268094843154354971063 61630902142264731532456595)
    ·
      refine ⟨92446353213397097298684893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61630902142264731532456595 92446353213397097298684893)
      ·
        refine ⟨34667382455023911487006835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92446353213397097298684893 34667382455023911487006835)
        ·
          refine ⟨52001073682535867230510253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34667382455023911487006835 52001073682535867230510253)
          ·
            refine ⟨19500402630950950211441345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52001073682535867230510253 19500402630950950211441345)
            ·
              refine ⟨14625301973213212658581009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19500402630950950211441345 14625301973213212658581009)
              ·
                refine ⟨10968976479909909493935757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14625301973213212658581009 10968976479909909493935757)
                ·
                  refine ⟨4113366179966216060225909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10968976479909909493935757 4113366179966216060225909)
                  ·
                    refine ⟨385628079371832755646179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4113366179966216060225909 385628079371832755646179)
                    ·
                      rfl

theorem cell23_2253024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_2253024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253024 prefixEnd_2253024 := by exact prefixLift 2253024
  have htrace : WordTrace (prefixWord ++ tailWord_2253024) baseStart_2253024 baseEnd_2253024 := by
    simpa [prefixWord, tailWord_2253024, baseEnd_2253024] using wordTrace_append hprefix tailTrace_2253024
  have hstable : (prefixWord ++ tailWord_2253024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253024).length < 2 ^ (prefixWord ++ tailWord_2253024).sum := by decide
  have hdescent : baseEnd_2253024 < baseStart_2253024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253041 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 1, 5]
def baseStart_2253041 : Nat := 118140960795 + 2253041 * 2 ^ 59
def prefixEnd_2253041 : Nat := 4983230072969 + 3 ^ 40 * 2253041 * 2
def baseEnd_2253041 : Nat := 385630989095541566808653

theorem tailTrace_2253041 : CollatzResearch.WordTrace tailWord_2253041 prefixEnd_2253041 385630989095541566808653 := by
  unfold tailWord_2253041
  simp only [CollatzResearch.WordTrace]
  refine ⟨82175156230624720613310977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54783437487083147075540651 82175156230624720613310977)
  ·
    refine ⟨61631367172968540459983233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82175156230624720613310977 61631367172968540459983233)
    ·
      refine ⟨46223525379726405344987425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61631367172968540459983233 46223525379726405344987425)
      ·
        refine ⟨34667644034794804008740569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46223525379726405344987425 34667644034794804008740569)
        ·
          refine ⟨26000733026096103006555427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34667644034794804008740569 26000733026096103006555427)
          ·
            refine ⟨39001099539144154509833141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26000733026096103006555427 39001099539144154509833141)
            ·
              refine ⟨3656353081794764485296857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39001099539144154509833141 3656353081794764485296857)
              ·
                refine ⟨2742264811346073363972643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3656353081794764485296857 2742264811346073363972643)
                ·
                  refine ⟨4113397217019110045958965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2742264811346073363972643 4113397217019110045958965)
                  ·
                    refine ⟨385630989095541566808653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4113397217019110045958965 385630989095541566808653)
                    ·
                      rfl

theorem cell23_2253041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_2253041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253041 prefixEnd_2253041 := by exact prefixLift 2253041
  have htrace : WordTrace (prefixWord ++ tailWord_2253041) baseStart_2253041 baseEnd_2253041 := by
    simpa [prefixWord, tailWord_2253041, baseEnd_2253041] using wordTrace_append hprefix tailTrace_2253041
  have hstable : (prefixWord ++ tailWord_2253041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253041).length < 2 ^ (prefixWord ++ tailWord_2253041).sum := by decide
  have hdescent : baseEnd_2253041 < baseStart_2253041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253088 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 2, 4]
def baseStart_2253088 : Nat := 118140960795 + 2253088 * 2 ^ 59
def prefixEnd_2253088 : Nat := 4983230072969 + 3 ^ 40 * 2253088 * 2
def baseEnd_2253088 : Nat := 385639033625795338846081

theorem tailTrace_2253088 : CollatzResearch.WordTrace tailWord_2253088 prefixEnd_2253088 385639033625795338846081 := by
  unfold tailWord_2253088
  simp only [CollatzResearch.WordTrace]
  refine ⟨41088435230727223820135959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54784580307636298426847945 41088435230727223820135959)
  ·
    refine ⟨61632652846090835730203939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41088435230727223820135959 61632652846090835730203939)
    ·
      refine ⟨92448979269136253595305909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61632652846090835730203939 92448979269136253595305909)
      ·
        refine ⟨8667091806481523774559929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92448979269136253595305909 8667091806481523774559929)
        ·
          refine ⟨6500318854861142830919947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8667091806481523774559929 6500318854861142830919947)
          ·
            refine ⟨9750478282291714246379921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6500318854861142830919947 9750478282291714246379921)
            ·
              refine ⟨7312858711718785684784941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9750478282291714246379921 7312858711718785684784941)
              ·
                refine ⟨2742322016894544631794353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7312858711718785684784941 2742322016894544631794353)
                ·
                  refine ⟨2056741512670908473845765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742322016894544631794353 2056741512670908473845765)
                  ·
                    refine ⟨385639033625795338846081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2056741512670908473845765 385639033625795338846081)
                    ·
                      rfl

theorem cell23_2253088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 4].length) (baseStart_2253088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253088 prefixEnd_2253088 := by exact prefixLift 2253088
  have htrace : WordTrace (prefixWord ++ tailWord_2253088) baseStart_2253088 baseEnd_2253088 := by
    simpa [prefixWord, tailWord_2253088, baseEnd_2253088] using wordTrace_append hprefix tailTrace_2253088
  have hstable : (prefixWord ++ tailWord_2253088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253088).length < 2 ^ (prefixWord ++ tailWord_2253088).sum := by decide
  have hdescent : baseEnd_2253088 < baseStart_2253088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253091 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 4]
def baseStart_2253091 : Nat := 118140960795 + 2253091 * 2 ^ 59
def prefixEnd_2253091 : Nat := 4983230072969 + 3 ^ 40 * 2253091 * 2
def baseEnd_2253091 : Nat := 1156918641319349504800729

theorem tailTrace_2253091 : CollatzResearch.WordTrace tailWord_2253091 prefixEnd_2253091 1156918641319349504800729 := by
  unfold tailWord_2253091
  simp only [CollatzResearch.WordTrace]
  refine ⟨82176979880443579152631127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54784653253629052768420751 82176979880443579152631127)
  ·
    refine ⟨123265469820665368728946691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82176979880443579152631127 123265469820665368728946691)
    ·
      refine ⟨184898204730998053093420037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123265469820665368728946691 184898204730998053093420037)
      ·
        refine ⟨34668413387062134955016257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184898204730998053093420037 34668413387062134955016257)
        ·
          refine ⟨26001310040296601216262193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34668413387062134955016257 26001310040296601216262193)
          ·
            refine ⟨19500982530222450912196645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26001310040296601216262193 19500982530222450912196645)
            ·
              refine ⟨3656434224416709546036871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19500982530222450912196645 3656434224416709546036871)
              ·
                refine ⟨5484651336625064319055307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656434224416709546036871 5484651336625064319055307)
                ·
                  refine ⟨8226977004937596478582961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5484651336625064319055307 8226977004937596478582961)
                  ·
                    refine ⟨6170232753703197358937221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8226977004937596478582961 6170232753703197358937221)
                    ·
                      refine ⟨1156918641319349504800729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6170232753703197358937221 1156918641319349504800729)
                      ·
                        rfl

theorem cell23_2253091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_2253091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253091 prefixEnd_2253091 := by exact prefixLift 2253091
  have htrace : WordTrace (prefixWord ++ tailWord_2253091) baseStart_2253091 baseEnd_2253091 := by
    simpa [prefixWord, tailWord_2253091, baseEnd_2253091] using wordTrace_append hprefix tailTrace_2253091
  have hstable : (prefixWord ++ tailWord_2253091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253091).length < 2 ^ (prefixWord ++ tailWord_2253091).sum := by decide
  have hdescent : baseEnd_2253091 < baseStart_2253091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253108 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2253108 : Nat := 118140960795 + 2253108 * 2 ^ 59
def prefixEnd_2253108 : Nat := 4983230072969 + 3 ^ 40 * 2253108 * 2
def baseEnd_2253108 : Nat := 1156927370490475938288151

theorem tailTrace_2253108 : CollatzResearch.WordTrace tailWord_2253108 prefixEnd_2253108 1156927370490475938288151 := by
  unfold tailWord_2253108
  simp only [CollatzResearch.WordTrace]
  refine ⟨41088799960690995527999989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54785066614254660703999985 41088799960690995527999989)
  ·
    refine ⟨3852074996314780830749999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41088799960690995527999989 3852074996314780830749999)
    ·
      refine ⟨5778112494472171246124999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852074996314780830749999 5778112494472171246124999)
      ·
        refine ⟨8667168741708256869187499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5778112494472171246124999 8667168741708256869187499)
        ·
          refine ⟨13000753112562385303781249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8667168741708256869187499 13000753112562385303781249)
          ·
            refine ⟨9750564834421788977835937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13000753112562385303781249 9750564834421788977835937)
            ·
              refine ⟨7312923625816341733376953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9750564834421788977835937 7312923625816341733376953)
              ·
                refine ⟨5484692719362256300032715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7312923625816341733376953 5484692719362256300032715)
                ·
                  refine ⟨8227039079043384450049073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5484692719362256300032715 8227039079043384450049073)
                  ·
                    refine ⟨6170279309282538337536805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8227039079043384450049073 6170279309282538337536805)
                    ·
                      refine ⟨1156927370490475938288151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6170279309282538337536805 1156927370490475938288151)
                      ·
                        rfl

theorem cell23_2253108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2253108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253108 prefixEnd_2253108 := by exact prefixLift 2253108
  have htrace : WordTrace (prefixWord ++ tailWord_2253108) baseStart_2253108 baseEnd_2253108 := by
    simpa [prefixWord, tailWord_2253108, baseEnd_2253108] using wordTrace_append hprefix tailTrace_2253108
  have hstable : (prefixWord ++ tailWord_2253108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253108).length < 2 ^ (prefixWord ++ tailWord_2253108).sum := by decide
  have hdescent : baseEnd_2253108 < baseStart_2253108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253138 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_2253138 : Nat := 118140960795 + 2253138 * 2 ^ 59
def prefixEnd_2253138 : Nat := 4983230072969 + 3 ^ 40 * 2253138 * 2
def baseEnd_2253138 : Nat := 1156942774910110820913013

theorem tailTrace_2253138 : CollatzResearch.WordTrace tailWord_2253138 prefixEnd_2253138 1156942774910110820913013 := by
  unfold tailWord_2253138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20544673527818326544898017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54785796074182204119728045 20544673527818326544898017)
  ·
    refine ⟨15408505145863744908673513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20544673527818326544898017 15408505145863744908673513)
    ·
      refine ⟨11556378859397808681505135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15408505145863744908673513 11556378859397808681505135)
      ·
        refine ⟨17334568289096713022257703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11556378859397808681505135 17334568289096713022257703)
        ·
          refine ⟨26001852433645069533386555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17334568289096713022257703 26001852433645069533386555)
          ·
            refine ⟨39002778650467604300079833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26001852433645069533386555 39002778650467604300079833)
            ·
              refine ⟨29252083987850703225059875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39002778650467604300079833 29252083987850703225059875)
              ·
                refine ⟨43878125981776054837589813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29252083987850703225059875 43878125981776054837589813)
                ·
                  refine ⟨4113574310791505141024045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43878125981776054837589813 4113574310791505141024045)
                  ·
                    refine ⟨1542590366546814427884017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4113574310791505141024045 1542590366546814427884017)
                    ·
                      refine ⟨1156942774910110820913013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542590366546814427884017 1156942774910110820913013)
                      ·
                        rfl

theorem cell23_2253138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_2253138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253138 prefixEnd_2253138 := by exact prefixLift 2253138
  have htrace : WordTrace (prefixWord ++ tailWord_2253138) baseStart_2253138 baseEnd_2253138 := by
    simpa [prefixWord, tailWord_2253138, baseEnd_2253138] using wordTrace_append hprefix tailTrace_2253138
  have hstable : (prefixWord ++ tailWord_2253138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253138).length < 2 ^ (prefixWord ++ tailWord_2253138).sum := by decide
  have hdescent : baseEnd_2253138 < baseStart_2253138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253144 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 1, 8]
def baseStart_2253144 : Nat := 118140960795 + 2253144 * 2 ^ 59
def prefixEnd_2253144 : Nat := 4983230072969 + 3 ^ 40 * 2253144 * 2
def baseEnd_2253144 : Nat := 385648618598012599145995

theorem tailTrace_2253144 : CollatzResearch.WordTrace tailWord_2253144 prefixEnd_2253144 385648618598012599145995 := by
  unfold tailWord_2253144
  simp only [CollatzResearch.WordTrace]
  refine ⟨41089456474625784602155243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54785941966167712802873657 41089456474625784602155243)
  ·
    refine ⟨61634184711938676903232865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41089456474625784602155243 61634184711938676903232865)
    ·
      refine ⟨46225638533954007677424649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61634184711938676903232865 46225638533954007677424649)
      ·
        refine ⟨34669228900465505758068487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46225638533954007677424649 34669228900465505758068487)
        ·
          refine ⟨52003843350698258637102731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34669228900465505758068487 52003843350698258637102731)
          ·
            refine ⟨78005765026047387955654097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52003843350698258637102731 78005765026047387955654097)
            ·
              refine ⟨58504323769535540966740573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78005765026047387955654097 58504323769535540966740573)
              ·
                refine ⟨21939121413575827862527715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58504323769535540966740573 21939121413575827862527715)
                ·
                  refine ⟨32908682120363741793791573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21939121413575827862527715 32908682120363741793791573)
                  ·
                    refine ⟨385648618598012599145995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32908682120363741793791573 385648618598012599145995)
                    ·
                      rfl

theorem cell23_2253144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_2253144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253144 prefixEnd_2253144 := by exact prefixLift 2253144
  have htrace : WordTrace (prefixWord ++ tailWord_2253144) baseStart_2253144 baseEnd_2253144 := by
    simpa [prefixWord, tailWord_2253144, baseEnd_2253144] using wordTrace_append hprefix tailTrace_2253144
  have hstable : (prefixWord ++ tailWord_2253144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253144).length < 2 ^ (prefixWord ++ tailWord_2253144).sum := by decide
  have hdescent : baseEnd_2253144 < baseStart_2253144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253155 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 1, 3, 2]
def baseStart_2253155 : Nat := 118140960795 + 2253155 * 2 ^ 59
def prefixEnd_2253155 : Nat := 4983230072969 + 3 ^ 40 * 2253155 * 2
def baseEnd_2253155 : Nat := 1156951504081237254400435

theorem tailTrace_2253155 : CollatzResearch.WordTrace tailWord_2253155 prefixEnd_2253155 1156951504081237254400435 := by
  unfold tailWord_2253155
  simp only [CollatzResearch.WordTrace]
  refine ⟨82179314152211718082960919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54786209434807812055307279 82179314152211718082960919)
  ·
    refine ⟨123268971228317577124441379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82179314152211718082960919 123268971228317577124441379)
    ·
      refine ⟨184903456842476365686662069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123268971228317577124441379 184903456842476365686662069)
      ·
        refine ⟨17334699078982159283124569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 184903456842476365686662069 17334699078982159283124569)
        ·
          refine ⟨13001024309236619462343427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17334699078982159283124569 13001024309236619462343427)
          ·
            refine ⟨19501536463854929193515141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13001024309236619462343427 19501536463854929193515141)
            ·
              refine ⟨3656538086972799223784089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19501536463854929193515141 3656538086972799223784089)
              ·
                refine ⟨2742403565229599417838067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3656538086972799223784089 2742403565229599417838067)
                ·
                  refine ⟨4113605347844399126757101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2742403565229599417838067 4113605347844399126757101)
                  ·
                    refine ⟨1542602005441649672533913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4113605347844399126757101 1542602005441649672533913)
                    ·
                      refine ⟨1156951504081237254400435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542602005441649672533913 1156951504081237254400435)
                      ·
                        rfl

theorem cell23_2253155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_2253155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253155 prefixEnd_2253155 := by exact prefixLift 2253155
  have htrace : WordTrace (prefixWord ++ tailWord_2253155) baseStart_2253155 baseEnd_2253155 := by
    simpa [prefixWord, tailWord_2253155, baseEnd_2253155] using wordTrace_append hprefix tailTrace_2253155
  have hstable : (prefixWord ++ tailWord_2253155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253155).length < 2 ^ (prefixWord ++ tailWord_2253155).sum := by decide
  have hdescent : baseEnd_2253155 < baseStart_2253155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253206 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2253206 : Nat := 118140960795 + 2253206 * 2 ^ 59
def prefixEnd_2253206 : Nat := 4983230072969 + 3 ^ 40 * 2253206 * 2
def baseEnd_2253206 : Nat := 1156977691594616554862701

theorem tailTrace_2253206 : CollatzResearch.WordTrace tailWord_2253206 prefixEnd_2253206 1156977691594616554862701 := by
  unfold tailWord_2253206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5136323392189184612066717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54787449516684635862044981 5136323392189184612066717)
  ·
    refine ⟨1926121272070944229525019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5136323392189184612066717 1926121272070944229525019)
    ·
      refine ⟨2889181908106416344287529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926121272070944229525019 2889181908106416344287529)
      ·
        refine ⟨2166886431079812258215647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2889181908106416344287529 2166886431079812258215647)
        ·
          refine ⟨3250329646619718387323471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166886431079812258215647 3250329646619718387323471)
          ·
            refine ⟨4875494469929577580985207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250329646619718387323471 4875494469929577580985207)
            ·
              refine ⟨7313241704894366371477811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4875494469929577580985207 7313241704894366371477811)
              ·
                refine ⟨10969862557341549557216717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7313241704894366371477811 10969862557341549557216717)
                ·
                  refine ⟨4113698459003081083956269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10969862557341549557216717 4113698459003081083956269)
                  ·
                    refine ⟨1542636922126155406483601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4113698459003081083956269 1542636922126155406483601)
                    ·
                      refine ⟨1156977691594616554862701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542636922126155406483601 1156977691594616554862701)
                      ·
                        rfl

theorem cell23_2253206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2253206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253206 prefixEnd_2253206 := by exact prefixLift 2253206
  have htrace : WordTrace (prefixWord ++ tailWord_2253206) baseStart_2253206 baseEnd_2253206 := by
    simpa [prefixWord, tailWord_2253206, baseEnd_2253206] using wordTrace_append hprefix tailTrace_2253206
  have hstable : (prefixWord ++ tailWord_2253206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253206).length < 2 ^ (prefixWord ++ tailWord_2253206).sum := by decide
  have hdescent : baseEnd_2253206 < baseStart_2253206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253281 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 8]
def baseStart_2253281 : Nat := 118140960795 + 2253281 * 2 ^ 59
def prefixEnd_2253281 : Nat := 4983230072969 + 3 ^ 40 * 2253281 * 2
def baseEnd_2253281 : Nat := 128557355849300417936095

theorem tailTrace_2253281 : CollatzResearch.WordTrace tailWord_2253281 prefixEnd_2253281 128557355849300417936095 := by
  unfold tailWord_2253281
  simp only [CollatzResearch.WordTrace]
  refine ⟨82183909749755241602047697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54789273166503494401365131 82183909749755241602047697)
  ·
    refine ⟨61637932312316431201535773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82183909749755241602047697 61637932312316431201535773)
    ·
      refine ⟨23114224617118661700575915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61637932312316431201535773 23114224617118661700575915)
      ·
        refine ⟨34671336925677992550863873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23114224617118661700575915 34671336925677992550863873)
        ·
          refine ⟨26003502694258494413147905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34671336925677992550863873 26003502694258494413147905)
          ·
            refine ⟨19502627020693870809860929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26003502694258494413147905 19502627020693870809860929)
            ·
              refine ⟨14626970265520403107395697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19502627020693870809860929 14626970265520403107395697)
              ·
                refine ⟨10970227699140302330546773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14626970265520403107395697 10970227699140302330546773)
                ·
                  refine ⟨128557355849300417936095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10970227699140302330546773 128557355849300417936095)
                  ·
                    rfl

theorem cell23_2253281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 8].length) (baseStart_2253281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253281 prefixEnd_2253281 := by exact prefixLift 2253281
  have htrace : WordTrace (prefixWord ++ tailWord_2253281) baseStart_2253281 baseEnd_2253281 := by
    simpa [prefixWord, tailWord_2253281, baseEnd_2253281] using wordTrace_append hprefix tailTrace_2253281
  have hstable : (prefixWord ++ tailWord_2253281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253281).length < 2 ^ (prefixWord ++ tailWord_2253281).sum := by decide
  have hdescent : baseEnd_2253281 < baseStart_2253281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253302 : List Nat := [5, 1, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_2253302 : Nat := 118140960795 + 2253302 * 2 ^ 59
def prefixEnd_2253302 : Nat := 4983230072969 + 3 ^ 40 * 2253302 * 2
def baseEnd_2253302 : Nat := 385675661912482726420753

theorem tailTrace_2253302 : CollatzResearch.WordTrace tailWord_2253302 prefixEnd_2253302 385675661912482726420753 := by
  unfold tailWord_2253302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5136542230167447636785135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54789783788452774792374773 5136542230167447636785135)
  ·
    refine ⟨7704813345251171455177703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5136542230167447636785135 7704813345251171455177703)
    ·
      refine ⟨11557220017876757182766555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7704813345251171455177703 11557220017876757182766555)
      ·
        refine ⟨17335830026815135774149833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11557220017876757182766555 17335830026815135774149833)
        ·
          refine ⟨13001872520111351830612375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17335830026815135774149833 13001872520111351830612375)
          ·
            refine ⟨19502808780167027745918563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13001872520111351830612375 19502808780167027745918563)
            ·
              refine ⟨29254213170250541618877845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19502808780167027745918563 29254213170250541618877845)
              ·
                refine ⟨1371291242355494138384899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29254213170250541618877845 1371291242355494138384899)
                ·
                  refine ⟨2056936863533241207577349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371291242355494138384899 2056936863533241207577349)
                  ·
                    refine ⟨385675661912482726420753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2056936863533241207577349 385675661912482726420753)
                    ·
                      rfl

theorem cell23_2253302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_2253302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253302 prefixEnd_2253302 := by exact prefixLift 2253302
  have htrace : WordTrace (prefixWord ++ tailWord_2253302) baseStart_2253302 baseEnd_2253302 := by
    simpa [prefixWord, tailWord_2253302, baseEnd_2253302] using wordTrace_append hprefix tailTrace_2253302
  have hstable : (prefixWord ++ tailWord_2253302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253302).length < 2 ^ (prefixWord ++ tailWord_2253302).sum := by decide
  have hdescent : baseEnd_2253302 < baseStart_2253302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253352 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_2253352 : Nat := 118140960795 + 2253352 * 2 ^ 59
def prefixEnd_2253352 : Nat := 4983230072969 + 3 ^ 40 * 2253352 * 2
def baseEnd_2253352 : Nat := 1157052659770172983637029

theorem tailTrace_2253352 : CollatzResearch.WordTrace tailWord_2253352 prefixEnd_2253352 1157052659770172983637029 := by
  unfold tailWord_2253352
  simp only [CollatzResearch.WordTrace]
  refine ⟨41093249666249010363941155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54790999554998680485254873 41093249666249010363941155)
  ·
    refine ⟨61639874499373515545911733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41093249666249010363941155 61639874499373515545911733)
    ·
      refine ⟨5778738234316267082429225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61639874499373515545911733 5778738234316267082429225)
      ·
        refine ⟨4334053675737200311821919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5778738234316267082429225 4334053675737200311821919)
        ·
          refine ⟨6501080513605800467732879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4334053675737200311821919 6501080513605800467732879)
          ·
            refine ⟨9751620770408700701599319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6501080513605800467732879 9751620770408700701599319)
            ·
              refine ⟨14627431155613051052398979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9751620770408700701599319 14627431155613051052398979)
              ·
                refine ⟨21941146733419576578598469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14627431155613051052398979 21941146733419576578598469)
                ·
                  refine ⟨4113965012516170608487213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21941146733419576578598469 4113965012516170608487213)
                  ·
                    refine ⟨1542736879693563978182705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4113965012516170608487213 1542736879693563978182705)
                    ·
                      refine ⟨1157052659770172983637029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542736879693563978182705 1157052659770172983637029)
                      ·
                        rfl

theorem cell23_2253352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_2253352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253352 prefixEnd_2253352 := by exact prefixLift 2253352
  have htrace : WordTrace (prefixWord ++ tailWord_2253352) baseStart_2253352 baseEnd_2253352 := by
    simpa [prefixWord, tailWord_2253352, baseEnd_2253352] using wordTrace_append hprefix tailTrace_2253352
  have hstable : (prefixWord ++ tailWord_2253352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253352).length < 2 ^ (prefixWord ++ tailWord_2253352).sum := by decide
  have hdescent : baseEnd_2253352 < baseStart_2253352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253368 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_2253368 : Nat := 118140960795 + 2253368 * 2 ^ 59
def prefixEnd_2253368 : Nat := 4983230072969 + 3 ^ 40 * 2253368 * 2
def baseEnd_2253368 : Nat := 1157060875460644921036955

theorem tailTrace_2253368 : CollatzResearch.WordTrace tailWord_2253368 prefixEnd_2253368 1157060875460644921036955 := by
  unfold tailWord_2253368
  simp only [CollatzResearch.WordTrace]
  refine ⟨41093541450220027730232379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54791388600293370306976505 41093541450220027730232379)
  ·
    refine ⟨61640312175330041595348569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41093541450220027730232379 61640312175330041595348569)
    ·
      refine ⟨46230234131497531196511427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61640312175330041595348569 46230234131497531196511427)
      ·
        refine ⟨69345351197246296794767141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46230234131497531196511427 69345351197246296794767141)
        ·
          refine ⟨13002253349483680649018839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69345351197246296794767141 13002253349483680649018839)
          ·
            refine ⟨19503380024225520973528259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13002253349483680649018839 19503380024225520973528259)
            ·
              refine ⟨29255070036338281460292389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19503380024225520973528259 29255070036338281460292389)
              ·
                refine ⟨5485325631813427773804823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29255070036338281460292389 5485325631813427773804823)
                ·
                  refine ⟨8227988447720141660707235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5485325631813427773804823 8227988447720141660707235)
                  ·
                    refine ⟨12341982671580212491060853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8227988447720141660707235 12341982671580212491060853)
                    ·
                      refine ⟨1157060875460644921036955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12341982671580212491060853 1157060875460644921036955)
                      ·
                        rfl

theorem cell23_2253368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_2253368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253368 prefixEnd_2253368 := by exact prefixLift 2253368
  have htrace : WordTrace (prefixWord ++ tailWord_2253368) baseStart_2253368 baseEnd_2253368 := by
    simpa [prefixWord, tailWord_2253368, baseEnd_2253368] using wordTrace_append hprefix tailTrace_2253368
  have hstable : (prefixWord ++ tailWord_2253368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253368).length < 2 ^ (prefixWord ++ tailWord_2253368).sum := by decide
  have hdescent : baseEnd_2253368 < baseStart_2253368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253375 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 2, 4]
def baseStart_2253375 : Nat := 118140960795 + 2253375 * 2 ^ 59
def prefixEnd_2253375 : Nat := 4983230072969 + 3 ^ 40 * 2253375 * 2
def baseEnd_2253375 : Nat := 385688156608408797883141

theorem tailTrace_2253375 : CollatzResearch.WordTrace tailWord_2253375 prefixEnd_2253375 385688156608408797883141 := by
  unfold tailWord_2253375
  simp only [CollatzResearch.WordTrace]
  refine ⟨82187338211414695655969579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54791558807609797103979719 82187338211414695655969579)
  ·
    refine ⟨123281007317122043483954369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82187338211414695655969579 123281007317122043483954369)
    ·
      refine ⟨92460755487841532612965777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123281007317122043483954369 92460755487841532612965777)
      ·
        refine ⟨69345566615881149459724333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92460755487841532612965777 69345566615881149459724333)
        ·
          refine ⟨26004587480955431047396625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69345566615881149459724333 26004587480955431047396625)
          ·
            refine ⟨19503440610716573285547469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26004587480955431047396625 19503440610716573285547469)
            ·
              refine ⟨7313790229018714982080301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19503440610716573285547469 7313790229018714982080301)
              ·
                refine ⟨2742671335882018118280113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7313790229018714982080301 2742671335882018118280113)
                ·
                  refine ⟨2057003501911513588710085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742671335882018118280113 2057003501911513588710085)
                  ·
                    refine ⟨385688156608408797883141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2057003501911513588710085 385688156608408797883141)
                    ·
                      rfl

theorem cell23_2253375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 4].length) (baseStart_2253375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253375 prefixEnd_2253375 := by exact prefixLift 2253375
  have htrace : WordTrace (prefixWord ++ tailWord_2253375) baseStart_2253375 baseEnd_2253375 := by
    simpa [prefixWord, tailWord_2253375, baseEnd_2253375] using wordTrace_append hprefix tailTrace_2253375
  have hstable : (prefixWord ++ tailWord_2253375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253375).length < 2 ^ (prefixWord ++ tailWord_2253375).sum := by decide
  have hdescent : baseEnd_2253375 < baseStart_2253375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253399 : List Nat := [1, 1, 3, 2, 2, 2, 2, 5, 1, 2, 2]
def baseStart_2253399 : Nat := 118140960795 + 2253399 * 2 ^ 59
def prefixEnd_2253399 : Nat := 4983230072969 + 3 ^ 40 * 2253399 * 2
def baseEnd_2253399 : Nat := 1157076793360934299749313

theorem tailTrace_2253399 : CollatzResearch.WordTrace tailWord_2253399 prefixEnd_2253399 1157076793360934299749313 := by
  unfold tailWord_2253399
  simp only [CollatzResearch.WordTrace]
  refine ⟨82188213563327747754843251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54792142375551831836562167 82188213563327747754843251)
  ·
    refine ⟨123282320344991621632264877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82188213563327747754843251 123282320344991621632264877)
    ·
      refine ⟨46230870129371858112099329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123282320344991621632264877 46230870129371858112099329)
      ·
        refine ⟨34673152597028893584074497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46230870129371858112099329 34673152597028893584074497)
        ·
          refine ⟨26004864447771670188055873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34673152597028893584074497 26004864447771670188055873)
          ·
            refine ⟨19503648335828752641041905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26004864447771670188055873 19503648335828752641041905)
            ·
              refine ⟨14627736251871564480781429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19503648335828752641041905 14627736251871564480781429)
              ·
                refine ⟨1371350273612959170073259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14627736251871564480781429 1371350273612959170073259)
                ·
                  refine ⟨2057025410419438755109889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371350273612959170073259 2057025410419438755109889)
                  ·
                    refine ⟨1542769057814579066332417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2057025410419438755109889 1542769057814579066332417)
                    ·
                      refine ⟨1157076793360934299749313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542769057814579066332417 1157076793360934299749313)
                      ·
                        rfl

theorem cell23_2253399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_2253399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253399 prefixEnd_2253399 := by exact prefixLift 2253399
  have htrace : WordTrace (prefixWord ++ tailWord_2253399) baseStart_2253399 baseEnd_2253399 := by
    simpa [prefixWord, tailWord_2253399, baseEnd_2253399] using wordTrace_append hprefix tailTrace_2253399
  have hstable : (prefixWord ++ tailWord_2253399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253399).length < 2 ^ (prefixWord ++ tailWord_2253399).sum := by decide
  have hdescent : baseEnd_2253399 < baseStart_2253399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253410 : List Nat := [3, 3, 2, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2253410 : Nat := 118140960795 + 2253410 * 2 ^ 59
def prefixEnd_2253410 : Nat := 4983230072969 + 3 ^ 40 * 2253410 * 2
def baseEnd_2253410 : Nat := 1157082441648133756711763

theorem tailTrace_2253410 : CollatzResearch.WordTrace tailWord_2253410 prefixEnd_2253410 1157082441648133756711763 := by
  unfold tailWord_2253410
  simp only [CollatzResearch.WordTrace]
  refine ⟨20547153691571974158373421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54792409844191931088995789 20547153691571974158373421)
  ·
    refine ⟨7705182634339490309390033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20547153691571974158373421 7705182634339490309390033)
    ·
      refine ⟨5778886975754617732042525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7705182634339490309390033 5778886975754617732042525)
      ·
        refine ⟨2167082615907981649515947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5778886975754617732042525 2167082615907981649515947)
        ·
          refine ⟨3250623923861972474273921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167082615907981649515947 3250623923861972474273921)
          ·
            refine ⟨2437967942896479355705441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3250623923861972474273921 2437967942896479355705441)
            ·
              refine ⟨1828475957172359516779081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437967942896479355705441 1828475957172359516779081)
              ·
                refine ⟨1371356967879269637584311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828475957172359516779081 1371356967879269637584311)
                ·
                  refine ⟨2057035451818904456376467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371356967879269637584311 2057035451818904456376467)
                  ·
                    refine ⟨3085553177728356684564701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2057035451818904456376467 3085553177728356684564701)
                    ·
                      refine ⟨1157082441648133756711763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3085553177728356684564701 1157082441648133756711763)
                      ·
                        rfl

theorem cell23_2253410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2253410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253410 prefixEnd_2253410 := by exact prefixLift 2253410
  have htrace : WordTrace (prefixWord ++ tailWord_2253410) baseStart_2253410 baseEnd_2253410 := by
    simpa [prefixWord, tailWord_2253410, baseEnd_2253410] using wordTrace_append hprefix tailTrace_2253410
  have hstable : (prefixWord ++ tailWord_2253410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253410).length < 2 ^ (prefixWord ++ tailWord_2253410).sum := by decide
  have hdescent : baseEnd_2253410 < baseStart_2253410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253418 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_2253418 : Nat := 118140960795 + 2253418 * 2 ^ 59
def prefixEnd_2253418 : Nat := 4983230072969 + 3 ^ 40 * 2253418 * 2
def baseEnd_2253418 : Nat := 385695516497789908470575

theorem tailTrace_2253418 : CollatzResearch.WordTrace tailWord_2253418 prefixEnd_2253418 385695516497789908470575 := by
  unfold tailWord_2253418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20547226637564728499946227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54792604366839275999856605 20547226637564728499946227)
  ·
    refine ⟨30820839956347092749919341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20547226637564728499946227 30820839956347092749919341)
    ·
      refine ⟨11557814983630159781219753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30820839956347092749919341 11557814983630159781219753)
      ·
        refine ⟨8668361237722619835914815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11557814983630159781219753 8668361237722619835914815)
        ·
          refine ⟨13002541856583929753872223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8668361237722619835914815 13002541856583929753872223)
          ·
            refine ⟨19503812784875894630808335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13002541856583929753872223 19503812784875894630808335)
            ·
              refine ⟨29255719177313841946212503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19503812784875894630808335 29255719177313841946212503)
              ·
                refine ⟨43883578765970762919318755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29255719177313841946212503 43883578765970762919318755)
                ·
                  refine ⟨65825368148956144378978133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43883578765970762919318755 65825368148956144378978133)
                  ·
                    refine ⟨385695516497789908470575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 65825368148956144378978133 385695516497789908470575)
                    ·
                      rfl

theorem cell23_2253418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_2253418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253418 prefixEnd_2253418 := by exact prefixLift 2253418
  have htrace : WordTrace (prefixWord ++ tailWord_2253418) baseStart_2253418 baseEnd_2253418 := by
    simpa [prefixWord, tailWord_2253418, baseEnd_2253418] using wordTrace_append hprefix tailTrace_2253418
  have hstable : (prefixWord ++ tailWord_2253418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253418).length < 2 ^ (prefixWord ++ tailWord_2253418).sum := by decide
  have hdescent : baseEnd_2253418 < baseStart_2253418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253512 : List Nat := [2, 1, 3, 1, 2, 3, 3, 3, 5]
def baseStart_2253512 : Nat := 118140960795 + 2253512 * 2 ^ 59
def prefixEnd_2253512 : Nat := 4983230072969 + 3 ^ 40 * 2253512 * 2
def baseEnd_2253512 : Nat := 128570535186099150848477

theorem tailTrace_2253512 : CollatzResearch.WordTrace tailWord_2253512 prefixEnd_2253512 128570535186099150848477 := by
  unfold tailWord_2253512
  simp only [CollatzResearch.WordTrace]
  refine ⟨41096167505959184026853395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54794890007945578702471193 41096167505959184026853395)
  ·
    refine ⟨61644251258938776040280093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41096167505959184026853395 61644251258938776040280093)
    ·
      refine ⟨23116594222102041015105035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61644251258938776040280093 23116594222102041015105035)
      ·
        refine ⟨34674891333153061522657553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23116594222102041015105035 34674891333153061522657553)
        ·
          refine ⟨26006168499864796141993165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34674891333153061522657553 26006168499864796141993165)
          ·
            refine ⟨9752313187449298553247437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26006168499864796141993165 9752313187449298553247437)
            ·
              refine ⟨3657117445293486957467789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9752313187449298553247437 3657117445293486957467789)
              ·
                refine ⟨1371419041985057609050421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3657117445293486957467789 1371419041985057609050421)
                ·
                  refine ⟨128570535186099150848477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1371419041985057609050421 128570535186099150848477)
                  ·
                    rfl

theorem cell23_2253512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 5].length) (baseStart_2253512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253512 prefixEnd_2253512 := by exact prefixLift 2253512
  have htrace : WordTrace (prefixWord ++ tailWord_2253512) baseStart_2253512 baseEnd_2253512 := by
    simpa [prefixWord, tailWord_2253512, baseEnd_2253512] using wordTrace_append hprefix tailTrace_2253512
  have hstable : (prefixWord ++ tailWord_2253512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253512).length < 2 ^ (prefixWord ++ tailWord_2253512).sum := by decide
  have hdescent : baseEnd_2253512 < baseStart_2253512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253515 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 3, 7, 2]
def baseStart_2253515 : Nat := 118140960795 + 2253515 * 2 ^ 59
def prefixEnd_2253515 : Nat := 4983230072969 + 3 ^ 40 * 2253515 * 2
def baseEnd_2253515 : Nat := 1157136357116855845898779

theorem tailTrace_2253515 : CollatzResearch.WordTrace tailWord_2253515 prefixEnd_2253515 1157136357116855845898779 := by
  unfold tailWord_2253515
  simp only [CollatzResearch.WordTrace]
  refine ⟨82192444430907499566065999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54794962953938333044043999 82192444430907499566065999)
  ·
    refine ⟨123288666646361249349098999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82192444430907499566065999 123288666646361249349098999)
    ·
      refine ⟨184932999969541874023648499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123288666646361249349098999 184932999969541874023648499)
      ·
        refine ⟨277399499954312811035472749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184932999969541874023648499 277399499954312811035472749)
        ·
          refine ⟨104024812482867304138302281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277399499954312811035472749 104024812482867304138302281)
          ·
            refine ⟨78018609362150478103726711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104024812482867304138302281 78018609362150478103726711)
            ·
              refine ⟨117027914043225717155590067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78018609362150478103726711 117027914043225717155590067)
              ·
                refine ⟨175541871064838575733385101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117027914043225717155590067 175541871064838575733385101)
                ·
                  refine ⟨65828201649314465900019413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175541871064838575733385101 65828201649314465900019413)
                  ·
                    refine ⟨1542848476155807794531705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65828201649314465900019413 1542848476155807794531705)
                    ·
                      refine ⟨1157136357116855845898779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542848476155807794531705 1157136357116855845898779)
                      ·
                        rfl

theorem cell23_2253515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 7, 2].length) (baseStart_2253515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253515 prefixEnd_2253515 := by exact prefixLift 2253515
  have htrace : WordTrace (prefixWord ++ tailWord_2253515) baseStart_2253515 baseEnd_2253515 := by
    simpa [prefixWord, tailWord_2253515, baseEnd_2253515] using wordTrace_append hprefix tailTrace_2253515
  have hstable : (prefixWord ++ tailWord_2253515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253515).length < 2 ^ (prefixWord ++ tailWord_2253515).sum := by decide
  have hdescent : baseEnd_2253515 < baseStart_2253515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253535 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_2253535 : Nat := 118140960795 + 2253535 * 2 ^ 59
def prefixEnd_2253535 : Nat := 4983230072969 + 3 ^ 40 * 2253535 * 2
def baseEnd_2253535 : Nat := 1157146626729945767648687

theorem tailTrace_2253535 : CollatzResearch.WordTrace tailWord_2253535 prefixEnd_2253535 1157146626729945767648687 := by
  unfold tailWord_2253535
  simp only [CollatzResearch.WordTrace]
  refine ⟨82193173890835042981794059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54795449260556695321196039 82193173890835042981794059)
  ·
    refine ⟨123289760836252564472691089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82193173890835042981794059 123289760836252564472691089)
    ·
      refine ⟨92467320627189423354518317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123289760836252564472691089 92467320627189423354518317)
      ·
        refine ⟨34675245235196033757944369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92467320627189423354518317 34675245235196033757944369)
        ·
          refine ⟨26006433926397025318458277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34675245235196033757944369 26006433926397025318458277)
          ·
            refine ⟨4876206361199442247210927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26006433926397025318458277 4876206361199442247210927)
            ·
              refine ⟨7314309541799163370816391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4876206361199442247210927 7314309541799163370816391)
              ·
                refine ⟨10971464312698745056224587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7314309541799163370816391 10971464312698745056224587)
                ·
                  refine ⟨16457196469048117584336881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10971464312698745056224587 16457196469048117584336881)
                  ·
                    refine ⟨12342897351786088188252661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16457196469048117584336881 12342897351786088188252661)
                    ·
                      refine ⟨1157146626729945767648687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12342897351786088188252661 1157146626729945767648687)
                      ·
                        rfl

theorem cell23_2253535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_2253535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253535 prefixEnd_2253535 := by exact prefixLift 2253535
  have htrace : WordTrace (prefixWord ++ tailWord_2253535) baseStart_2253535 baseEnd_2253535 := by
    simpa [prefixWord, tailWord_2253535, baseEnd_2253535] using wordTrace_append hprefix tailTrace_2253535
  have hstable : (prefixWord ++ tailWord_2253535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253535).length < 2 ^ (prefixWord ++ tailWord_2253535).sum := by decide
  have hdescent : baseEnd_2253535 < baseStart_2253535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253555 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 5, 4]
def baseStart_2253555 : Nat := 118140960795 + 2253555 * 2 ^ 59
def prefixEnd_2253555 : Nat := 4983230072969 + 3 ^ 40 * 2253555 * 2
def baseEnd_2253555 : Nat := 385718965447678563132865

theorem tailTrace_2253555 : CollatzResearch.WordTrace tailWord_2253555 prefixEnd_2253555 385718965447678563132865 := by
  unfold tailWord_2253555
  simp only [CollatzResearch.WordTrace]
  refine ⟨82193903350762586397522119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54795935567175057598348079 82193903350762586397522119)
  ·
    refine ⟨123290855026143879596283179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82193903350762586397522119 123290855026143879596283179)
    ·
      refine ⟨184936282539215819394424769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123290855026143879596283179 184936282539215819394424769)
      ·
        refine ⟨138702211904411864545818577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184936282539215819394424769 138702211904411864545818577)
        ·
          refine ⟨104026658928308898409363933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138702211904411864545818577 104026658928308898409363933)
          ·
            refine ⟨39009997098115836903511475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104026658928308898409363933 39009997098115836903511475)
            ·
              refine ⟨58514995647173755355267213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39009997098115836903511475 58514995647173755355267213)
              ·
                refine ⟨21943123367690158258225205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58514995647173755355267213 21943123367690158258225205)
                ·
                  refine ⟨2057167815720952336708613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21943123367690158258225205 2057167815720952336708613)
                  ·
                    refine ⟨385718965447678563132865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2057167815720952336708613 385718965447678563132865)
                    ·
                      rfl

theorem cell23_2253555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 4].length) (baseStart_2253555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253555 prefixEnd_2253555 := by exact prefixLift 2253555
  have htrace : WordTrace (prefixWord ++ tailWord_2253555) baseStart_2253555 baseEnd_2253555 := by
    simpa [prefixWord, tailWord_2253555, baseEnd_2253555] using wordTrace_append hprefix tailTrace_2253555
  have hstable : (prefixWord ++ tailWord_2253555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253555).length < 2 ^ (prefixWord ++ tailWord_2253555).sum := by decide
  have hdescent : baseEnd_2253555 < baseStart_2253555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253585 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 6]
def baseStart_2253585 : Nat := 118140960795 + 2253585 * 2 ^ 59
def prefixEnd_2253585 : Nat := 4983230072969 + 3 ^ 40 * 2253585 * 2
def baseEnd_2253585 : Nat := 128574700084741174669273

theorem tailTrace_2253585 : CollatzResearch.WordTrace tailWord_2253585 prefixEnd_2253585 128574700084741174669273 := by
  unfold tailWord_2253585
  simp only [CollatzResearch.WordTrace]
  refine ⟨82194997540653901521114209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54796665027102601014076139 82194997540653901521114209)
  ·
    refine ⟨61646248155490426140835657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82194997540653901521114209 61646248155490426140835657)
    ·
      refine ⟨46234686116617819605626743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61646248155490426140835657 46234686116617819605626743)
      ·
        refine ⟨69352029174926729408440115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46234686116617819605626743 69352029174926729408440115)
        ·
          refine ⟨104028043762390094112660173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69352029174926729408440115 104028043762390094112660173)
          ·
            refine ⟨39010516410896285292247565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104028043762390094112660173 39010516410896285292247565)
            ·
              refine ⟨14628943654086106984592837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39010516410896285292247565 14628943654086106984592837)
              ·
                refine ⟨2742926935141145059611157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14628943654086106984592837 2742926935141145059611157)
                ·
                  refine ⟨128574700084741174669273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2742926935141145059611157 128574700084741174669273)
                  ·
                    rfl

theorem cell23_2253585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 6].length) (baseStart_2253585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253585 prefixEnd_2253585 := by exact prefixLift 2253585
  have htrace : WordTrace (prefixWord ++ tailWord_2253585) baseStart_2253585 baseEnd_2253585 := by
    simpa [prefixWord, tailWord_2253585, baseEnd_2253585] using wordTrace_append hprefix tailTrace_2253585
  have hstable : (prefixWord ++ tailWord_2253585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253585).length < 2 ^ (prefixWord ++ tailWord_2253585).sum := by decide
  have hdescent : baseEnd_2253585 < baseStart_2253585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253589 : List Nat := [1, 3, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_2253589 : Nat := 118140960795 + 2253589 * 2 ^ 59
def prefixEnd_2253589 : Nat := 4983230072969 + 3 ^ 40 * 2253589 * 2
def baseEnd_2253589 : Nat := 385724784895096185457813

theorem tailTrace_2253589 : CollatzResearch.WordTrace tailWord_2253589 prefixEnd_2253589 385724784895096185457813 := by
  unfold tailWord_2253589
  simp only [CollatzResearch.WordTrace]
  refine ⟨82195143432639410204259821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54796762288426273469506547 82195143432639410204259821)
  ·
    refine ⟨30823178787239778826597433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82195143432639410204259821 30823178787239778826597433)
    ·
      refine ⟨23117384090429834119948075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30823178787239778826597433 23117384090429834119948075)
      ·
        refine ⟨34676076135644751179922113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23117384090429834119948075 34676076135644751179922113)
        ·
          refine ⟨26007057101733563384941585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34676076135644751179922113 26007057101733563384941585)
          ·
            refine ⟨19505292826300172538706189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26007057101733563384941585 19505292826300172538706189)
            ·
              refine ⟨7314484809862564702014821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19505292826300172538706189 7314484809862564702014821)
              ·
                refine ⟨1371465901849230881627779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7314484809862564702014821 1371465901849230881627779)
                ·
                  refine ⟨2057198852773846322441669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371465901849230881627779 2057198852773846322441669)
                  ·
                    refine ⟨385724784895096185457813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2057198852773846322441669 385724784895096185457813)
                    ·
                      rfl

theorem cell23_2253589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_2253589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253589 prefixEnd_2253589 := by exact prefixLift 2253589
  have htrace : WordTrace (prefixWord ++ tailWord_2253589) baseStart_2253589 baseEnd_2253589 := by
    simpa [prefixWord, tailWord_2253589, baseEnd_2253589] using wordTrace_append hprefix tailTrace_2253589
  have hstable : (prefixWord ++ tailWord_2253589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253589).length < 2 ^ (prefixWord ++ tailWord_2253589).sum := by decide
  have hdescent : baseEnd_2253589 < baseStart_2253589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253602 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 6]
def baseStart_2253602 : Nat := 118140960795 + 2253602 * 2 ^ 59
def prefixEnd_2253602 : Nat := 4983230072969 + 3 ^ 40 * 2253602 * 2
def baseEnd_2253602 : Nat := 128575669992644111723431

theorem tailTrace_2253602 : CollatzResearch.WordTrace tailWord_2253602 prefixEnd_2253602 128575669992644111723431 := by
  unfold tailWord_2253602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20548904395398078356120765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54797078387728208949655373 20548904395398078356120765)
  ·
    refine ⟨7705839148274279383545287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20548904395398078356120765 7705839148274279383545287)
    ·
      refine ⟨11558758722411419075317931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7705839148274279383545287 11558758722411419075317931)
      ·
        refine ⟨17338138083617128612976897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11558758722411419075317931 17338138083617128612976897)
        ·
          refine ⟨13003603562712846459732673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17338138083617128612976897 13003603562712846459732673)
          ·
            refine ⟨9752702672034634844799505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13003603562712846459732673 9752702672034634844799505)
            ·
              refine ⟨7314527004025976133599629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9752702672034634844799505 7314527004025976133599629)
              ·
                refine ⟨2742947626509741050099861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7314527004025976133599629 2742947626509741050099861)
                ·
                  refine ⟨128575669992644111723431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2742947626509741050099861 128575669992644111723431)
                  ·
                    rfl

theorem cell23_2253602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_2253602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253602 prefixEnd_2253602 := by exact prefixLift 2253602
  have htrace : WordTrace (prefixWord ++ tailWord_2253602) baseStart_2253602 baseEnd_2253602 := by
    simpa [prefixWord, tailWord_2253602, baseEnd_2253602] using wordTrace_append hprefix tailTrace_2253602
  have hstable : (prefixWord ++ tailWord_2253602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253602).length < 2 ^ (prefixWord ++ tailWord_2253602).sum := by decide
  have hdescent : baseEnd_2253602 < baseStart_2253602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253613 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2253613 : Nat := 118140960795 + 2253613 * 2 ^ 59
def prefixEnd_2253613 : Nat := 4983230072969 + 3 ^ 40 * 2253613 * 2
def baseEnd_2253613 : Nat := 1157186678220996462473329

theorem tailTrace_2253613 : CollatzResearch.WordTrace tailWord_2253613 prefixEnd_2253613 1157186678220996462473329 := by
  unfold tailWord_2253613
  simp only [CollatzResearch.WordTrace]
  refine ⟨82196018784552462303133493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54797345856368308202088995 82196018784552462303133493)
  ·
    refine ⟨7705876761051793340918765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82196018784552462303133493 7705876761051793340918765)
    ·
      refine ⟨2889703785394422502844537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7705876761051793340918765 2889703785394422502844537)
      ·
        refine ⟨2167277839045816877133403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2889703785394422502844537 2167277839045816877133403)
        ·
          refine ⟨3250916758568725315700105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167277839045816877133403 3250916758568725315700105)
          ·
            refine ⟨2438187568926543986775079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3250916758568725315700105 2438187568926543986775079)
            ·
              refine ⟨3657281353389815980162619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438187568926543986775079 3657281353389815980162619)
              ·
                refine ⟨5485922030084723970243929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3657281353389815980162619 5485922030084723970243929)
                ·
                  refine ⟨4114441522563542977682947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5485922030084723970243929 4114441522563542977682947)
                  ·
                    refine ⟨6171662283845314466524421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4114441522563542977682947 6171662283845314466524421)
                    ·
                      refine ⟨1157186678220996462473329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6171662283845314466524421 1157186678220996462473329)
                      ·
                        rfl

theorem cell23_2253613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2253613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253613 prefixEnd_2253613 := by exact prefixLift 2253613
  have htrace : WordTrace (prefixWord ++ tailWord_2253613) baseStart_2253613 baseEnd_2253613 := by
    simpa [prefixWord, tailWord_2253613, baseEnd_2253613] using wordTrace_append hprefix tailTrace_2253613
  have hstable : (prefixWord ++ tailWord_2253613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253613).length < 2 ^ (prefixWord ++ tailWord_2253613).sum := by decide
  have hdescent : baseEnd_2253613 < baseStart_2253613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253666 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2253666 : Nat := 118140960795 + 2253666 * 2 ^ 59
def prefixEnd_2253666 : Nat := 4983230072969 + 3 ^ 40 * 2253666 * 2
def baseEnd_2253666 : Nat := 385737964231894918370195

theorem tailTrace_2253666 : CollatzResearch.WordTrace tailWord_2253666 prefixEnd_2253666 385737964231894918370195 := by
  unfold tailWord_2253666
  simp only [CollatzResearch.WordTrace]
  refine ⟨20549487963340113088703213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54798634568906968236541901 20549487963340113088703213)
  ·
    refine ⟨7706057986252542408263705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20549487963340113088703213 7706057986252542408263705)
    ·
      refine ⟨5779543489689406806197779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7706057986252542408263705 5779543489689406806197779)
      ·
        refine ⟨8669315234534110209296669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5779543489689406806197779 8669315234534110209296669)
        ·
          refine ⟨3250993212950291328486251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8669315234534110209296669 3250993212950291328486251)
          ·
            refine ⟨4876489819425436992729377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250993212950291328486251 4876489819425436992729377)
            ·
              refine ⟨3657367364569077744547033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4876489819425436992729377 3657367364569077744547033)
              ·
                refine ⟨2743025523426808308410275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3657367364569077744547033 2743025523426808308410275)
                ·
                  refine ⟨4114538285140212462615413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743025523426808308410275 4114538285140212462615413)
                  ·
                    refine ⟨385737964231894918370195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4114538285140212462615413 385737964231894918370195)
                    ·
                      rfl

theorem cell23_2253666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2253666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253666 prefixEnd_2253666 := by exact prefixLift 2253666
  have htrace : WordTrace (prefixWord ++ tailWord_2253666) baseStart_2253666 baseEnd_2253666 := by
    simpa [prefixWord, tailWord_2253666, baseEnd_2253666] using wordTrace_append hprefix tailTrace_2253666
  have hstable : (prefixWord ++ tailWord_2253666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253666).length < 2 ^ (prefixWord ++ tailWord_2253666).sum := by decide
  have hdescent : baseEnd_2253666 < baseStart_2253666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253682 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2253682 : Nat := 118140960795 + 2253682 * 2 ^ 59
def prefixEnd_2253682 : Nat := 4983230072969 + 3 ^ 40 * 2253682 * 2
def baseEnd_2253682 : Nat := 1157222108386156692510511

theorem tailTrace_2253682 : CollatzResearch.WordTrace tailWord_2253682 prefixEnd_2253682 1157222108386156692510511 := by
  unfold tailWord_2253682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20549633855325621771848825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54799023614201658058263533 20549633855325621771848825)
  ·
    refine ⟨15412225391494216328886619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20549633855325621771848825 15412225391494216328886619)
    ·
      refine ⟨23118338087241324493329929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15412225391494216328886619 23118338087241324493329929)
      ·
        refine ⟨17338753565430993369997447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23118338087241324493329929 17338753565430993369997447)
        ·
          refine ⟨26008130348146490054996171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17338753565430993369997447 26008130348146490054996171)
          ·
            refine ⟨39012195522219735082494257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26008130348146490054996171 39012195522219735082494257)
            ·
              refine ⟨29259146641664801311870693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39012195522219735082494257 29259146641664801311870693)
              ·
                refine ⟨5486089995312150245975755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29259146641664801311870693 5486089995312150245975755)
                ·
                  refine ⟨8229134992968225368963633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5486089995312150245975755 8229134992968225368963633)
                  ·
                    refine ⟨6171851244726169026722725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8229134992968225368963633 6171851244726169026722725)
                    ·
                      refine ⟨1157222108386156692510511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6171851244726169026722725 1157222108386156692510511)
                      ·
                        rfl

theorem cell23_2253682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2253682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253682 prefixEnd_2253682 := by exact prefixLift 2253682
  have htrace : WordTrace (prefixWord ++ tailWord_2253682) baseStart_2253682 baseEnd_2253682 := by
    simpa [prefixWord, tailWord_2253682, baseEnd_2253682] using wordTrace_append hprefix tailTrace_2253682
  have hstable : (prefixWord ++ tailWord_2253682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253682).length < 2 ^ (prefixWord ++ tailWord_2253682).sum := by decide
  have hdescent : baseEnd_2253682 < baseStart_2253682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253686 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2253686 : Nat := 118140960795 + 2253686 * 2 ^ 59
def prefixEnd_2253686 : Nat := 4983230072969 + 3 ^ 40 * 2253686 * 2
def baseEnd_2253686 : Nat := 1157224162308774676860493

theorem tailTrace_2253686 : CollatzResearch.WordTrace tailWord_2253686 prefixEnd_2253686 1157224162308774676860493 := by
  unfold tailWord_2253686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137417582080499735658807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54799120875525330513693941 5137417582080499735658807)
  ·
    refine ⟨7706126373120749603488211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5137417582080499735658807 7706126373120749603488211)
    ·
      refine ⟨11559189559681124405232317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7706126373120749603488211 11559189559681124405232317)
      ·
        refine ⟨4334696084880421651962119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11559189559681124405232317 4334696084880421651962119)
        ·
          refine ⟨6502044127320632477943179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4334696084880421651962119 6502044127320632477943179)
          ·
            refine ⟨9753066190980948716914769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502044127320632477943179 9753066190980948716914769)
            ·
              refine ⟨7314799643235711537686077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9753066190980948716914769 7314799643235711537686077)
              ·
                refine ⟨2743049866213391826632279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7314799643235711537686077 2743049866213391826632279)
                ·
                  refine ⟨4114574799320087739948419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743049866213391826632279 4114574799320087739948419)
                  ·
                    refine ⟨6171862198980131609922629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4114574799320087739948419 6171862198980131609922629)
                    ·
                      refine ⟨1157224162308774676860493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6171862198980131609922629 1157224162308774676860493)
                      ·
                        rfl

theorem cell23_2253686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2253686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253686 prefixEnd_2253686 := by exact prefixLift 2253686
  have htrace : WordTrace (prefixWord ++ tailWord_2253686) baseStart_2253686 baseEnd_2253686 := by
    simpa [prefixWord, tailWord_2253686, baseEnd_2253686] using wordTrace_append hprefix tailTrace_2253686
  have hstable : (prefixWord ++ tailWord_2253686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253686).length < 2 ^ (prefixWord ++ tailWord_2253686).sum := by decide
  have hdescent : baseEnd_2253686 < baseStart_2253686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253689 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 3]
def baseStart_2253689 : Nat := 118140960795 + 2253689 * 2 ^ 59
def prefixEnd_2253689 : Nat := 4983230072969 + 3 ^ 40 * 2253689 * 2
def baseEnd_2253689 : Nat := 1157225702750738165122979

theorem tailTrace_2253689 : CollatzResearch.WordTrace tailWord_2253689 prefixEnd_2253689 1157225702750738165122979 := by
  unfold tailWord_2253689
  simp only [CollatzResearch.WordTrace]
  refine ⟨82198790732277127282900121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54799193821518084855266747 82198790732277127282900121)
  ·
    refine ⟨61649093049207845462175091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82198790732277127282900121 61649093049207845462175091)
    ·
      refine ⟨92473639573811768193262637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61649093049207845462175091 92473639573811768193262637)
      ·
        refine ⟨34677614840179413072473489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92473639573811768193262637 34677614840179413072473489)
        ·
          refine ⟨26008211130134559804355117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34677614840179413072473489 26008211130134559804355117)
          ·
            refine ⟨9753079173800459926633169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26008211130134559804355117 9753079173800459926633169)
            ·
              refine ⟨7314809380350344944974877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9753079173800459926633169 7314809380350344944974877)
              ·
                refine ⟨2743053517631379354365579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7314809380350344944974877 2743053517631379354365579)
                ·
                  refine ⟨4114580276447069031548369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743053517631379354365579 4114580276447069031548369)
                  ·
                    refine ⟨3085935207335301773661277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4114580276447069031548369 3085935207335301773661277)
                    ·
                      refine ⟨1157225702750738165122979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3085935207335301773661277 1157225702750738165122979)
                      ·
                        rfl

theorem cell23_2253689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_2253689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253689 prefixEnd_2253689 := by exact prefixLift 2253689
  have htrace : WordTrace (prefixWord ++ tailWord_2253689) baseStart_2253689 baseEnd_2253689 := by
    simpa [prefixWord, tailWord_2253689, baseEnd_2253689] using wordTrace_append hprefix tailTrace_2253689
  have hstable : (prefixWord ++ tailWord_2253689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253689).length < 2 ^ (prefixWord ++ tailWord_2253689).sum := by decide
  have hdescent : baseEnd_2253689 < baseStart_2253689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253703 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_2253703 : Nat := 118140960795 + 2253703 * 2 ^ 59
def prefixEnd_2253703 : Nat := 4983230072969 + 3 ^ 40 * 2253703 * 2
def baseEnd_2253703 : Nat := 1157232891479901110347915

theorem tailTrace_2253703 : CollatzResearch.WordTrace tailWord_2253703 prefixEnd_2253703 1157232891479901110347915 := by
  unfold tailWord_2253703
  simp only [CollatzResearch.WordTrace]
  refine ⟨82199301354226407673909763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54799534236150938449273175 82199301354226407673909763)
  ·
    refine ⟨123298952031339611510864645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82199301354226407673909763 123298952031339611510864645)
    ·
      refine ⟨23118553505876177158287121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123298952031339611510864645 23118553505876177158287121)
      ·
        refine ⟨17338915129407132868715341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23118553505876177158287121 17338915129407132868715341)
        ·
          refine ⟨6502093173527674825768253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17338915129407132868715341 6502093173527674825768253)
          ·
            refine ⟨2438284940072878059663095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6502093173527674825768253 2438284940072878059663095)
            ·
              refine ⟨3657427410109317089494643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438284940072878059663095 3657427410109317089494643)
              ·
                refine ⟨5486141115163975634241965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3657427410109317089494643 5486141115163975634241965)
                ·
                  refine ⟨2057302918186490862840737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5486141115163975634241965 2057302918186490862840737)
                  ·
                    refine ⟨1542977188639868147130553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2057302918186490862840737 1542977188639868147130553)
                    ·
                      refine ⟨1157232891479901110347915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1542977188639868147130553 1157232891479901110347915)
                      ·
                        rfl

theorem cell23_2253703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_2253703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253703 prefixEnd_2253703 := by exact prefixLift 2253703
  have htrace : WordTrace (prefixWord ++ tailWord_2253703) baseStart_2253703 baseEnd_2253703 := by
    simpa [prefixWord, tailWord_2253703, baseEnd_2253703] using wordTrace_append hprefix tailTrace_2253703
  have hstable : (prefixWord ++ tailWord_2253703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253703).length < 2 ^ (prefixWord ++ tailWord_2253703).sum := by decide
  have hdescent : baseEnd_2253703 < baseStart_2253703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253715 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 5]
def baseStart_2253715 : Nat := 118140960795 + 2253715 * 2 ^ 59
def prefixEnd_2253715 : Nat := 4983230072969 + 3 ^ 40 * 2253715 * 2
def baseEnd_2253715 : Nat := 1157239053247755063397859

theorem tailTrace_2253715 : CollatzResearch.WordTrace tailWord_2253715 prefixEnd_2253715 1157239053247755063397859 := by
  unfold tailWord_2253715
  simp only [CollatzResearch.WordTrace]
  refine ⟨82199739030182933723346599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54799826020121955815564399 82199739030182933723346599)
  ·
    refine ⟨123299608545274400585019899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82199739030182933723346599 123299608545274400585019899)
    ·
      refine ⟨184949412817911600877529849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123299608545274400585019899 184949412817911600877529849)
      ·
        refine ⟨138712059613433700658147387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184949412817911600877529849 138712059613433700658147387)
        ·
          refine ⟨208068089420150550987221081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138712059613433700658147387 208068089420150550987221081)
          ·
            refine ⟨156051067065112913240415811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208068089420150550987221081 156051067065112913240415811)
            ·
              refine ⟨234076600597669369860623717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156051067065112913240415811 234076600597669369860623717)
              ·
                refine ⟨43889362612063006848866947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234076600597669369860623717 43889362612063006848866947)
                ·
                  refine ⟨65834043918094510273300421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43889362612063006848866947 65834043918094510273300421)
                  ·
                    refine ⟨12343883234642720676243829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65834043918094510273300421 12343883234642720676243829)
                    ·
                      refine ⟨1157239053247755063397859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12343883234642720676243829 1157239053247755063397859)
                      ·
                        rfl

theorem cell23_2253715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_2253715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253715 prefixEnd_2253715 := by exact prefixLift 2253715
  have htrace : WordTrace (prefixWord ++ tailWord_2253715) baseStart_2253715 baseEnd_2253715 := by
    simpa [prefixWord, tailWord_2253715, baseEnd_2253715] using wordTrace_append hprefix tailTrace_2253715
  have hstable : (prefixWord ++ tailWord_2253715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253715).length < 2 ^ (prefixWord ++ tailWord_2253715).sum := by decide
  have hdescent : baseEnd_2253715 < baseStart_2253715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253797 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2253797 : Nat := 118140960795 + 2253797 * 2 ^ 59
def prefixEnd_2253797 : Nat := 4983230072969 + 3 ^ 40 * 2253797 * 2
def baseEnd_2253797 : Nat := 1157281158661423742572483

theorem tailTrace_2253797 : CollatzResearch.WordTrace tailWord_2253797 prefixEnd_2253797 1157281158661423742572483 := by
  unfold tailWord_2253797
  simp only [CollatzResearch.WordTrace]
  refine ⟨82202729815885861727831645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54801819877257241151887763 82202729815885861727831645)
  ·
    refine ⟨30826023680957198147936867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82202729815885861727831645 30826023680957198147936867)
    ·
      refine ⟨46239035521435797221905301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30826023680957198147936867 46239035521435797221905301)
      ·
        refine ⟨2167454790067302994776811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46239035521435797221905301 2167454790067302994776811)
        ·
          refine ⟨3251182185100954492165217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167454790067302994776811 3251182185100954492165217)
          ·
            refine ⟨2438386638825715869123913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3251182185100954492165217 2438386638825715869123913)
            ·
              refine ⟨1828789979119286901842935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2438386638825715869123913 1828789979119286901842935)
              ·
                refine ⟨2743184968678930352764403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828789979119286901842935 2743184968678930352764403)
                ·
                  refine ⟨4114777453018395529146605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743184968678930352764403 4114777453018395529146605)
                  ·
                    refine ⟨1543041544881898323429977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4114777453018395529146605 1543041544881898323429977)
                    ·
                      refine ⟨1157281158661423742572483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543041544881898323429977 1157281158661423742572483)
                      ·
                        rfl

theorem cell23_2253797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2253797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253797 prefixEnd_2253797 := by exact prefixLift 2253797
  have htrace : WordTrace (prefixWord ++ tailWord_2253797) baseStart_2253797 baseEnd_2253797 := by
    simpa [prefixWord, tailWord_2253797, baseEnd_2253797] using wordTrace_append hprefix tailTrace_2253797
  have hstable : (prefixWord ++ tailWord_2253797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253797).length < 2 ^ (prefixWord ++ tailWord_2253797).sum := by decide
  have hdescent : baseEnd_2253797 < baseStart_2253797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253809 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_2253809 : Nat := 118140960795 + 2253809 * 2 ^ 59
def prefixEnd_2253809 : Nat := 4983230072969 + 3 ^ 40 * 2253809 * 2
def baseEnd_2253809 : Nat := 1157287320429277695622427

theorem tailTrace_2253809 : CollatzResearch.WordTrace tailWord_2253809 prefixEnd_2253809 1157287320429277695622427 := by
  unfold tailWord_2253809
  simp only [CollatzResearch.WordTrace]
  refine ⟨82203167491842387777268481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54802111661228258518178987 82203167491842387777268481)
  ·
    refine ⟨61652375618881790832951361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82203167491842387777268481 61652375618881790832951361)
    ·
      refine ⟨46239281714161343124713521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61652375618881790832951361 46239281714161343124713521)
      ·
        refine ⟨34679461285621007343535141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46239281714161343124713521 34679461285621007343535141)
        ·
          refine ⟨6502398991053938876912839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34679461285621007343535141 6502398991053938876912839)
          ·
            refine ⟨9753598486580908315369259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502398991053938876912839 9753598486580908315369259)
            ·
              refine ⟨14630397729871362473053889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9753598486580908315369259 14630397729871362473053889)
              ·
                refine ⟨10972798297403521854790417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14630397729871362473053889 10972798297403521854790417)
                ·
                  refine ⟨8229598723052641391092813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10972798297403521854790417 8229598723052641391092813)
                  ·
                    refine ⟨3086099521144740521659805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8229598723052641391092813 3086099521144740521659805)
                    ·
                      refine ⟨1157287320429277695622427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3086099521144740521659805 1157287320429277695622427)
                      ·
                        rfl

theorem cell23_2253809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_2253809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253809 prefixEnd_2253809 := by exact prefixLift 2253809
  have htrace : WordTrace (prefixWord ++ tailWord_2253809) baseStart_2253809 baseEnd_2253809 := by
    simpa [prefixWord, tailWord_2253809, baseEnd_2253809] using wordTrace_append hprefix tailTrace_2253809
  have hstable : (prefixWord ++ tailWord_2253809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253809).length < 2 ^ (prefixWord ++ tailWord_2253809).sum := by decide
  have hdescent : baseEnd_2253809 < baseStart_2253809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253810 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2253810 : Nat := 118140960795 + 2253810 * 2 ^ 59
def prefixEnd_2253810 : Nat := 4983230072969 + 3 ^ 40 * 2253810 * 2
def baseEnd_2253810 : Nat := 1157287833909932191709923

theorem tailTrace_2253810 : CollatzResearch.WordTrace tailWord_2253810 prefixEnd_2253810 1157287833909932191709923 := by
  unfold tailWord_2253810
  simp only [CollatzResearch.WordTrace]
  refine ⟨20550800991209691237013721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54802135976559176632036589 20550800991209691237013721)
  ·
    refine ⟨15413100743407268427760291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20550800991209691237013721 15413100743407268427760291)
    ·
      refine ⟨23119651115110902641640437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15413100743407268427760291 23119651115110902641640437)
      ·
        refine ⟨2167467292041647122653791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23119651115110902641640437 2167467292041647122653791)
        ·
          refine ⟨3251200938062470683980687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167467292041647122653791 3251200938062470683980687)
          ·
            refine ⟨4876801407093706025971031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3251200938062470683980687 4876801407093706025971031)
            ·
              refine ⟨7315202110640559038956547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4876801407093706025971031 7315202110640559038956547)
              ·
                refine ⟨10972803165960838558434821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7315202110640559038956547 10972803165960838558434821)
                ·
                  refine ⟨2057400593617657229706529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10972803165960838558434821 2057400593617657229706529)
                  ·
                    refine ⟨1543050445213242922279897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2057400593617657229706529 1543050445213242922279897)
                    ·
                      refine ⟨1157287833909932191709923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543050445213242922279897 1157287833909932191709923)
                      ·
                        rfl

theorem cell23_2253810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2253810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253810 prefixEnd_2253810 := by exact prefixLift 2253810
  have htrace : WordTrace (prefixWord ++ tailWord_2253810) baseStart_2253810 baseEnd_2253810 := by
    simpa [prefixWord, tailWord_2253810, baseEnd_2253810] using wordTrace_append hprefix tailTrace_2253810
  have hstable : (prefixWord ++ tailWord_2253810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253810).length < 2 ^ (prefixWord ++ tailWord_2253810).sum := by decide
  have hdescent : baseEnd_2253810 < baseStart_2253810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253849 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 1, 6, 2]
def baseStart_2253849 : Nat := 118140960795 + 2253849 * 2 ^ 59
def prefixEnd_2253849 : Nat := 4983230072969 + 3 ^ 40 * 2253849 * 2
def baseEnd_2253849 : Nat := 1157307859655457539122243

theorem tailTrace_2253849 : CollatzResearch.WordTrace tailWord_2253849 prefixEnd_2253849 1157307859655457539122243 := by
  unfold tailWord_2253849
  simp only [CollatzResearch.WordTrace]
  refine ⟨82204626411697474608724601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54803084274464983072483067 82204626411697474608724601)
  ·
    refine ⟨61653469808773105956543451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82204626411697474608724601 61653469808773105956543451)
    ·
      refine ⟨92480204713159658934815177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61653469808773105956543451 92480204713159658934815177)
      ·
        refine ⟨69360153534869744201111383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92480204713159658934815177 69360153534869744201111383)
        ·
          refine ⟨104040230302304616301667075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69360153534869744201111383 104040230302304616301667075)
          ·
            refine ⟨156060345453456924452500613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104040230302304616301667075 156060345453456924452500613)
            ·
              refine ⟨29261314772523173334843865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156060345453456924452500613 29261314772523173334843865)
              ·
                refine ⟨21945986079392380001132899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29261314772523173334843865 21945986079392380001132899)
                ·
                  refine ⟨32918979119088570001699349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21945986079392380001132899 32918979119088570001699349)
                  ·
                    refine ⟨1543077146207276718829657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32918979119088570001699349 1543077146207276718829657)
                    ·
                      refine ⟨1157307859655457539122243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543077146207276718829657 1157307859655457539122243)
                      ·
                        rfl

theorem cell23_2253849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_2253849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253849 prefixEnd_2253849 := by exact prefixLift 2253849
  have htrace : WordTrace (prefixWord ++ tailWord_2253849) baseStart_2253849 baseEnd_2253849 := by
    simpa [prefixWord, tailWord_2253849, baseEnd_2253849] using wordTrace_append hprefix tailTrace_2253849
  have hstable : (prefixWord ++ tailWord_2253849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253849).length < 2 ^ (prefixWord ++ tailWord_2253849).sum := by decide
  have hdescent : baseEnd_2253849 < baseStart_2253849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253872 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 8]
def baseStart_2253872 : Nat := 118140960795 + 2253872 * 2 ^ 59
def prefixEnd_2253872 : Nat := 4983230072969 + 3 ^ 40 * 2253872 * 2
def baseEnd_2253872 : Nat := 128591074412278994348293

theorem tailTrace_2253872 : CollatzResearch.WordTrace tailWord_2253872 prefixEnd_2253872 128591074412278994348293 := by
  unfold tailWord_2253872
  simp only [CollatzResearch.WordTrace]
  refine ⟨41102732645307074768405935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54803643527076099691207913 41102732645307074768405935)
  ·
    refine ⟨61654098967960612152608903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41102732645307074768405935 61654098967960612152608903)
    ·
      refine ⟨92481148451940918228913355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61654098967960612152608903 92481148451940918228913355)
      ·
        refine ⟨138721722677911377343370033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92481148451940918228913355 138721722677911377343370033)
        ·
          refine ⟨104041292008433533007527525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138721722677911377343370033 104041292008433533007527525)
          ·
            refine ⟨19507742251581287438911411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104041292008433533007527525 19507742251581287438911411)
            ·
              refine ⟨29261613377371931158367117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19507742251581287438911411 29261613377371931158367117)
              ·
                refine ⟨10973105016514474184387669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29261613377371931158367117 10973105016514474184387669)
                ·
                  refine ⟨128591074412278994348293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10973105016514474184387669 128591074412278994348293)
                  ·
                    rfl

theorem cell23_2253872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 8].length) (baseStart_2253872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253872 prefixEnd_2253872 := by exact prefixLift 2253872
  have htrace : WordTrace (prefixWord ++ tailWord_2253872) baseStart_2253872 baseEnd_2253872 := by
    simpa [prefixWord, tailWord_2253872, baseEnd_2253872] using wordTrace_append hprefix tailTrace_2253872
  have hstable : (prefixWord ++ tailWord_2253872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253872).length < 2 ^ (prefixWord ++ tailWord_2253872).sum := by decide
  have hdescent : baseEnd_2253872 < baseStart_2253872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253956 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_2253956 : Nat := 118140960795 + 2253956 * 2 ^ 59
def prefixEnd_2253956 : Nat := 4983230072969 + 3 ^ 40 * 2253956 * 2
def baseEnd_2253956 : Nat := 1157362802085488620484251

theorem tailTrace_2253956 : CollatzResearch.WordTrace tailWord_2253956 prefixEnd_2253956 1157362802085488620484251 := by
  unfold tailWord_2253956
  simp only [CollatzResearch.WordTrace]
  refine ⟨41104264511154915941434861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54805686014873221255246481 41104264511154915941434861)
  ·
    refine ⟨15414099191683093478038073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41104264511154915941434861 15414099191683093478038073)
    ·
      refine ⟨11560574393762320108528555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15414099191683093478038073 11560574393762320108528555)
      ·
        refine ⟨17340861590643480162792833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11560574393762320108528555 17340861590643480162792833)
        ·
          refine ⟨13005646192982610122094625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17340861590643480162792833 13005646192982610122094625)
          ·
            refine ⟨9754234644736957591570969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13005646192982610122094625 9754234644736957591570969)
            ·
              refine ⟨7315675983552718193678227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9754234644736957591570969 7315675983552718193678227)
              ·
                refine ⟨10973513975329077290517341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7315675983552718193678227 10973513975329077290517341)
                ·
                  refine ⟨4115067740748403983944003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10973513975329077290517341 4115067740748403983944003)
                  ·
                    refine ⟨6172601611122605975916005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4115067740748403983944003 6172601611122605975916005)
                    ·
                      refine ⟨1157362802085488620484251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6172601611122605975916005 1157362802085488620484251)
                      ·
                        rfl

theorem cell23_2253956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_2253956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253956 prefixEnd_2253956 := by exact prefixLift 2253956
  have htrace : WordTrace (prefixWord ++ tailWord_2253956) baseStart_2253956 baseEnd_2253956 := by
    simpa [prefixWord, tailWord_2253956, baseEnd_2253956] using wordTrace_append hprefix tailTrace_2253956
  have hstable : (prefixWord ++ tailWord_2253956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253956).length < 2 ^ (prefixWord ++ tailWord_2253956).sum := by decide
  have hdescent : baseEnd_2253956 < baseStart_2253956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253966 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2253966 : Nat := 118140960795 + 2253966 * 2 ^ 59
def prefixEnd_2253966 : Nat := 4983230072969 + 3 ^ 40 * 2253966 * 2
def baseEnd_2253966 : Nat := 385789312297344527119735

theorem tailTrace_2253966 : CollatzResearch.WordTrace tailWord_2253966 prefixEnd_2253966 385789312297344527119735 := by
  unfold tailWord_2253966
  simp only [CollatzResearch.WordTrace]
  refine ⟨10276111719034200448841719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54805929168182402393822501 10276111719034200448841719)
  ·
    refine ⟨15414167578551300673262579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10276111719034200448841719 15414167578551300673262579)
    ·
      refine ⟨23121251367826951009893869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15414167578551300673262579 23121251367826951009893869)
      ·
        refine ⟨8670469262935106628710201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23121251367826951009893869 8670469262935106628710201)
        ·
          refine ⟨6502851947201329971532651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8670469262935106628710201 6502851947201329971532651)
          ·
            refine ⟨9754277920801994957298977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502851947201329971532651 9754277920801994957298977)
            ·
              refine ⟨7315708440601496217974233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9754277920801994957298977 7315708440601496217974233)
              ·
                refine ⟨5486781330451122163480675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7315708440601496217974233 5486781330451122163480675)
                ·
                  refine ⟨8230171995676683245221013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5486781330451122163480675 8230171995676683245221013)
                  ·
                    refine ⟨385789312297344527119735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8230171995676683245221013 385789312297344527119735)
                    ·
                      rfl

theorem cell23_2253966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2253966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253966 prefixEnd_2253966 := by exact prefixLift 2253966
  have htrace : WordTrace (prefixWord ++ tailWord_2253966) baseStart_2253966 baseEnd_2253966 := by
    simpa [prefixWord, tailWord_2253966, baseEnd_2253966] using wordTrace_append hprefix tailTrace_2253966
  have hstable : (prefixWord ++ tailWord_2253966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253966).length < 2 ^ (prefixWord ++ tailWord_2253966).sum := by decide
  have hdescent : baseEnd_2253966 < baseStart_2253966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253970 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_2253970 : Nat := 118140960795 + 2253970 * 2 ^ 59
def prefixEnd_2253970 : Nat := 4983230072969 + 3 ^ 40 * 2253970 * 2
def baseEnd_2253970 : Nat := 385789996938217188569729

theorem tailTrace_2253970 : CollatzResearch.WordTrace tailWord_2253970 prefixEnd_2253970 385789996938217188569729 := by
  unfold tailWord_2253970
  simp only [CollatzResearch.WordTrace]
  refine ⟨20552259911064778068469841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54806026429506074849252909 20552259911064778068469841)
  ·
    refine ⟨15414194933298583551352381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20552259911064778068469841 15414194933298583551352381)
    ·
      refine ⟨5780323099986968831757143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15414194933298583551352381 5780323099986968831757143)
      ·
        refine ⟨8670484649980453247635715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5780323099986968831757143 8670484649980453247635715)
        ·
          refine ⟨13005726974970679871453573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670484649980453247635715 13005726974970679871453573)
          ·
            refine ⟨2438573807807002475897545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13005726974970679871453573 2438573807807002475897545)
            ·
              refine ⟨1828930355855251856923159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2438573807807002475897545 1828930355855251856923159)
              ·
                refine ⟨2743395533782877785384739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828930355855251856923159 2743395533782877785384739)
                ·
                  refine ⟨4115093300674316678077109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743395533782877785384739 4115093300674316678077109)
                  ·
                    refine ⟨385789996938217188569729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4115093300674316678077109 385789996938217188569729)
                    ·
                      rfl

theorem cell23_2253970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_2253970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253970 prefixEnd_2253970 := by exact prefixLift 2253970
  have htrace : WordTrace (prefixWord ++ tailWord_2253970) baseStart_2253970 baseEnd_2253970 := by
    simpa [prefixWord, tailWord_2253970, baseEnd_2253970] using wordTrace_append hprefix tailTrace_2253970
  have hstable : (prefixWord ++ tailWord_2253970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253970).length < 2 ^ (prefixWord ++ tailWord_2253970).sum := by decide
  have hdescent : baseEnd_2253970 < baseStart_2253970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2253983 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 4, 4]
def baseStart_2253983 : Nat := 118140960795 + 2253983 * 2 ^ 59
def prefixEnd_2253983 : Nat := 4983230072969 + 3 ^ 40 * 2253983 * 2
def baseEnd_2253983 : Nat := 385792222021053338282209

theorem tailTrace_2253983 : CollatzResearch.WordTrace tailWord_2253983 prefixEnd_2253983 385792222021053338282209 := by
  unfold tailWord_2253983
  simp only [CollatzResearch.WordTrace]
  refine ⟨82209513793212015494102603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54806342528808010329401735 82209513793212015494102603)
  ·
    refine ⟨123314270689818023241153905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82209513793212015494102603 123314270689818023241153905)
    ·
      refine ⟨92485703017363517430865429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123314270689818023241153905 92485703017363517430865429)
      ·
        refine ⟨4335267328938914879571817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92485703017363517430865429 4335267328938914879571817)
        ·
          refine ⟨3251450496704186159678863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4335267328938914879571817 3251450496704186159678863)
          ·
            refine ⟨4877175745056279239518295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3251450496704186159678863 4877175745056279239518295)
            ·
              refine ⟨7315763617584418859277443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877175745056279239518295 7315763617584418859277443)
              ·
                refine ⟨10973645426376628288916165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7315763617584418859277443 10973645426376628288916165)
                ·
                  refine ⟨2057558517445617804171781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10973645426376628288916165 2057558517445617804171781)
                  ·
                    refine ⟨385792222021053338282209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2057558517445617804171781 385792222021053338282209)
                    ·
                      rfl

theorem cell23_2253983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 4].length) (baseStart_2253983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2253983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2253983 prefixEnd_2253983 := by exact prefixLift 2253983
  have htrace : WordTrace (prefixWord ++ tailWord_2253983) baseStart_2253983 baseEnd_2253983 := by
    simpa [prefixWord, tailWord_2253983, baseEnd_2253983] using wordTrace_append hprefix tailTrace_2253983
  have hstable : (prefixWord ++ tailWord_2253983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2253983).length < 2 ^ (prefixWord ++ tailWord_2253983).sum := by decide
  have hdescent : baseEnd_2253983 < baseStart_2253983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2253983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254018 : List Nat := [3, 5, 1, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_2254018 : Nat := 118140960795 + 2254018 * 2 ^ 59
def prefixEnd_2254018 : Nat := 4983230072969 + 3 ^ 40 * 2254018 * 2
def baseEnd_2254018 : Nat := 1157394637886067377908967

theorem tailTrace_2254018 : CollatzResearch.WordTrace tailWord_2254018 prefixEnd_2254018 1157394637886067377908967 := by
  unfold tailWord_2254018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20552697587021304117906677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54807193565390144314417805 20552697587021304117906677)
  ·
    refine ⟨1926815398783247261053751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20552697587021304117906677 1926815398783247261053751)
    ·
      refine ⟨2890223098174870891580627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926815398783247261053751 2890223098174870891580627)
      ·
        refine ⟨4335334647262306337370941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890223098174870891580627 4335334647262306337370941)
        ·
          refine ⟨1625750492723364876514103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4335334647262306337370941 1625750492723364876514103)
          ·
            refine ⟨2438625739085047314771155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625750492723364876514103 2438625739085047314771155)
            ·
              refine ⟨3657938608627570972156733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438625739085047314771155 3657938608627570972156733)
              ·
                refine ⟨1371726978235339114558775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3657938608627570972156733 1371726978235339114558775)
                ·
                  refine ⟨2057590467353008671838163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371726978235339114558775 2057590467353008671838163)
                  ·
                    refine ⟨3086385701029513007757245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2057590467353008671838163 3086385701029513007757245)
                    ·
                      refine ⟨1157394637886067377908967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3086385701029513007757245 1157394637886067377908967)
                      ·
                        rfl

theorem cell23_2254018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_2254018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254018 prefixEnd_2254018 := by exact prefixLift 2254018
  have htrace : WordTrace (prefixWord ++ tailWord_2254018) baseStart_2254018 baseEnd_2254018 := by
    simpa [prefixWord, tailWord_2254018, baseEnd_2254018] using wordTrace_append hprefix tailTrace_2254018
  have hstable : (prefixWord ++ tailWord_2254018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254018).length < 2 ^ (prefixWord ++ tailWord_2254018).sum := by decide
  have hdescent : baseEnd_2254018 < baseStart_2254018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254039 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 4, 6]
def baseStart_2254039 : Nat := 118140960795 + 2254039 * 2 ^ 59
def prefixEnd_2254039 : Nat := 4983230072969 + 3 ^ 40 * 2254039 * 2
def baseEnd_2254039 : Nat := 385801806993270598582123

theorem tailTrace_2254039 : CollatzResearch.WordTrace tailWord_2254039 prefixEnd_2254039 385801806993270598582123 := by
  unfold tailWord_2254039
  simp only [CollatzResearch.WordTrace]
  refine ⟨82211556281009137058141171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54807704187339424705427447 82211556281009137058141171)
  ·
    refine ⟨123317334421513705587211757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82211556281009137058141171 123317334421513705587211757)
    ·
      refine ⟨46244000408067639595204409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123317334421513705587211757 46244000408067639595204409)
      ·
        refine ⟨34683000306050729696403307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46244000408067639595204409 34683000306050729696403307)
        ·
          refine ⟨52024500459076094544604961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34683000306050729696403307 52024500459076094544604961)
          ·
            refine ⟨39018375344307070908453721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52024500459076094544604961 39018375344307070908453721)
            ·
              refine ⟨29263781508230303181340291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39018375344307070908453721 29263781508230303181340291)
              ·
                refine ⟨43895672262345454772010437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29263781508230303181340291 43895672262345454772010437)
                ·
                  refine ⟨8230438549189772769751957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43895672262345454772010437 8230438549189772769751957)
                  ·
                    refine ⟨385801806993270598582123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8230438549189772769751957 385801806993270598582123)
                    ·
                      rfl

theorem cell23_2254039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_2254039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254039 prefixEnd_2254039 := by exact prefixLift 2254039
  have htrace : WordTrace (prefixWord ++ tailWord_2254039) baseStart_2254039 baseEnd_2254039 := by
    simpa [prefixWord, tailWord_2254039, baseEnd_2254039] using wordTrace_append hprefix tailTrace_2254039
  have hstable : (prefixWord ++ tailWord_2254039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254039).length < 2 ^ (prefixWord ++ tailWord_2254039).sum := by decide
  have hdescent : baseEnd_2254039 < baseStart_2254039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254099 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 5, 7]
def baseStart_2254099 : Nat := 118140960795 + 2254099 * 2 ^ 59
def prefixEnd_2254099 : Nat := 4983230072969 + 3 ^ 40 * 2254099 * 2
def baseEnd_2254099 : Nat := 385812076606360520332031

theorem tailTrace_2254099 : CollatzResearch.WordTrace tailWord_2254099 prefixEnd_2254099 385812076606360520332031 := by
  unfold tailWord_2254099
  simp only [CollatzResearch.WordTrace]
  refine ⟨82213744660791767305325351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54809163107194511536883567 82213744660791767305325351)
  ·
    refine ⟨123320616991187650957988027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82213744660791767305325351 123320616991187650957988027)
    ·
      refine ⟨184980925486781476436982041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123320616991187650957988027 184980925486781476436982041)
      ·
        refine ⟨138735694115086107327736531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184980925486781476436982041 138735694115086107327736531)
        ·
          refine ⟨208103541172629160991604797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138735694115086107327736531 208103541172629160991604797)
          ·
            refine ⟨78038827939735935371851799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208103541172629160991604797 78038827939735935371851799)
            ·
              refine ⟨117058241909603903057777699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78038827939735935371851799 117058241909603903057777699)
              ·
                refine ⟨175587362864405854586666549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117058241909603903057777699 175587362864405854586666549)
                ·
                  refine ⟨16461315268538048867499989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175587362864405854586666549 16461315268538048867499989)
                  ·
                    refine ⟨385812076606360520332031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16461315268538048867499989 385812076606360520332031)
                    ·
                      rfl

theorem cell23_2254099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 7].length) (baseStart_2254099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254099 prefixEnd_2254099 := by exact prefixLift 2254099
  have htrace : WordTrace (prefixWord ++ tailWord_2254099) baseStart_2254099 baseEnd_2254099 := by
    simpa [prefixWord, tailWord_2254099, baseEnd_2254099] using wordTrace_append hprefix tailTrace_2254099
  have hstable : (prefixWord ++ tailWord_2254099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254099).length < 2 ^ (prefixWord ++ tailWord_2254099).sum := by decide
  have hdescent : baseEnd_2254099 < baseStart_2254099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254103 : List Nat := [1, 1, 3, 4, 1, 1, 3, 4, 5]
def baseStart_2254103 : Nat := 118140960795 + 2254103 * 2 ^ 59
def prefixEnd_2254103 : Nat := 4983230072969 + 3 ^ 40 * 2254103 * 2
def baseEnd_2254103 : Nat := 128604253749077727260675

theorem tailTrace_2254103 : CollatzResearch.WordTrace tailWord_2254103 prefixEnd_2254103 128604253749077727260675 := by
  unfold tailWord_2254103
  simp only [CollatzResearch.WordTrace]
  refine ⟨82213890552777275988470963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54809260368518183992313975 82213890552777275988470963)
  ·
    refine ⟨123320835829165913982706445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82213890552777275988470963 123320835829165913982706445)
    ·
      refine ⟨46245313435937217743514917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123320835829165913982706445 46245313435937217743514917)
      ·
        refine ⟨8670996269238228326909047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46245313435937217743514917 8670996269238228326909047)
        ·
          refine ⟨13006494403857342490363571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670996269238228326909047 13006494403857342490363571)
          ·
            refine ⟨19509741605786013735545357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13006494403857342490363571 19509741605786013735545357)
            ·
              refine ⟨7316153102169755150829509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19509741605786013735545357 7316153102169755150829509)
              ·
                refine ⟨1371778706656829090780533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7316153102169755150829509 1371778706656829090780533)
                ·
                  refine ⟨128604253749077727260675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1371778706656829090780533 128604253749077727260675)
                  ·
                    rfl

theorem cell23_2254103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 5].length) (baseStart_2254103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254103 prefixEnd_2254103 := by exact prefixLift 2254103
  have htrace : WordTrace (prefixWord ++ tailWord_2254103) baseStart_2254103 baseEnd_2254103 := by
    simpa [prefixWord, tailWord_2254103, baseEnd_2254103] using wordTrace_append hprefix tailTrace_2254103
  have hstable : (prefixWord ++ tailWord_2254103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254103).length < 2 ^ (prefixWord ++ tailWord_2254103).sum := by decide
  have hdescent : baseEnd_2254103 < baseStart_2254103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254116 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_2254116 : Nat := 118140960795 + 2254116 * 2 ^ 59
def prefixEnd_2254116 : Nat := 4983230072969 + 3 ^ 40 * 2254116 * 2
def baseEnd_2254116 : Nat := 385814986330069331494505

theorem tailTrace_2254116 : CollatzResearch.WordTrace tailWord_2254116 prefixEnd_2254116 385814986330069331494505 := by
  unfold tailWord_2254116
  simp only [CollatzResearch.WordTrace]
  refine ⟨41107182350865089604347101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54809576467820119472462801 41107182350865089604347101)
  ·
    refine ⟨15415193381574408601630163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41107182350865089604347101 15415193381574408601630163)
    ·
      refine ⟨23122790072361612902445245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15415193381574408601630163 23122790072361612902445245)
      ·
        refine ⟨8671046277135604838416967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23122790072361612902445245 8671046277135604838416967)
        ·
          refine ⟨13006569415703407257625451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8671046277135604838416967 13006569415703407257625451)
          ·
            refine ⟨19509854123555110886438177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13006569415703407257625451 19509854123555110886438177)
            ·
              refine ⟨14632390592666333164828633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19509854123555110886438177 14632390592666333164828633)
              ·
                refine ⟨10974292944499749873621475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14632390592666333164828633 10974292944499749873621475)
                ·
                  refine ⟨16461439416749624810432213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10974292944499749873621475 16461439416749624810432213)
                  ·
                    refine ⟨385814986330069331494505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16461439416749624810432213 385814986330069331494505)
                    ·
                      rfl

theorem cell23_2254116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_2254116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254116 prefixEnd_2254116 := by exact prefixLift 2254116
  have htrace : WordTrace (prefixWord ++ tailWord_2254116) baseStart_2254116 baseEnd_2254116 := by
    simpa [prefixWord, tailWord_2254116, baseEnd_2254116] using wordTrace_append hprefix tailTrace_2254116
  have hstable : (prefixWord ++ tailWord_2254116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254116).length < 2 ^ (prefixWord ++ tailWord_2254116).sum := by decide
  have hdescent : baseEnd_2254116 < baseStart_2254116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254133 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2254133 : Nat := 118140960795 + 2254133 * 2 ^ 59
def prefixEnd_2254133 : Nat := 4983230072969 + 3 ^ 40 * 2254133 * 2
def baseEnd_2254133 : Nat := 385817896053778142656979

theorem tailTrace_2254133 : CollatzResearch.WordTrace tailWord_2254133 prefixEnd_2254133 385817896053778142656979 := by
  unfold tailWord_2254133
  simp only [CollatzResearch.WordTrace]
  refine ⟨82214984742668591112063053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54809989828445727408042035 82214984742668591112063053)
  ·
    refine ⟨30830619278500721667023645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82214984742668591112063053 30830619278500721667023645)
    ·
      refine ⟨11561482229437770625133867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30830619278500721667023645 11561482229437770625133867)
      ·
        refine ⟨17342223344156655937700801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11561482229437770625133867 17342223344156655937700801)
        ·
          refine ⟨13006667508117491953275601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17342223344156655937700801 13006667508117491953275601)
          ·
            refine ⟨9755000631088118964956701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13006667508117491953275601 9755000631088118964956701)
            ·
              refine ⟨3658125236658044611858763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9755000631088118964956701 3658125236658044611858763)
              ·
                refine ⟨5487187854987066917788145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658125236658044611858763 5487187854987066917788145)
                ·
                  refine ⟨4115390891240300188341109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5487187854987066917788145 4115390891240300188341109)
                  ·
                    refine ⟨385817896053778142656979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4115390891240300188341109 385817896053778142656979)
                    ·
                      rfl

theorem cell23_2254133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2254133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254133 prefixEnd_2254133 := by exact prefixLift 2254133
  have htrace : WordTrace (prefixWord ++ tailWord_2254133) baseStart_2254133 baseEnd_2254133 := by
    simpa [prefixWord, tailWord_2254133, baseEnd_2254133] using wordTrace_append hprefix tailTrace_2254133
  have hstable : (prefixWord ++ tailWord_2254133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254133).length < 2 ^ (prefixWord ++ tailWord_2254133).sum := by decide
  have hdescent : baseEnd_2254133 < baseStart_2254133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254153 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 2, 4, 2]
def baseStart_2254153 : Nat := 118140960795 + 2254153 * 2 ^ 59
def prefixEnd_2254153 : Nat := 4983230072969 + 3 ^ 40 * 2254153 * 2
def baseEnd_2254153 : Nat := 1157463957774424349720845

theorem tailTrace_2254153 : CollatzResearch.WordTrace tailWord_2254153 prefixEnd_2254153 1157463957774424349720845 := by
  unfold tailWord_2254153
  simp only [CollatzResearch.WordTrace]
  refine ⟨82215714202596134527791113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54810476135064089685194075 82215714202596134527791113)
  ·
    refine ⟨61661785651947100895843335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82215714202596134527791113 61661785651947100895843335)
    ·
      refine ⟨92492678477920651343765003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61661785651947100895843335 92492678477920651343765003)
      ·
        refine ⟨138739017716880977015647505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92492678477920651343765003 138739017716880977015647505)
        ·
          refine ⟨104054263287660732761735629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138739017716880977015647505 104054263287660732761735629)
          ·
            refine ⟨39020348732872774785650861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104054263287660732761735629 39020348732872774785650861)
            ·
              refine ⟨14632630774827290544619073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39020348732872774785650861 14632630774827290544619073)
              ·
                refine ⟨10974473081120467908464305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14632630774827290544619073 10974473081120467908464305)
                ·
                  refine ⟨8230854810840350931348229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10974473081120467908464305 8230854810840350931348229)
                  ·
                    refine ⟨1543285277032565799627793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8230854810840350931348229 1543285277032565799627793)
                    ·
                      refine ⟨1157463957774424349720845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543285277032565799627793 1157463957774424349720845)
                      ·
                        rfl

theorem cell23_2254153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 4, 2].length) (baseStart_2254153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254153 prefixEnd_2254153 := by exact prefixLift 2254153
  have htrace : WordTrace (prefixWord ++ tailWord_2254153) baseStart_2254153 baseEnd_2254153 := by
    simpa [prefixWord, tailWord_2254153, baseEnd_2254153] using wordTrace_append hprefix tailTrace_2254153
  have hstable : (prefixWord ++ tailWord_2254153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254153).length < 2 ^ (prefixWord ++ tailWord_2254153).sum := by decide
  have hdescent : baseEnd_2254153 < baseStart_2254153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254163 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 3, 4]
def baseStart_2254163 : Nat := 118140960795 + 2254163 * 2 ^ 59
def prefixEnd_2254163 : Nat := 4983230072969 + 3 ^ 40 * 2254163 * 2
def baseEnd_2254163 : Nat := 385823030860323103531933

theorem tailTrace_2254163 : CollatzResearch.WordTrace tailWord_2254163 prefixEnd_2254163 385823030860323103531933 := by
  unfold tailWord_2254163
  simp only [CollatzResearch.WordTrace]
  refine ⟨82216078932559906235655143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54810719288373270823770095 82216078932559906235655143)
  ·
    refine ⟨123324118398839859353482715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82216078932559906235655143 123324118398839859353482715)
    ·
      refine ⟨184986177598259789030224073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123324118398839859353482715 184986177598259789030224073)
      ·
        refine ⟨138739633198694841772668055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184986177598259789030224073 138739633198694841772668055)
        ·
          refine ⟨208109449798042262659002083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138739633198694841772668055 208109449798042262659002083)
          ·
            refine ⟨312164174697063393988503125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208109449798042262659002083 312164174697063393988503125)
            ·
              refine ⟨3658173922231211648302771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 312164174697063393988503125 3658173922231211648302771)
              ·
                refine ⟨5487260883346817472454157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658173922231211648302771 5487260883346817472454157)
                ·
                  refine ⟨2057722831255056552170309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5487260883346817472454157 2057722831255056552170309)
                  ·
                    refine ⟨385823030860323103531933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2057722831255056552170309 385823030860323103531933)
                    ·
                      rfl

theorem cell23_2254163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 4].length) (baseStart_2254163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254163 prefixEnd_2254163 := by exact prefixLift 2254163
  have htrace : WordTrace (prefixWord ++ tailWord_2254163) baseStart_2254163 baseEnd_2254163 := by
    simpa [prefixWord, tailWord_2254163, baseEnd_2254163] using wordTrace_append hprefix tailTrace_2254163
  have hstable : (prefixWord ++ tailWord_2254163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254163).length < 2 ^ (prefixWord ++ tailWord_2254163).sum := by decide
  have hdescent : baseEnd_2254163 < baseStart_2254163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254210 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2254210 : Nat := 118140960795 + 2254210 * 2 ^ 59
def prefixEnd_2254210 : Nat := 4983230072969 + 3 ^ 40 * 2254210 * 2
def baseEnd_2254210 : Nat := 128610358463525625189787

theorem tailTrace_2254210 : CollatzResearch.WordTrace tailWord_2254210 prefixEnd_2254210 128610358463525625189787 := by
  unfold tailWord_2254210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20554448290847408315654021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54811862108926422175077389 20554448290847408315654021)
  ·
    refine ⟨3853959054533889059185129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20554448290847408315654021 3853959054533889059185129)
    ·
      refine ⟨2890469290900416794388847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3853959054533889059185129 2890469290900416794388847)
      ·
        refine ⟨4335703936350625191583271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890469290900416794388847 4335703936350625191583271)
        ·
          refine ⟨6503555904525937787374907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335703936350625191583271 6503555904525937787374907)
          ·
            refine ⟨9755333856788906681062361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6503555904525937787374907 9755333856788906681062361)
            ·
              refine ⟨7316500392591680010796771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9755333856788906681062361 7316500392591680010796771)
              ·
                refine ⟨10974750588887520016195157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7316500392591680010796771 10974750588887520016195157)
                ·
                  refine ⟨128610358463525625189787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10974750588887520016195157 128610358463525625189787)
                  ·
                    rfl

theorem cell23_2254210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2254210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254210 prefixEnd_2254210 := by exact prefixLift 2254210
  have htrace : WordTrace (prefixWord ++ tailWord_2254210) baseStart_2254210 baseEnd_2254210 := by
    simpa [prefixWord, tailWord_2254210, baseEnd_2254210] using wordTrace_append hprefix tailTrace_2254210
  have hstable : (prefixWord ++ tailWord_2254210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254210).length < 2 ^ (prefixWord ++ tailWord_2254210).sum := by decide
  have hdescent : baseEnd_2254210 < baseStart_2254210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254243 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 4]
def baseStart_2254243 : Nat := 118140960795 + 2254243 * 2 ^ 59
def prefixEnd_2254243 : Nat := 4983230072969 + 3 ^ 40 * 2254243 * 2
def baseEnd_2254243 : Nat := 1157510171033328997595431

theorem tailTrace_2254243 : CollatzResearch.WordTrace tailWord_2254243 prefixEnd_2254243 1157510171033328997595431 := by
  unfold tailWord_2254243
  simp only [CollatzResearch.WordTrace]
  refine ⟨82218996772270079898567383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54812664514846719932378255 82218996772270079898567383)
  ·
    refine ⟨123328495158405119847851075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82218996772270079898567383 123328495158405119847851075)
    ·
      refine ⟨184992742737607679771776613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123328495158405119847851075 184992742737607679771776613)
      ·
        refine ⟨34686139263301439957208115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184992742737607679771776613 34686139263301439957208115)
        ·
          refine ⟨52029208894952159935812173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34686139263301439957208115 52029208894952159935812173)
          ·
            refine ⟨19510953335607059975929565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52029208894952159935812173 19510953335607059975929565)
            ·
              refine ⟨7316607500852647490973587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19510953335607059975929565 7316607500852647490973587)
              ·
                refine ⟨10974911251278971236460381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7316607500852647490973587 10974911251278971236460381)
                ·
                  refine ⟨4115591719229614213672643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10974911251278971236460381 4115591719229614213672643)
                  ·
                    refine ⟨6173387578844421320508965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4115591719229614213672643 6173387578844421320508965)
                    ·
                      refine ⟨1157510171033328997595431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6173387578844421320508965 1157510171033328997595431)
                      ·
                        rfl

theorem cell23_2254243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_2254243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254243 prefixEnd_2254243 := by exact prefixLift 2254243
  have htrace : WordTrace (prefixWord ++ tailWord_2254243) baseStart_2254243 baseEnd_2254243 := by
    simpa [prefixWord, tailWord_2254243, baseEnd_2254243] using wordTrace_append hprefix tailTrace_2254243
  have hstable : (prefixWord ++ tailWord_2254243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254243).length < 2 ^ (prefixWord ++ tailWord_2254243).sum := by decide
  have hdescent : baseEnd_2254243 < baseStart_2254243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254247 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_2254247 : Nat := 118140960795 + 2254247 * 2 ^ 59
def prefixEnd_2254247 : Nat := 4983230072969 + 3 ^ 40 * 2254247 * 2
def baseEnd_2254247 : Nat := 1157512224955946981945413

theorem tailTrace_2254247 : CollatzResearch.WordTrace tailWord_2254247 prefixEnd_2254247 1157512224955946981945413 := by
  unfold tailWord_2254247
  simp only [CollatzResearch.WordTrace]
  refine ⟨82219142664255588581712995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54812761776170392387808663 82219142664255588581712995)
  ·
    refine ⟨123328713996383382872569493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82219142664255588581712995 123328713996383382872569493)
    ·
      refine ⟨5781033468580471072151695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123328713996383382872569493 5781033468580471072151695)
      ·
        refine ⟨8671550202870706608227543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5781033468580471072151695 8671550202870706608227543)
        ·
          refine ⟨13007325304306059912341315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8671550202870706608227543 13007325304306059912341315)
          ·
            refine ⟨19510987956459089868511973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13007325304306059912341315 19510987956459089868511973)
            ·
              refine ⟨3658310241836079350345995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19510987956459089868511973 3658310241836079350345995)
              ·
                refine ⟨5487465362754119025518993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658310241836079350345995 5487465362754119025518993)
                ·
                  refine ⟨4115599022065589269139245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5487465362754119025518993 4115599022065589269139245)
                  ·
                    refine ⟨1543349633274595975927217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4115599022065589269139245 1543349633274595975927217)
                    ·
                      refine ⟨1157512224955946981945413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543349633274595975927217 1157512224955946981945413)
                      ·
                        rfl

theorem cell23_2254247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_2254247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254247 prefixEnd_2254247 := by exact prefixLift 2254247
  have htrace : WordTrace (prefixWord ++ tailWord_2254247) baseStart_2254247 baseEnd_2254247 := by
    simpa [prefixWord, tailWord_2254247, baseEnd_2254247] using wordTrace_append hprefix tailTrace_2254247
  have hstable : (prefixWord ++ tailWord_2254247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254247).length < 2 ^ (prefixWord ++ tailWord_2254247).sum := by decide
  have hdescent : baseEnd_2254247 < baseStart_2254247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254256 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_2254256 : Nat := 118140960795 + 2254256 * 2 ^ 59
def prefixEnd_2254256 : Nat := 4983230072969 + 3 ^ 40 * 2254256 * 2
def baseEnd_2254256 : Nat := 1157516846281837446732871

theorem tailTrace_2254256 : CollatzResearch.WordTrace tailWord_2254256 prefixEnd_2254256 1157516846281837446732871 := by
  unfold tailWord_2254256
  simp only [CollatzResearch.WordTrace]
  refine ⟨41109735460611491559395311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54812980614148655412527081 41109735460611491559395311)
  ·
    refine ⟨61664603190917237339092967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41109735460611491559395311 61664603190917237339092967)
    ·
      refine ⟨92496904786375856008639451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61664603190917237339092967 92496904786375856008639451)
      ·
        refine ⟨138745357179563784012959177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92496904786375856008639451 138745357179563784012959177)
        ·
          refine ⟨104059017884672838009719383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138745357179563784012959177 104059017884672838009719383)
          ·
            refine ⟨156088526827009257014579075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104059017884672838009719383 156088526827009257014579075)
            ·
              refine ⟨234132790240513885521868613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156088526827009257014579075 234132790240513885521868613)
              ·
                refine ⟨43899898170096353535350365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234132790240513885521868613 43899898170096353535350365)
                ·
                  refine ⟨16462461813786132575756387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43899898170096353535350365 16462461813786132575756387)
                  ·
                    refine ⟨24693692720679198863634581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16462461813786132575756387 24693692720679198863634581)
                    ·
                      refine ⟨1157516846281837446732871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24693692720679198863634581 1157516846281837446732871)
                      ·
                        rfl

theorem cell23_2254256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_2254256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254256 prefixEnd_2254256 := by exact prefixLift 2254256
  have htrace : WordTrace (prefixWord ++ tailWord_2254256) baseStart_2254256 baseEnd_2254256 := by
    simpa [prefixWord, tailWord_2254256, baseEnd_2254256] using wordTrace_append hprefix tailTrace_2254256
  have hstable : (prefixWord ++ tailWord_2254256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254256).length < 2 ^ (prefixWord ++ tailWord_2254256).sum := by decide
  have hdescent : baseEnd_2254256 < baseStart_2254256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254294 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_2254294 : Nat := 118140960795 + 2254294 * 2 ^ 59
def prefixEnd_2254294 : Nat := 4983230072969 + 3 ^ 40 * 2254294 * 2
def baseEnd_2254294 : Nat := 1157536358546708298057697

theorem tailTrace_2254294 : CollatzResearch.WordTrace tailWord_2254294 prefixEnd_2254294 1157536358546708298057697 := by
  unfold tailWord_2254294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138803555942832225542121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54813904596723543739115957 5138803555942832225542121)
  ·
    refine ⟨3854102666957124169156591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5138803555942832225542121 3854102666957124169156591)
    ·
      refine ⟨5781154000435686253734887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3854102666957124169156591 5781154000435686253734887)
      ·
        refine ⟨8671731000653529380602331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5781154000435686253734887 8671731000653529380602331)
        ·
          refine ⟨13007596500980294070903497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8671731000653529380602331 13007596500980294070903497)
          ·
            refine ⟨9755697375735220553177623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13007596500980294070903497 9755697375735220553177623)
            ·
              refine ⟨14633546063602830829766435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9755697375735220553177623 14633546063602830829766435)
              ·
                refine ⟨21950319095404246244649653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14633546063602830829766435 21950319095404246244649653)
                ·
                  refine ⟨2057842415194148085435905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21950319095404246244649653 2057842415194148085435905)
                  ·
                    refine ⟨1543381811395611064076929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2057842415194148085435905 1543381811395611064076929)
                    ·
                      refine ⟨1157536358546708298057697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543381811395611064076929 1157536358546708298057697)
                      ·
                        rfl

theorem cell23_2254294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_2254294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254294 prefixEnd_2254294 := by exact prefixLift 2254294
  have htrace : WordTrace (prefixWord ++ tailWord_2254294) baseStart_2254294 baseEnd_2254294 := by
    simpa [prefixWord, tailWord_2254294, baseEnd_2254294] using wordTrace_append hprefix tailTrace_2254294
  have hstable : (prefixWord ++ tailWord_2254294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254294).length < 2 ^ (prefixWord ++ tailWord_2254294).sum := by decide
  have hdescent : baseEnd_2254294 < baseStart_2254294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254311 : List Nat := [1, 1, 5, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_2254311 : Nat := 118140960795 + 2254311 * 2 ^ 59
def prefixEnd_2254311 : Nat := 4983230072969 + 3 ^ 40 * 2254311 * 2
def baseEnd_2254311 : Nat := 1157545087717834731545119

theorem tailTrace_2254311 : CollatzResearch.WordTrace tailWord_2254311 prefixEnd_2254311 1157545087717834731545119 := by
  unfold tailWord_2254311
  simp only [CollatzResearch.WordTrace]
  refine ⟨82221476936023727512042787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54814317957349151674695191 82221476936023727512042787)
  ·
    refine ⟨123332215404035591268064181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82221476936023727512042787 123332215404035591268064181)
    ·
      refine ⟨11562395194128336681381017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123332215404035591268064181 11562395194128336681381017)
      ·
        refine ⟨8671796395596252511035763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11562395194128336681381017 8671796395596252511035763)
        ·
          refine ⟨13007694593394378766553645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8671796395596252511035763 13007694593394378766553645)
          ·
            refine ⟨4877885472522892037457617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13007694593394378766553645 4877885472522892037457617)
            ·
              refine ⟨3658414104392169028093213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4877885472522892037457617 3658414104392169028093213)
              ·
                refine ⟨1371905289147063385534955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3658414104392169028093213 1371905289147063385534955)
                ·
                  refine ⟨2057857933720595078302433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371905289147063385534955 2057857933720595078302433)
                  ·
                    refine ⟨1543393450290446308726825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2057857933720595078302433 1543393450290446308726825)
                    ·
                      refine ⟨1157545087717834731545119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543393450290446308726825 1157545087717834731545119)
                      ·
                        rfl

theorem cell23_2254311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_2254311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254311 prefixEnd_2254311 := by exact prefixLift 2254311
  have htrace : WordTrace (prefixWord ++ tailWord_2254311) baseStart_2254311 baseEnd_2254311 := by
    simpa [prefixWord, tailWord_2254311, baseEnd_2254311] using wordTrace_append hprefix tailTrace_2254311
  have hstable : (prefixWord ++ tailWord_2254311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254311).length < 2 ^ (prefixWord ++ tailWord_2254311).sum := by decide
  have hdescent : baseEnd_2254311 < baseStart_2254311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254353 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_2254353 : Nat := 118140960795 + 2254353 * 2 ^ 59
def prefixEnd_2254353 : Nat := 4983230072969 + 3 ^ 40 * 2254353 * 2
def baseEnd_2254353 : Nat := 1157566653905323567219925

theorem tailTrace_2254353 : CollatzResearch.WordTrace tailWord_2254353 prefixEnd_2254353 1157566653905323567219925 := by
  unfold tailWord_2254353
  simp only [CollatzResearch.WordTrace]
  refine ⟨82223008801871568685071713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54815339201247712456714475 82223008801871568685071713)
  ·
    refine ⟨61667256601403676513803785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82223008801871568685071713 61667256601403676513803785)
    ·
      refine ⟨46250442451052757385352839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61667256601403676513803785 46250442451052757385352839)
      ·
        refine ⟨69375663676579136078029259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46250442451052757385352839 69375663676579136078029259)
        ·
          refine ⟨104063495514868704117043889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69375663676579136078029259 104063495514868704117043889)
          ·
            refine ⟨78047621636151528087782917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104063495514868704117043889 78047621636151528087782917)
            ·
              refine ⟨14633929056778411516459297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78047621636151528087782917 14633929056778411516459297)
              ·
                refine ⟨10975446792583808637344473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14633929056778411516459297 10975446792583808637344473)
                ·
                  refine ⟨8231585094437856478008355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10975446792583808637344473 8231585094437856478008355)
                  ·
                    refine ⟨12347377641656784717012533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8231585094437856478008355 12347377641656784717012533)
                    ·
                      refine ⟨1157566653905323567219925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12347377641656784717012533 1157566653905323567219925)
                      ·
                        rfl

theorem cell23_2254353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_2254353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254353 prefixEnd_2254353 := by exact prefixLift 2254353
  have htrace : WordTrace (prefixWord ++ tailWord_2254353) baseStart_2254353 baseEnd_2254353 := by
    simpa [prefixWord, tailWord_2254353, baseEnd_2254353] using wordTrace_append hprefix tailTrace_2254353
  have hstable : (prefixWord ++ tailWord_2254353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254353).length < 2 ^ (prefixWord ++ tailWord_2254353).sum := by decide
  have hdescent : baseEnd_2254353 < baseStart_2254353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254367 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 4, 2, 2]
def baseStart_2254367 : Nat := 118140960795 + 2254367 * 2 ^ 59
def prefixEnd_2254367 : Nat := 4983230072969 + 3 ^ 40 * 2254367 * 2
def baseEnd_2254367 : Nat := 1157573842634486512444861

theorem tailTrace_2254367 : CollatzResearch.WordTrace tailWord_2254367 prefixEnd_2254367 1157573842634486512444861 := by
  unfold tailWord_2254367
  simp only [CollatzResearch.WordTrace]
  refine ⟨82223519423820849076081355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54815679615880566050720903 82223519423820849076081355)
  ·
    refine ⟨123335279135731273614122033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82223519423820849076081355 123335279135731273614122033)
    ·
      refine ⟨92501459351798455210591525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123335279135731273614122033 92501459351798455210591525)
      ·
        refine ⟨17344023628462210351985911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92501459351798455210591525 17344023628462210351985911)
        ·
          refine ⟨26016035442693315527978867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17344023628462210351985911 26016035442693315527978867)
          ·
            refine ⟨39024053164039973291968301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26016035442693315527978867 39024053164039973291968301)
            ·
              refine ⟨14634019936514989984488113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39024053164039973291968301 14634019936514989984488113)
              ·
                refine ⟨10975514952386242488366085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14634019936514989984488113 10975514952386242488366085)
                ·
                  refine ⟨2057909053572420466568641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10975514952386242488366085 2057909053572420466568641)
                  ·
                    refine ⟨1543431790179315349926481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2057909053572420466568641 1543431790179315349926481)
                    ·
                      refine ⟨1157573842634486512444861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543431790179315349926481 1157573842634486512444861)
                      ·
                        rfl

theorem cell23_2254367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_2254367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254367 prefixEnd_2254367 := by exact prefixLift 2254367
  have htrace : WordTrace (prefixWord ++ tailWord_2254367) baseStart_2254367 baseEnd_2254367 := by
    simpa [prefixWord, tailWord_2254367, baseEnd_2254367] using wordTrace_append hprefix tailTrace_2254367
  have hstable : (prefixWord ++ tailWord_2254367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254367).length < 2 ^ (prefixWord ++ tailWord_2254367).sum := by decide
  have hdescent : baseEnd_2254367 < baseStart_2254367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254457 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 2, 4, 2]
def baseStart_2254457 : Nat := 118140960795 + 2254457 * 2 ^ 59
def prefixEnd_2254457 : Nat := 4983230072969 + 3 ^ 40 * 2254457 * 2
def baseEnd_2254457 : Nat := 1157620055893391160319447

theorem tailTrace_2254457 : CollatzResearch.WordTrace tailWord_2254457 prefixEnd_2254457 1157620055893391160319447 := by
  unfold tailWord_2254457
  simp only [CollatzResearch.WordTrace]
  refine ⟨82226801993494794446857625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54817867995663196297905083 82226801993494794446857625)
  ·
    refine ⟨61670101495121095835143219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82226801993494794446857625 61670101495121095835143219)
    ·
      refine ⟨92505152242681643752714829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61670101495121095835143219 92505152242681643752714829)
      ·
        refine ⟨34689432091005616407268061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92505152242681643752714829 34689432091005616407268061)
        ·
          refine ⟨13008537034127106152725523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34689432091005616407268061 13008537034127106152725523)
          ·
            refine ⟨19512805551190659229088285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13008537034127106152725523 19512805551190659229088285)
            ·
              refine ⟨7317302081696497210908107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19512805551190659229088285 7317302081696497210908107)
              ·
                refine ⟨10975953122544745816362161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7317302081696497210908107 10975953122544745816362161)
                ·
                  refine ⟨8231964841908559362271621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10975953122544745816362161 8231964841908559362271621)
                  ·
                    refine ⟨1543493407857854880425929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8231964841908559362271621 1543493407857854880425929)
                    ·
                      refine ⟨1157620055893391160319447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543493407857854880425929 1157620055893391160319447)
                      ·
                        rfl

theorem cell23_2254457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_2254457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254457 prefixEnd_2254457 := by exact prefixLift 2254457
  have htrace : WordTrace (prefixWord ++ tailWord_2254457) baseStart_2254457 baseEnd_2254457 := by
    simpa [prefixWord, tailWord_2254457, baseEnd_2254457] using wordTrace_append hprefix tailTrace_2254457
  have hstable : (prefixWord ++ tailWord_2254457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254457).length < 2 ^ (prefixWord ++ tailWord_2254457).sum := by decide
  have hdescent : baseEnd_2254457 < baseStart_2254457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254460 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_2254460 : Nat := 118140960795 + 2254460 * 2 ^ 59
def prefixEnd_2254460 : Nat := 4983230072969 + 3 ^ 40 * 2254460 * 2
def baseEnd_2254460 : Nat := 1157621596335354648581933

theorem tailTrace_2254460 : CollatzResearch.WordTrace tailWord_2254460 prefixEnd_2254460 1157621596335354648581933 := by
  unfold tailWord_2254460
  simp only [CollatzResearch.WordTrace]
  refine ⟨41113455706241962979608417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54817940941655950639477889 41113455706241962979608417)
  ·
    refine ⟨30835091779681472234706313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41113455706241962979608417 30835091779681472234706313)
    ·
      refine ⟨23126318834761104176029735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30835091779681472234706313 23126318834761104176029735)
      ·
        refine ⟨34689478252141656264044603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23126318834761104176029735 34689478252141656264044603)
        ·
          refine ⟨52034217378212484396066905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34689478252141656264044603 52034217378212484396066905)
          ·
            refine ⟨39025663033659363297050179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52034217378212484396066905 39025663033659363297050179)
            ·
              refine ⟨58538494550489044945575269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39025663033659363297050179 58538494550489044945575269)
              ·
                refine ⟨10975967728216695927295363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58538494550489044945575269 10975967728216695927295363)
                ·
                  refine ⟨16463951592325043890943045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10975967728216695927295363 16463951592325043890943045)
                  ·
                    refine ⟨3086990923560945729551821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16463951592325043890943045 3086990923560945729551821)
                    ·
                      refine ⟨1157621596335354648581933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3086990923560945729551821 1157621596335354648581933)
                      ·
                        rfl

theorem cell23_2254460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_2254460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254460 prefixEnd_2254460 := by exact prefixLift 2254460
  have htrace : WordTrace (prefixWord ++ tailWord_2254460) baseStart_2254460 baseEnd_2254460 := by
    simpa [prefixWord, tailWord_2254460, baseEnd_2254460] using wordTrace_append hprefix tailTrace_2254460
  have hstable : (prefixWord ++ tailWord_2254460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254460).length < 2 ^ (prefixWord ++ tailWord_2254460).sum := by decide
  have hdescent : baseEnd_2254460 < baseStart_2254460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254474 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2254474 : Nat := 118140960795 + 2254474 * 2 ^ 59
def prefixEnd_2254474 : Nat := 4983230072969 + 3 ^ 40 * 2254474 * 2
def baseEnd_2254474 : Nat := 1157628785064517593806869

theorem tailTrace_2254474 : CollatzResearch.WordTrace tailWord_2254474 prefixEnd_2254474 1157628785064517593806869 := by
  unfold tailWord_2254474
  simp only [CollatzResearch.WordTrace]
  refine ⟨20556855508608301587556619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54818281356288804233484317 20556855508608301587556619)
  ·
    refine ⟨30835283262912452381334929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20556855508608301587556619 30835283262912452381334929)
    ·
      refine ⟨23126462447184339286001197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30835283262912452381334929 23126462447184339286001197)
      ·
        refine ⟨8672423417694127232250449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23126462447184339286001197 8672423417694127232250449)
        ·
          refine ⟨6504317563270595424187837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8672423417694127232250449 6504317563270595424187837)
          ·
            refine ⟨2439119086226473284070439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6504317563270595424187837 2439119086226473284070439)
            ·
              refine ⟨3658678629339709926105659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439119086226473284070439 3658678629339709926105659)
              ·
                refine ⟨5488017944009564889158489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658678629339709926105659 5488017944009564889158489)
                ·
                  refine ⟨4116013458007173666868867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5488017944009564889158489 4116013458007173666868867)
                  ·
                    refine ⟨6174020187010760500303301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4116013458007173666868867 6174020187010760500303301)
                    ·
                      refine ⟨1157628785064517593806869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6174020187010760500303301 1157628785064517593806869)
                      ·
                        rfl

theorem cell23_2254474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2254474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254474 prefixEnd_2254474 := by exact prefixLift 2254474
  have htrace : WordTrace (prefixWord ++ tailWord_2254474) baseStart_2254474 baseEnd_2254474 := by
    simpa [prefixWord, tailWord_2254474, baseEnd_2254474] using wordTrace_append hprefix tailTrace_2254474
  have hstable : (prefixWord ++ tailWord_2254474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254474).length < 2 ^ (prefixWord ++ tailWord_2254474).sum := by decide
  have hdescent : baseEnd_2254474 < baseStart_2254474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254483 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 8]
def baseStart_2254483 : Nat := 118140960795 + 2254483 * 2 ^ 59
def prefixEnd_2254483 : Nat := 4983230072969 + 3 ^ 40 * 2254483 * 2
def baseEnd_2254483 : Nat := 1157633406390408058594327

theorem tailTrace_2254483 : CollatzResearch.WordTrace tailWord_2254483 prefixEnd_2254483 1157633406390408058594327 := by
  unfold tailWord_2254483
  simp only [CollatzResearch.WordTrace]
  refine ⟨82227750291400600887304103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54818500194267067258202735 82227750291400600887304103)
  ·
    refine ⟨123341625437100901330956155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82227750291400600887304103 123341625437100901330956155)
    ·
      refine ⟨185012438155651351996434233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123341625437100901330956155 185012438155651351996434233)
      ·
        refine ⟨138759328616738513997325675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185012438155651351996434233 138759328616738513997325675)
        ·
          refine ⟨208138992925107770995988513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138759328616738513997325675 208138992925107770995988513)
          ·
            refine ⟨156104244693830828246991385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208138992925107770995988513 156104244693830828246991385)
            ·
              refine ⟨117078183520373121185243539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156104244693830828246991385 117078183520373121185243539)
              ·
                refine ⟨175617275280559681777865309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117078183520373121185243539 175617275280559681777865309)
                ·
                  refine ⟨65856478230209880666699491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175617275280559681777865309 65856478230209880666699491)
                  ·
                    refine ⟨98784717345314821000049237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65856478230209880666699491 98784717345314821000049237)
                    ·
                      refine ⟨1157633406390408058594327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 98784717345314821000049237 1157633406390408058594327)
                      ·
                        rfl

theorem cell23_2254483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_2254483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254483 prefixEnd_2254483 := by exact prefixLift 2254483
  have htrace : WordTrace (prefixWord ++ tailWord_2254483) baseStart_2254483 baseEnd_2254483 := by
    simpa [prefixWord, tailWord_2254483, baseEnd_2254483] using wordTrace_append hprefix tailTrace_2254483
  have hstable : (prefixWord ++ tailWord_2254483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254483).length < 2 ^ (prefixWord ++ tailWord_2254483).sum := by decide
  have hdescent : baseEnd_2254483 < baseStart_2254483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254497 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 6]
def baseStart_2254497 : Nat := 118140960795 + 2254497 * 2 ^ 59
def prefixEnd_2254497 : Nat := 4983230072969 + 3 ^ 40 * 2254497 * 2
def baseEnd_2254497 : Nat := 128626732791063444868807

theorem tailTrace_2254497 : CollatzResearch.WordTrace tailWord_2254497 prefixEnd_2254497 128626732791063444868807 := by
  unfold tailWord_2254497
  simp only [CollatzResearch.WordTrace]
  refine ⟨82228260913349881278313745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54818840608899920852209163 82228260913349881278313745)
  ·
    refine ⟨61671195685012410958735309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82228260913349881278313745 61671195685012410958735309)
    ·
      refine ⟨23126698381879654109525741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61671195685012410958735309 23126698381879654109525741)
      ·
        refine ⟨8672511893204870291072153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23126698381879654109525741 8672511893204870291072153)
        ·
          refine ⟨6504383919903652718304115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8672511893204870291072153 6504383919903652718304115)
          ·
            refine ⟨9756575879855479077456173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6504383919903652718304115 9756575879855479077456173)
            ·
              refine ⟨3658715954945804654046065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9756575879855479077456173 3658715954945804654046065)
              ·
                refine ⟨2744036966209353490534549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3658715954945804654046065 2744036966209353490534549)
                ·
                  refine ⟨128626732791063444868807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2744036966209353490534549 128626732791063444868807)
                  ·
                    rfl

theorem cell23_2254497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 6].length) (baseStart_2254497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254497 prefixEnd_2254497 := by exact prefixLift 2254497
  have htrace : WordTrace (prefixWord ++ tailWord_2254497) baseStart_2254497 baseEnd_2254497 := by
    simpa [prefixWord, tailWord_2254497, baseEnd_2254497] using wordTrace_append hprefix tailTrace_2254497
  have hstable : (prefixWord ++ tailWord_2254497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254497).length < 2 ^ (prefixWord ++ tailWord_2254497).sum := by decide
  have hdescent : baseEnd_2254497 < baseStart_2254497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254500 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_2254500 : Nat := 118140960795 + 2254500 * 2 ^ 59
def prefixEnd_2254500 : Nat := 4983230072969 + 3 ^ 40 * 2254500 * 2
def baseEnd_2254500 : Nat := 1157642135561534492081749

theorem tailTrace_2254500 : CollatzResearch.WordTrace tailWord_2254500 prefixEnd_2254500 1157642135561534492081749 := by
  unfold tailWord_2254500
  simp only [CollatzResearch.WordTrace]
  refine ⟨41114185166169506395336477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54818913554892675193781969 41114185166169506395336477)
  ·
    refine ⟨15417819437313564898251179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41114185166169506395336477 15417819437313564898251179)
    ·
      refine ⟨23126729155970347347376769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15417819437313564898251179 23126729155970347347376769)
      ·
        refine ⟨17345046866977760510532577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23126729155970347347376769 17345046866977760510532577)
        ·
          refine ⟨13008785150233320382899433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17345046866977760510532577 13008785150233320382899433)
          ·
            refine ⟨9756588862674990287174575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13008785150233320382899433 9756588862674990287174575)
            ·
              refine ⟨14634883294012485430761863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9756588862674990287174575 14634883294012485430761863)
              ·
                refine ⟨21952324941018728146142795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14634883294012485430761863 21952324941018728146142795)
                ·
                  refine ⟨32928487411528092219214193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21952324941018728146142795 32928487411528092219214193)
                  ·
                    refine ⟨24696365558646069164410645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32928487411528092219214193 24696365558646069164410645)
                    ·
                      refine ⟨1157642135561534492081749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24696365558646069164410645 1157642135561534492081749)
                      ·
                        rfl

theorem cell23_2254500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_2254500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254500 prefixEnd_2254500 := by exact prefixLift 2254500
  have htrace : WordTrace (prefixWord ++ tailWord_2254500) baseStart_2254500 baseEnd_2254500 := by
    simpa [prefixWord, tailWord_2254500, baseEnd_2254500] using wordTrace_append hprefix tailTrace_2254500
  have hstable : (prefixWord ++ tailWord_2254500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254500).length < 2 ^ (prefixWord ++ tailWord_2254500).sum := by decide
  have hdescent : baseEnd_2254500 < baseStart_2254500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254524 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_2254524 : Nat := 118140960795 + 2254524 * 2 ^ 59
def prefixEnd_2254524 : Nat := 4983230072969 + 3 ^ 40 * 2254524 * 2
def baseEnd_2254524 : Nat := 1157654459097242398181639

theorem tailTrace_2254524 : CollatzResearch.WordTrace tailWord_2254524 prefixEnd_2254524 1157654459097242398181639 := by
  unfold tailWord_2254524
  simp only [CollatzResearch.WordTrace]
  refine ⟨41114622842126032444773313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54819497122834709926364417 41114622842126032444773313)
  ·
    refine ⟨30835967131594524333579985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41114622842126032444773313 30835967131594524333579985)
    ·
      refine ⟨23126975348695893250184989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30835967131594524333579985 23126975348695893250184989)
      ·
        refine ⟨8672615755760959968819371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23126975348695893250184989 8672615755760959968819371)
        ·
          refine ⟨13008923633641439953229057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8672615755760959968819371 13008923633641439953229057)
          ·
            refine ⟨9756692725231079964921793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13008923633641439953229057 9756692725231079964921793)
            ·
              refine ⟨7317519543923309973691345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9756692725231079964921793 7317519543923309973691345)
              ·
                refine ⟨5488139657942482480268509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7317519543923309973691345 5488139657942482480268509)
                ·
                  refine ⟨2058052371728430930100691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5488139657942482480268509 2058052371728430930100691)
                  ·
                    refine ⟨3087078557592646395151037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2058052371728430930100691 3087078557592646395151037)
                    ·
                      refine ⟨1157654459097242398181639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3087078557592646395151037 1157654459097242398181639)
                      ·
                        rfl

theorem cell23_2254524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_2254524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254524 prefixEnd_2254524 := by exact prefixLift 2254524
  have htrace : WordTrace (prefixWord ++ tailWord_2254524) baseStart_2254524 baseEnd_2254524 := by
    simpa [prefixWord, tailWord_2254524, baseEnd_2254524] using wordTrace_append hprefix tailTrace_2254524
  have hstable : (prefixWord ++ tailWord_2254524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254524).length < 2 ^ (prefixWord ++ tailWord_2254524).sum := by decide
  have hdescent : baseEnd_2254524 < baseStart_2254524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254527 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 1, 5]
def baseStart_2254527 : Nat := 118140960795 + 2254527 * 2 ^ 59
def prefixEnd_2254527 : Nat := 4983230072969 + 3 ^ 40 * 2254527 * 2
def baseEnd_2254527 : Nat := 385885333179735295481375

theorem tailTrace_2254527 : CollatzResearch.WordTrace tailWord_2254527 prefixEnd_2254527 385885333179735295481375 := by
  unfold tailWord_2254527
  simp only [CollatzResearch.WordTrace]
  refine ⟨82229355103241196401905835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54819570068827464267937223 82229355103241196401905835)
  ·
    refine ⟨123344032654861794602858753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82229355103241196401905835 123344032654861794602858753)
    ·
      refine ⟨92508024491146345952144065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123344032654861794602858753 92508024491146345952144065)
      ·
        refine ⟨69381018368359759464108049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92508024491146345952144065 69381018368359759464108049)
        ·
          refine ⟨52035763776269819598081037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69381018368359759464108049 52035763776269819598081037)
          ·
            refine ⟨19513411416101182349280389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52035763776269819598081037 19513411416101182349280389)
            ·
              refine ⟨3658764640518971690490073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19513411416101182349280389 3658764640518971690490073)
              ·
                refine ⟨2744073480389228767867555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3658764640518971690490073 2744073480389228767867555)
                ·
                  refine ⟨4116110220583843151801333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744073480389228767867555 4116110220583843151801333)
                  ·
                    refine ⟨385885333179735295481375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4116110220583843151801333 385885333179735295481375)
                    ·
                      rfl

theorem cell23_2254527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_2254527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254527 prefixEnd_2254527 := by exact prefixLift 2254527
  have htrace : WordTrace (prefixWord ++ tailWord_2254527) baseStart_2254527 baseEnd_2254527 := by
    simpa [prefixWord, tailWord_2254527, baseEnd_2254527] using wordTrace_append hprefix tailTrace_2254527
  have hstable : (prefixWord ++ tailWord_2254527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254527).length < 2 ^ (prefixWord ++ tailWord_2254527).sum := by decide
  have hdescent : baseEnd_2254527 < baseStart_2254527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254560 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2254560 : Nat := 118140960795 + 2254560 * 2 ^ 59
def prefixEnd_2254560 : Nat := 4983230072969 + 3 ^ 40 * 2254560 * 2
def baseEnd_2254560 : Nat := 1157672944400804257331473

theorem tailTrace_2254560 : CollatzResearch.WordTrace tailWord_2254560 prefixEnd_2254560 1157672944400804257331473 := by
  unfold tailWord_2254560
  simp only [CollatzResearch.WordTrace]
  refine ⟨41115279356060821518928567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54820372474747762025238089 41115279356060821518928567)
  ·
    refine ⟨61672919034091232278392851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41115279356060821518928567 61672919034091232278392851)
    ·
      refine ⟨92509378551136848417589277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61672919034091232278392851 92509378551136848417589277)
      ·
        refine ⟨34691016956676318156595979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92509378551136848417589277 34691016956676318156595979)
        ·
          refine ⟨52036525435014477234893969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34691016956676318156595979 52036525435014477234893969)
          ·
            refine ⟨39027394076260857926170477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52036525435014477234893969 39027394076260857926170477)
            ·
              refine ⟨14635272778597821722313929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39027394076260857926170477 14635272778597821722313929)
              ·
                refine ⟨10976454583948366291735447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14635272778597821722313929 10976454583948366291735447)
                ·
                  refine ⟨16464681875922549437603171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10976454583948366291735447 16464681875922549437603171)
                  ·
                    refine ⟨24697022813883824156404757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16464681875922549437603171 24697022813883824156404757)
                    ·
                      refine ⟨1157672944400804257331473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24697022813883824156404757 1157672944400804257331473)
                      ·
                        rfl

theorem cell23_2254560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2254560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254560 prefixEnd_2254560 := by exact prefixLift 2254560
  have htrace : WordTrace (prefixWord ++ tailWord_2254560) baseStart_2254560 baseEnd_2254560 := by
    simpa [prefixWord, tailWord_2254560, baseEnd_2254560] using wordTrace_append hprefix tailTrace_2254560
  have hstable : (prefixWord ++ tailWord_2254560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254560).length < 2 ^ (prefixWord ++ tailWord_2254560).sum := by decide
  have hdescent : baseEnd_2254560 < baseStart_2254560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254570 : List Nat := [3, 1, 3, 1, 1, 1, 3, 10]
def baseStart_2254570 : Nat := 118140960795 + 2254570 * 2 ^ 59
def prefixEnd_2254570 : Nat := 4983230072969 + 3 ^ 40 * 2254570 * 2
def baseEnd_2254570 : Nat := 42876965896568489563201

theorem tailTrace_2254570 : CollatzResearch.WordTrace tailWord_2254570 prefixEnd_2254570 42876965896568489563201 := by
  unfold tailWord_2254570
  simp only [CollatzResearch.WordTrace]
  refine ⟨20557730860521353686430291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54820615628056943163814109 20557730860521353686430291)
  ·
    refine ⟨30836596290782030529645437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20557730860521353686430291 30836596290782030529645437)
    ·
      refine ⟨11563723609043261448617039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30836596290782030529645437 11563723609043261448617039)
      ·
        refine ⟨17345585413564892172925559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11563723609043261448617039 17345585413564892172925559)
        ·
          refine ⟨26018378120347338259388339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17345585413564892172925559 26018378120347338259388339)
          ·
            refine ⟨39027567180521007389082509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26018378120347338259388339 39027567180521007389082509)
            ·
              refine ⟨14635337692695377770905941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39027567180521007389082509 14635337692695377770905941)
              ·
                refine ⟨42876965896568489563201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14635337692695377770905941 42876965896568489563201)
                ·
                  rfl

theorem cell23_2254570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 10].length) (baseStart_2254570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254570 prefixEnd_2254570 := by exact prefixLift 2254570
  have htrace : WordTrace (prefixWord ++ tailWord_2254570) baseStart_2254570 baseEnd_2254570 := by
    simpa [prefixWord, tailWord_2254570, baseEnd_2254570] using wordTrace_append hprefix tailTrace_2254570
  have hstable : (prefixWord ++ tailWord_2254570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254570).length < 2 ^ (prefixWord ++ tailWord_2254570).sum := by decide
  have hdescent : baseEnd_2254570 < baseStart_2254570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254574 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2254574 : Nat := 118140960795 + 2254574 * 2 ^ 59
def prefixEnd_2254574 : Nat := 4983230072969 + 3 ^ 40 * 2254574 * 2
def baseEnd_2254574 : Nat := 385893377709989067518803

theorem tailTrace_2254574 : CollatzResearch.WordTrace tailWord_2254574 prefixEnd_2254574 385893377709989067518803 := by
  unfold tailWord_2254574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10278883666758865428608347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54820712889380615619244517 10278883666758865428608347)
  ·
    refine ⟨15418325500138298142912521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10278883666758865428608347 15418325500138298142912521)
    ·
      refine ⟨11563744125103723607184391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15418325500138298142912521 11563744125103723607184391)
      ·
        refine ⟨17345616187655585410776587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11563744125103723607184391 17345616187655585410776587)
        ·
          refine ⟨26018424281483378116164881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17345616187655585410776587 26018424281483378116164881)
          ·
            refine ⟨19513818211112533587123661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26018424281483378116164881 19513818211112533587123661)
            ·
              refine ⟨7317681829167200095171373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19513818211112533587123661 7317681829167200095171373)
              ·
                refine ⟨2744130685937700035689265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7317681829167200095171373 2744130685937700035689265)
                ·
                  refine ⟨2058098014453275026766949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2744130685937700035689265 2058098014453275026766949)
                  ·
                    refine ⟨385893377709989067518803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2058098014453275026766949 385893377709989067518803)
                    ·
                      rfl

theorem cell23_2254574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2254574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254574 prefixEnd_2254574 := by exact prefixLift 2254574
  have htrace : WordTrace (prefixWord ++ tailWord_2254574) baseStart_2254574 baseEnd_2254574 := by
    simpa [prefixWord, tailWord_2254574, baseEnd_2254574] using wordTrace_append hprefix tailTrace_2254574
  have hstable : (prefixWord ++ tailWord_2254574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254574).length < 2 ^ (prefixWord ++ tailWord_2254574).sum := by decide
  have hdescent : baseEnd_2254574 < baseStart_2254574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254594 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2254594 : Nat := 118140960795 + 2254594 * 2 ^ 59
def prefixEnd_2254594 : Nat := 4983230072969 + 3 ^ 40 * 2254594 * 2
def baseEnd_2254594 : Nat := 1157690402743057124306317

theorem tailTrace_2254594 : CollatzResearch.WordTrace tailWord_2254594 prefixEnd_2254594 1157690402743057124306317 := by
  unfold tailWord_2254594
  simp only [CollatzResearch.WordTrace]
  refine ⟨20557949698499616711148709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54821199195998977896396557 20557949698499616711148709)
  ·
    refine ⟨3854615568468678133340383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20557949698499616711148709 3854615568468678133340383)
    ·
      refine ⟨5781923352703017200010575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3854615568468678133340383 5781923352703017200010575)
      ·
        refine ⟨8672885029054525800015863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5781923352703017200010575 8672885029054525800015863)
        ·
          refine ⟨13009327543581788700023795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8672885029054525800015863 13009327543581788700023795)
          ·
            refine ⟨19513991315372683050035693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13009327543581788700023795 19513991315372683050035693)
            ·
              refine ⟨7317746743264756143763385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19513991315372683050035693 7317746743264756143763385)
              ·
                refine ⟨5488310057448567107822539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7317746743264756143763385 5488310057448567107822539)
                ·
                  refine ⟨8232465086172850661733809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5488310057448567107822539 8232465086172850661733809)
                  ·
                    refine ⟨6174348814629637996300357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8232465086172850661733809 6174348814629637996300357)
                    ·
                      refine ⟨1157690402743057124306317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6174348814629637996300357 1157690402743057124306317)
                      ·
                        rfl

theorem cell23_2254594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2254594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254594 prefixEnd_2254594 := by exact prefixLift 2254594
  have htrace : WordTrace (prefixWord ++ tailWord_2254594) baseStart_2254594 baseEnd_2254594 := by
    simpa [prefixWord, tailWord_2254594, baseEnd_2254594] using wordTrace_append hprefix tailTrace_2254594
  have hstable : (prefixWord ++ tailWord_2254594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254594).length < 2 ^ (prefixWord ++ tailWord_2254594).sum := by decide
  have hdescent : baseEnd_2254594 < baseStart_2254594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254615 : List Nat := [1, 1, 3, 4, 2, 1, 4, 2, 1, 2, 2]
def baseStart_2254615 : Nat := 118140960795 + 2254615 * 2 ^ 59
def prefixEnd_2254615 : Nat := 4983230072969 + 3 ^ 40 * 2254615 * 2
def baseEnd_2254615 : Nat := 1157701185836801542143721

theorem tailTrace_2254615 : CollatzResearch.WordTrace tailWord_2254615 prefixEnd_2254615 1157701185836801542143721 := by
  unfold tailWord_2254615
  simp only [CollatzResearch.WordTrace]
  refine ⟨82232564726922387431109299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54821709817948258287406199 82232564726922387431109299)
  ·
    refine ⟨123348847090383581146663949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82232564726922387431109299 123348847090383581146663949)
    ·
      refine ⟨46255817658893842929998981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123348847090383581146663949 46255817658893842929998981)
      ·
        refine ⟨8672965811042595549374809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46255817658893842929998981 8672965811042595549374809)
        ·
          refine ⟨6504724358281946662031107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8672965811042595549374809 6504724358281946662031107)
          ·
            refine ⟨9757086537422919993046661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6504724358281946662031107 9757086537422919993046661)
            ·
              refine ⟨1829453725766797498696249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9757086537422919993046661 1829453725766797498696249)
              ·
                refine ⟨1372090294325098124022187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829453725766797498696249 1372090294325098124022187)
                ·
                  refine ⟨2058135441487647186033281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372090294325098124022187 2058135441487647186033281)
                  ·
                    refine ⟨1543601581115735389524961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2058135441487647186033281 1543601581115735389524961)
                    ·
                      refine ⟨1157701185836801542143721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543601581115735389524961 1157701185836801542143721)
                      ·
                        rfl

theorem cell23_2254615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_2254615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254615 prefixEnd_2254615 := by exact prefixLift 2254615
  have htrace : WordTrace (prefixWord ++ tailWord_2254615) baseStart_2254615 baseEnd_2254615 := by
    simpa [prefixWord, tailWord_2254615, baseEnd_2254615] using wordTrace_append hprefix tailTrace_2254615
  have hstable : (prefixWord ++ tailWord_2254615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254615).length < 2 ^ (prefixWord ++ tailWord_2254615).sum := by decide
  have hdescent : baseEnd_2254615 < baseStart_2254615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254624 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 5, 3, 2]
def baseStart_2254624 : Nat := 118140960795 + 2254624 * 2 ^ 59
def prefixEnd_2254624 : Nat := 4983230072969 + 3 ^ 40 * 2254624 * 2
def baseEnd_2254624 : Nat := 1157705807162692006931179

theorem tailTrace_2254624 : CollatzResearch.WordTrace tailWord_2254624 prefixEnd_2254624 1157705807162692006931179 := by
  unfold tailWord_2254624
  simp only [CollatzResearch.WordTrace]
  refine ⟨41116446491944890984093463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54821928655926521312124617 41116446491944890984093463)
  ·
    refine ⟨61674669737917336476140195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41116446491944890984093463 61674669737917336476140195)
    ·
      refine ⟨92512004606876004714210293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61674669737917336476140195 92512004606876004714210293)
      ·
        refine ⟨8673000431894625441957215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92512004606876004714210293 8673000431894625441957215)
        ·
          refine ⟨13009500647841938162935823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8673000431894625441957215 13009500647841938162935823)
          ·
            refine ⟨19514250971762907244403735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13009500647841938162935823 19514250971762907244403735)
            ·
              refine ⟨29271376457644360866605603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19514250971762907244403735 29271376457644360866605603)
              ·
                refine ⟨43907064686466541299908405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29271376457644360866605603 43907064686466541299908405)
                ·
                  refine ⟨4116287314356238246866413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43907064686466541299908405 4116287314356238246866413)
                  ·
                    refine ⟨1543607742883589342574905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4116287314356238246866413 1543607742883589342574905)
                    ·
                      refine ⟨1157705807162692006931179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543607742883589342574905 1157705807162692006931179)
                      ·
                        rfl

theorem cell23_2254624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_2254624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254624 prefixEnd_2254624 := by exact prefixLift 2254624
  have htrace : WordTrace (prefixWord ++ tailWord_2254624) baseStart_2254624 baseEnd_2254624 := by
    simpa [prefixWord, tailWord_2254624, baseEnd_2254624] using wordTrace_append hprefix tailTrace_2254624
  have hstable : (prefixWord ++ tailWord_2254624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254624).length < 2 ^ (prefixWord ++ tailWord_2254624).sum := by decide
  have hdescent : baseEnd_2254624 < baseStart_2254624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254677 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 7]
def baseStart_2254677 : Nat := 118140960795 + 2254677 * 2 ^ 59
def prefixEnd_2254677 : Nat := 4983230072969 + 3 ^ 40 * 2254677 * 2
def baseEnd_2254677 : Nat := 128637002404153366618715

theorem tailTrace_2254677 : CollatzResearch.WordTrace tailWord_2254677 prefixEnd_2254677 128637002404153366618715 := by
  unfold tailWord_2254677
  simp only [CollatzResearch.WordTrace]
  refine ⟨82234826052697772019866285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54823217368465181346577523 82234826052697772019866285)
  ·
    refine ⟨30838059769761664507449857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82234826052697772019866285 30838059769761664507449857)
    ·
      refine ⟨23128544827321248380587393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30838059769761664507449857 23128544827321248380587393)
      ·
        refine ⟨17346408620490936285440545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23128544827321248380587393 17346408620490936285440545)
        ·
          refine ⟨13009806465368202214080409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17346408620490936285440545 13009806465368202214080409)
          ·
            refine ⟨9757354849026151660560307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13009806465368202214080409 9757354849026151660560307)
            ·
              refine ⟨14636032273539227490840461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9757354849026151660560307 14636032273539227490840461)
              ·
                refine ⟨5488512102577210309065173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14636032273539227490840461 5488512102577210309065173)
                ·
                  refine ⟨128637002404153366618715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5488512102577210309065173 128637002404153366618715)
                  ·
                    rfl

theorem cell23_2254677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_2254677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254677 prefixEnd_2254677 := by exact prefixLift 2254677
  have htrace : WordTrace (prefixWord ++ tailWord_2254677) baseStart_2254677 baseEnd_2254677 := by
    simpa [prefixWord, tailWord_2254677, baseEnd_2254677] using wordTrace_append hprefix tailTrace_2254677
  have hstable : (prefixWord ++ tailWord_2254677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254677).length < 2 ^ (prefixWord ++ tailWord_2254677).sum := by decide
  have hdescent : baseEnd_2254677 < baseStart_2254677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254707 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 2, 5]
def baseStart_2254707 : Nat := 118140960795 + 2254707 * 2 ^ 59
def prefixEnd_2254707 : Nat := 4983230072969 + 3 ^ 40 * 2254707 * 2
def baseEnd_2254707 : Nat := 385916142019005060731099

theorem tailTrace_2254707 : CollatzResearch.WordTrace tailWord_2254707 prefixEnd_2254707 385916142019005060731099 := by
  unfold tailWord_2254707
  simp only [CollatzResearch.WordTrace]
  refine ⟨82235920242589087143458375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54823946828392724762305583 82235920242589087143458375)
  ·
    refine ⟨123353880363883630715187563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82235920242589087143458375 123353880363883630715187563)
    ·
      refine ⟨185030820545825446072781345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123353880363883630715187563 185030820545825446072781345)
      ·
        refine ⟨138773115409369084554586009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185030820545825446072781345 138773115409369084554586009)
        ·
          refine ⟨104079836557026813415939507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138773115409369084554586009 104079836557026813415939507)
          ·
            refine ⟨156119754835540220123909261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104079836557026813415939507 156119754835540220123909261)
            ·
              refine ⟨58544908063327582546465973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156119754835540220123909261 58544908063327582546465973)
              ·
                refine ⟨5488585130936960863731185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58544908063327582546465973 5488585130936960863731185)
                ·
                  refine ⟨4116438848202720647798389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5488585130936960863731185 4116438848202720647798389)
                  ·
                    refine ⟨385916142019005060731099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4116438848202720647798389 385916142019005060731099)
                    ·
                      rfl

theorem cell23_2254707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 5].length) (baseStart_2254707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254707 prefixEnd_2254707 := by exact prefixLift 2254707
  have htrace : WordTrace (prefixWord ++ tailWord_2254707) baseStart_2254707 baseEnd_2254707 := by
    simpa [prefixWord, tailWord_2254707, baseEnd_2254707] using wordTrace_append hprefix tailTrace_2254707
  have hstable : (prefixWord ++ tailWord_2254707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254707).length < 2 ^ (prefixWord ++ tailWord_2254707).sum := by decide
  have hdescent : baseEnd_2254707 < baseStart_2254707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254717 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_2254717 : Nat := 118140960795 + 2254717 * 2 ^ 59
def prefixEnd_2254717 : Nat := 4983230072969 + 3 ^ 40 * 2254717 * 2
def baseEnd_2254717 : Nat := 1157753560863560143068251

theorem tailTrace_2254717 : CollatzResearch.WordTrace tailWord_2254717 prefixEnd_2254717 1157753560863560143068251 := by
  unfold tailWord_2254717
  simp only [CollatzResearch.WordTrace]
  refine ⟨82236284972552858851322405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54824189981701905900881603 82236284972552858851322405)
  ·
    refine ⟨15419303432353661034622951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82236284972552858851322405 15419303432353661034622951)
    ·
      refine ⟨23128955148530491551934427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15419303432353661034622951 23128955148530491551934427)
      ·
        refine ⟨34693432722795737327901641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23128955148530491551934427 34693432722795737327901641)
        ·
          refine ⟨26020074542096802995926231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34693432722795737327901641 26020074542096802995926231)
          ·
            refine ⟨39030111813145204493889347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26020074542096802995926231 39030111813145204493889347)
            ·
              refine ⟨58545167719717806740834021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39030111813145204493889347 58545167719717806740834021)
              ·
                refine ⟨10977218947447088763906379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58545167719717806740834021 10977218947447088763906379)
                ·
                  refine ⟨16465828421170633145859569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10977218947447088763906379 16465828421170633145859569)
                  ·
                    refine ⟨12349371315877974859394677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16465828421170633145859569 12349371315877974859394677)
                    ·
                      refine ⟨1157753560863560143068251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12349371315877974859394677 1157753560863560143068251)
                      ·
                        rfl

theorem cell23_2254717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_2254717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254717 prefixEnd_2254717 := by exact prefixLift 2254717
  have htrace : WordTrace (prefixWord ++ tailWord_2254717) baseStart_2254717 baseEnd_2254717 := by
    simpa [prefixWord, tailWord_2254717, baseEnd_2254717] using wordTrace_append hprefix tailTrace_2254717
  have hstable : (prefixWord ++ tailWord_2254717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254717).length < 2 ^ (prefixWord ++ tailWord_2254717).sum := by decide
  have hdescent : baseEnd_2254717 < baseStart_2254717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254728 : List Nat := [2, 1, 3, 3, 3, 1, 3, 2, 5]
def baseStart_2254728 : Nat := 118140960795 + 2254728 * 2 ^ 59
def prefixEnd_2254728 : Nat := 4983230072969 + 3 ^ 40 * 2254728 * 2
def baseEnd_2254728 : Nat := 128639912127862177781189

theorem tailTrace_2254728 : CollatzResearch.WordTrace tailWord_2254728 prefixEnd_2254728 128639912127862177781189 := by
  unfold tailWord_2254728
  simp only [CollatzResearch.WordTrace]
  refine ⟨41118343087756503864986419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54824457450342005153315225 41118343087756503864986419)
  ·
    refine ⟨61677514631634755797479629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41118343087756503864986419 61677514631634755797479629)
    ·
      refine ⟨23129067986863033424054861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61677514631634755797479629 23129067986863033424054861)
      ·
        refine ⟨8673400495073637534020573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23129067986863033424054861 8673400495073637534020573)
        ·
          refine ⟨3252525185652614075257715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8673400495073637534020573 3252525185652614075257715)
          ·
            refine ⟨4878787778478921112886573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252525185652614075257715 4878787778478921112886573)
            ·
              refine ⟨1829545416929595417332465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4878787778478921112886573 1829545416929595417332465)
              ·
                refine ⟨1372159062697196562999349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829545416929595417332465 1372159062697196562999349)
                ·
                  refine ⟨128639912127862177781189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1372159062697196562999349 128639912127862177781189)
                  ·
                    rfl

theorem cell23_2254728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 5].length) (baseStart_2254728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254728 prefixEnd_2254728 := by exact prefixLift 2254728
  have htrace : WordTrace (prefixWord ++ tailWord_2254728) baseStart_2254728 baseEnd_2254728 := by
    simpa [prefixWord, tailWord_2254728, baseEnd_2254728] using wordTrace_append hprefix tailTrace_2254728
  have hstable : (prefixWord ++ tailWord_2254728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254728).length < 2 ^ (prefixWord ++ tailWord_2254728).sum := by decide
  have hdescent : baseEnd_2254728 < baseStart_2254728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254757 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_2254757 : Nat := 118140960795 + 2254757 * 2 ^ 59
def prefixEnd_2254757 : Nat := 4983230072969 + 3 ^ 40 * 2254757 * 2
def baseEnd_2254757 : Nat := 1157774100089739986568067

theorem tailTrace_2254757 : CollatzResearch.WordTrace tailWord_2254757 prefixEnd_2254757 1157774100089739986568067 := by
  unfold tailWord_2254757
  simp only [CollatzResearch.WordTrace]
  refine ⟨82237743892407945682778525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54825162594938630455185683 82237743892407945682778525)
  ·
    refine ⟨30839153959652979631041947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82237743892407945682778525 30839153959652979631041947)
    ·
      refine ⟨46258730939479469446562921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30839153959652979631041947 46258730939479469446562921)
      ·
        refine ⟨34694048204609602084922191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46258730939479469446562921 34694048204609602084922191)
        ·
          refine ⟨52041072306914403127383287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34694048204609602084922191 52041072306914403127383287)
          ·
            refine ⟨78061608460371604691074931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52041072306914403127383287 78061608460371604691074931)
            ·
              refine ⟨117092412690557407036612397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78061608460371604691074931 117092412690557407036612397)
              ·
                refine ⟨43909654758959027638729649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117092412690557407036612397 43909654758959027638729649)
                ·
                  refine ⟨32932241069219270729047237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43909654758959027638729649 32932241069219270729047237)
                  ·
                    refine ⟨6174795200478613261696357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32932241069219270729047237 6174795200478613261696357)
                    ·
                      refine ⟨1157774100089739986568067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6174795200478613261696357 1157774100089739986568067)
                      ·
                        rfl

theorem cell23_2254757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_2254757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254757 prefixEnd_2254757 := by exact prefixLift 2254757
  have htrace : WordTrace (prefixWord ++ tailWord_2254757) baseStart_2254757 baseEnd_2254757 := by
    simpa [prefixWord, tailWord_2254757, baseEnd_2254757] using wordTrace_append hprefix tailTrace_2254757
  have hstable : (prefixWord ++ tailWord_2254757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254757).length < 2 ^ (prefixWord ++ tailWord_2254757).sum := by decide
  have hdescent : baseEnd_2254757 < baseStart_2254757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254771 : List Nat := [1, 1, 1, 2, 3, 1, 4, 5, 1, 4]
def baseStart_2254771 : Nat := 118140960795 + 2254771 * 2 ^ 59
def prefixEnd_2254771 : Nat := 4983230072969 + 3 ^ 40 * 2254771 * 2
def baseEnd_2254771 : Nat := 385927096272967643931001

theorem tailTrace_2254771 : CollatzResearch.WordTrace tailWord_2254771 prefixEnd_2254771 385927096272967643931001 := by
  unfold tailWord_2254771
  simp only [CollatzResearch.WordTrace]
  refine ⟨82238254514357226073788167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54825503009571484049192111 82238254514357226073788167)
  ·
    refine ⟨123357381771535839110682251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82238254514357226073788167 123357381771535839110682251)
    ·
      refine ⟨185036072657303758666023377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123357381771535839110682251 185036072657303758666023377)
      ·
        refine ⟨138777054492977818999517533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185036072657303758666023377 138777054492977818999517533)
        ·
          refine ⟨52041395434866682124819075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138777054492977818999517533 52041395434866682124819075)
          ·
            refine ⟨78062093152300023187228613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52041395434866682124819075 78062093152300023187228613)
            ·
              refine ⟨14636642466056254347605365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78062093152300023187228613 14636642466056254347605365)
              ·
                refine ⟨1372185231192773845088003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14636642466056254347605365 1372185231192773845088003)
                ·
                  refine ⟨2058277846789160767632005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372185231192773845088003 2058277846789160767632005)
                  ·
                    refine ⟨385927096272967643931001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2058277846789160767632005 385927096272967643931001)
                    ·
                      rfl

theorem cell23_2254771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 4].length) (baseStart_2254771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254771 prefixEnd_2254771 := by exact prefixLift 2254771
  have htrace : WordTrace (prefixWord ++ tailWord_2254771) baseStart_2254771 baseEnd_2254771 := by
    simpa [prefixWord, tailWord_2254771, baseEnd_2254771] using wordTrace_append hprefix tailTrace_2254771
  have hstable : (prefixWord ++ tailWord_2254771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254771).length < 2 ^ (prefixWord ++ tailWord_2254771).sum := by decide
  have hdescent : baseEnd_2254771 < baseStart_2254771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254781 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_2254781 : Nat := 118140960795 + 2254781 * 2 ^ 59
def prefixEnd_2254781 : Nat := 4983230072969 + 3 ^ 40 * 2254781 * 2
def baseEnd_2254781 : Nat := 1157786423625447892667957

theorem tailTrace_2254781 : CollatzResearch.WordTrace tailWord_2254781 prefixEnd_2254781 1157786423625447892667957 := by
  unfold tailWord_2254781
  simp only [CollatzResearch.WordTrace]
  refine ⟨82238619244320997781652197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54825746162880665187768131 82238619244320997781652197)
  ·
    refine ⟨15419741108310187084059787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82238619244320997781652197 15419741108310187084059787)
    ·
      refine ⟨23129611662465280626089681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15419741108310187084059787 23129611662465280626089681)
      ·
        refine ⟨17347208746848960469567261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23129611662465280626089681 17347208746848960469567261)
        ·
          refine ⟨6505203280068360176087723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17347208746848960469567261 6505203280068360176087723)
          ·
            refine ⟨9757804920102540264131585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6505203280068360176087723 9757804920102540264131585)
            ·
              refine ⟨7318353690076905198098689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9757804920102540264131585 7318353690076905198098689)
              ·
                refine ⟨5488765267557678898574017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7318353690076905198098689 5488765267557678898574017)
                ·
                  refine ⟨4116573950668259173930513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5488765267557678898574017 4116573950668259173930513)
                  ·
                    refine ⟨3087430463001194380447885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4116573950668259173930513 3087430463001194380447885)
                    ·
                      refine ⟨1157786423625447892667957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3087430463001194380447885 1157786423625447892667957)
                      ·
                        rfl

theorem cell23_2254781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_2254781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254781 prefixEnd_2254781 := by exact prefixLift 2254781
  have htrace : WordTrace (prefixWord ++ tailWord_2254781) baseStart_2254781 baseEnd_2254781 := by
    simpa [prefixWord, tailWord_2254781, baseEnd_2254781] using wordTrace_append hprefix tailTrace_2254781
  have hstable : (prefixWord ++ tailWord_2254781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254781).length < 2 ^ (prefixWord ++ tailWord_2254781).sum := by decide
  have hdescent : baseEnd_2254781 < baseStart_2254781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254784 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 6]
def baseStart_2254784 : Nat := 118140960795 + 2254784 * 2 ^ 59
def prefixEnd_2254784 : Nat := 4983230072969 + 3 ^ 40 * 2254784 * 2
def baseEnd_2254784 : Nat := 128643107118601264547827

theorem tailTrace_2254784 : CollatzResearch.WordTrace tailWord_2254784 prefixEnd_2254784 128643107118601264547827 := by
  unfold tailWord_2254784
  simp only [CollatzResearch.WordTrace]
  refine ⟨41119364331655064647005703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54825819108873419529340937 41119364331655064647005703)
  ·
    refine ⟨61679046497482596970508555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41119364331655064647005703 61679046497482596970508555)
    ·
      refine ⟨92518569746223895455762833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61679046497482596970508555 92518569746223895455762833)
      ·
        refine ⟨69388927309667921591822125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92518569746223895455762833 69388927309667921591822125)
        ·
          refine ⟨26020847741125470596933297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69388927309667921591822125 26020847741125470596933297)
          ·
            refine ⟨19515635805844102947699973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26020847741125470596933297 19515635805844102947699973)
            ·
              refine ⟨3659181713595769302693745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19515635805844102947699973 3659181713595769302693745)
              ·
                refine ⟨2744386285196826977020309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3659181713595769302693745 2744386285196826977020309)
                ·
                  refine ⟨128643107118601264547827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2744386285196826977020309 128643107118601264547827)
                  ·
                    rfl

theorem cell23_2254784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 6].length) (baseStart_2254784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254784 prefixEnd_2254784 := by exact prefixLift 2254784
  have htrace : WordTrace (prefixWord ++ tailWord_2254784) baseStart_2254784 baseEnd_2254784 := by
    simpa [prefixWord, tailWord_2254784, baseEnd_2254784] using wordTrace_append hprefix tailTrace_2254784
  have hstable : (prefixWord ++ tailWord_2254784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254784).length < 2 ^ (prefixWord ++ tailWord_2254784).sum := by decide
  have hdescent : baseEnd_2254784 < baseStart_2254784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254807 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_2254807 : Nat := 118140960795 + 2254807 * 2 ^ 59
def prefixEnd_2254807 : Nat := 4983230072969 + 3 ^ 40 * 2254807 * 2
def baseEnd_2254807 : Nat := 1157799774122464790942837

theorem tailTrace_2254807 : CollatzResearch.WordTrace tailWord_2254807 prefixEnd_2254807 1157799774122464790942837 := by
  unfold tailWord_2254807
  simp only [CollatzResearch.WordTrace]
  refine ⟨82239567542226804222098675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54826378361484536148065783 82239567542226804222098675)
  ·
    refine ⟨123359351313340206333148013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82239567542226804222098675 123359351313340206333148013)
    ·
      refine ⟨46259756742502577374930505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123359351313340206333148013 46259756742502577374930505)
      ·
        refine ⟨34694817556876933031197879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46259756742502577374930505 34694817556876933031197879)
        ·
          refine ⟨52042226335315399546796819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34694817556876933031197879 52042226335315399546796819)
          ·
            refine ⟨78063339502973099320195229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52042226335315399546796819 78063339502973099320195229)
            ·
              refine ⟨29273752313614912245073211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78063339502973099320195229 29273752313614912245073211)
              ·
                refine ⟨43910628470422368367609817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29273752313614912245073211 43910628470422368367609817)
                ·
                  refine ⟨32932971352816776275707363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43910628470422368367609817 32932971352816776275707363)
                  ·
                    refine ⟨49399457029225164413561045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32932971352816776275707363 49399457029225164413561045)
                    ·
                      refine ⟨1157799774122464790942837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49399457029225164413561045 1157799774122464790942837)
                      ·
                        rfl

theorem cell23_2254807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_2254807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254807 prefixEnd_2254807 := by exact prefixLift 2254807
  have htrace : WordTrace (prefixWord ++ tailWord_2254807) baseStart_2254807 baseEnd_2254807 := by
    simpa [prefixWord, tailWord_2254807, baseEnd_2254807] using wordTrace_append hprefix tailTrace_2254807
  have hstable : (prefixWord ++ tailWord_2254807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254807).length < 2 ^ (prefixWord ++ tailWord_2254807).sum := by decide
  have hdescent : baseEnd_2254807 < baseStart_2254807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254812 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2254812 : Nat := 118140960795 + 2254812 * 2 ^ 59
def prefixEnd_2254812 : Nat := 4983230072969 + 3 ^ 40 * 2254812 * 2
def baseEnd_2254812 : Nat := 1157802341525737271380315

theorem tailTrace_2254812 : CollatzResearch.WordTrace tailWord_2254812 prefixEnd_2254812 1157802341525737271380315 := by
  unfold tailWord_2254812
  simp only [CollatzResearch.WordTrace]
  refine ⟨41119874953604345038015345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54826499938139126717353793 41119874953604345038015345)
  ·
    refine ⟨30839906215203258778511509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41119874953604345038015345 30839906215203258778511509)
    ·
      refine ⟨1445620603837652755242727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30839906215203258778511509 1445620603837652755242727)
      ·
        refine ⟨2168430905756479132864091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445620603837652755242727 2168430905756479132864091)
        ·
          refine ⟨3252646358634718699296137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168430905756479132864091 3252646358634718699296137)
          ·
            refine ⟨2439484768976039024472103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3252646358634718699296137 2439484768976039024472103)
            ·
              refine ⟨3659227153464058536708155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439484768976039024472103 3659227153464058536708155)
              ·
                refine ⟨5488840730196087805062233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659227153464058536708155 5488840730196087805062233)
                ·
                  refine ⟨4116630547647065853796675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5488840730196087805062233 4116630547647065853796675)
                  ·
                    refine ⟨6174945821470598780695013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4116630547647065853796675 6174945821470598780695013)
                    ·
                      refine ⟨1157802341525737271380315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6174945821470598780695013 1157802341525737271380315)
                      ·
                        rfl

theorem cell23_2254812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2254812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254812 prefixEnd_2254812 := by exact prefixLift 2254812
  have htrace : WordTrace (prefixWord ++ tailWord_2254812) baseStart_2254812 baseEnd_2254812 := by
    simpa [prefixWord, tailWord_2254812, baseEnd_2254812] using wordTrace_append hprefix tailTrace_2254812
  have hstable : (prefixWord ++ tailWord_2254812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254812).length < 2 ^ (prefixWord ++ tailWord_2254812).sum := by decide
  have hdescent : baseEnd_2254812 < baseStart_2254812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254874 : List Nat := [3, 1, 1, 3, 1, 4, 1, 9]
def baseStart_2254874 : Nat := 118140960795 + 2254874 * 2 ^ 59
def prefixEnd_2254874 : Nat := 4983230072969 + 3 ^ 40 * 2254874 * 2
def baseEnd_2254874 : Nat := 42882747308382075140927

theorem tailTrace_2254874 : CollatzResearch.WordTrace tailWord_2254874 prefixEnd_2254874 42882747308382075140927 := by
  unfold tailWord_2254874
  simp only [CollatzResearch.WordTrace]
  refine ⟨20560502808246018666196919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54828007488656049776525117 20560502808246018666196919)
  ·
    refine ⟨30840754212369027999295379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20560502808246018666196919 30840754212369027999295379)
    ·
      refine ⟨46261131318553541998943069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30840754212369027999295379 46261131318553541998943069)
      ·
        refine ⟨17347924244457578249603651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46261131318553541998943069 17347924244457578249603651)
        ·
          refine ⟨26021886366686367374405477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17347924244457578249603651 26021886366686367374405477)
          ·
            refine ⟨4879103693753693882701027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26021886366686367374405477 4879103693753693882701027)
            ·
              refine ⟨7318655540630540824051541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879103693753693882701027 7318655540630540824051541)
              ·
                refine ⟨42882747308382075140927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7318655540630540824051541 42882747308382075140927)
                ·
                  rfl

theorem cell23_2254874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 9].length) (baseStart_2254874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254874 prefixEnd_2254874 := by exact prefixLift 2254874
  have htrace : WordTrace (prefixWord ++ tailWord_2254874) baseStart_2254874 baseEnd_2254874 := by
    simpa [prefixWord, tailWord_2254874, baseEnd_2254874] using wordTrace_append hprefix tailTrace_2254874
  have hstable : (prefixWord ++ tailWord_2254874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254874).length < 2 ^ (prefixWord ++ tailWord_2254874).sum := by decide
  have hdescent : baseEnd_2254874 < baseStart_2254874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254958 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_2254958 : Nat := 118140960795 + 2254958 * 2 ^ 59
def prefixEnd_2254958 : Nat := 4983230072969 + 3 ^ 40 * 2254958 * 2
def baseEnd_2254958 : Nat := 1157877309701293700154643

theorem tailTrace_2254958 : CollatzResearch.WordTrace tailWord_2254958 prefixEnd_2254958 1157877309701293700154643 := by
  unfold tailWord_2254958
  simp only [CollatzResearch.WordTrace]
  refine ⟨10280634370584969626355691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54830049976453171340563685 10280634370584969626355691)
  ·
    refine ⟨15420951555877454439533537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10280634370584969626355691 15420951555877454439533537)
    ·
      refine ⟨11565713666908090829650153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15420951555877454439533537 11565713666908090829650153)
      ·
        refine ⟨8674285250181068122237615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11565713666908090829650153 8674285250181068122237615)
        ·
          refine ⟨13011427875271602183356423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8674285250181068122237615 13011427875271602183356423)
          ·
            refine ⟨19517141812907403275034635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13011427875271602183356423 19517141812907403275034635)
            ·
              refine ⟨29275712719361104912551953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19517141812907403275034635 29275712719361104912551953)
              ·
                refine ⟨21956784539520828684413965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29275712719361104912551953 21956784539520828684413965)
                ·
                  refine ⟨8233794202320310756655237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21956784539520828684413965 8233794202320310756655237)
                  ·
                    refine ⟨1543836412935058266872857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8233794202320310756655237 1543836412935058266872857)
                    ·
                      refine ⟨1157877309701293700154643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543836412935058266872857 1157877309701293700154643)
                      ·
                        rfl

theorem cell23_2254958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_2254958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254958 prefixEnd_2254958 := by exact prefixLift 2254958
  have htrace : WordTrace (prefixWord ++ tailWord_2254958) baseStart_2254958 baseEnd_2254958 := by
    simpa [prefixWord, tailWord_2254958, baseEnd_2254958] using wordTrace_append hprefix tailTrace_2254958
  have hstable : (prefixWord ++ tailWord_2254958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254958).length < 2 ^ (prefixWord ++ tailWord_2254958).sum := by decide
  have hdescent : baseEnd_2254958 < baseStart_2254958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254981 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 7]
def baseStart_2254981 : Nat := 118140960795 + 2254981 * 2 ^ 59
def prefixEnd_2254981 : Nat := 4983230072969 + 3 ^ 40 * 2254981 * 2
def baseEnd_2254981 : Nat := 128654346639594123351893

theorem tailTrace_2254981 : CollatzResearch.WordTrace tailWord_2254981 prefixEnd_2254981 128654346639594123351893 := by
  unfold tailWord_2254981
  simp only [CollatzResearch.WordTrace]
  refine ⟨82245913843596431938932797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54830609229064287959288531 82245913843596431938932797)
  ·
    refine ⟨30842217691348661977099799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82245913843596431938932797 30842217691348661977099799)
    ·
      refine ⟨46263326537022992965649699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30842217691348661977099799 46263326537022992965649699)
      ·
        refine ⟨69394989805534489448474549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46263326537022992965649699 69394989805534489448474549)
        ·
          refine ⟨6505780294268858385794489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69394989805534489448474549 6505780294268858385794489)
          ·
            refine ⟨4879335220701643789345867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6505780294268858385794489 4879335220701643789345867)
            ·
              refine ⟨7319002831052465684018801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879335220701643789345867 7319002831052465684018801)
              ·
                refine ⟨5489252123289349263014101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7319002831052465684018801 5489252123289349263014101)
                ·
                  refine ⟨128654346639594123351893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5489252123289349263014101 128654346639594123351893)
                  ·
                    rfl

theorem cell23_2254981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_2254981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254981 prefixEnd_2254981 := by exact prefixLift 2254981
  have htrace : WordTrace (prefixWord ++ tailWord_2254981) baseStart_2254981 baseEnd_2254981 := by
    simpa [prefixWord, tailWord_2254981, baseEnd_2254981] using wordTrace_append hprefix tailTrace_2254981
  have hstable : (prefixWord ++ tailWord_2254981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254981).length < 2 ^ (prefixWord ++ tailWord_2254981).sum := by decide
  have hdescent : baseEnd_2254981 < baseStart_2254981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2254996 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2254996 : Nat := 118140960795 + 2254996 * 2 ^ 59
def prefixEnd_2254996 : Nat := 4983230072969 + 3 ^ 40 * 2254996 * 2
def baseEnd_2254996 : Nat := 1157896821966164551479469

theorem tailTrace_2254996 : CollatzResearch.WordTrace tailWord_2254996 prefixEnd_2254996 1157896821966164551479469 := by
  unfold tailWord_2254996
  simp only [CollatzResearch.WordTrace]
  refine ⟨41123230469271044750364421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54830973959028059667152561 41123230469271044750364421)
  ·
    refine ⟨7710605712988320890693329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41123230469271044750364421 7710605712988320890693329)
    ·
      refine ⟨5782954284741240668019997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7710605712988320890693329 5782954284741240668019997)
      ·
        refine ⟨2168607856777965250507499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5782954284741240668019997 2168607856777965250507499)
        ·
          refine ⟨3252911785166947875761249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168607856777965250507499 3252911785166947875761249)
          ·
            refine ⟨2439683838875210906820937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3252911785166947875761249 2439683838875210906820937)
            ·
              refine ⟨1829762879156408180115703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439683838875210906820937 1829762879156408180115703)
              ·
                refine ⟨2744644318734612270173555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829762879156408180115703 2744644318734612270173555)
                ·
                  refine ⟨4116966478101918405260333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744644318734612270173555 4116966478101918405260333)
                  ·
                    refine ⟨1543862429288219401972625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4116966478101918405260333 1543862429288219401972625)
                    ·
                      refine ⟨1157896821966164551479469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543862429288219401972625 1157896821966164551479469)
                      ·
                        rfl

theorem cell23_2254996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2254996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2254996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2254996 prefixEnd_2254996 := by exact prefixLift 2254996
  have htrace : WordTrace (prefixWord ++ tailWord_2254996) baseStart_2254996 baseEnd_2254996 := by
    simpa [prefixWord, tailWord_2254996, baseEnd_2254996] using wordTrace_append hprefix tailTrace_2254996
  have hstable : (prefixWord ++ tailWord_2254996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2254996).length < 2 ^ (prefixWord ++ tailWord_2254996).sum := by decide
  have hdescent : baseEnd_2254996 < baseStart_2254996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2254996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255024 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 4, 8]
def baseStart_2255024 : Nat := 118140960795 + 2255024 * 2 ^ 59
def prefixEnd_2255024 : Nat := 4983230072969 + 3 ^ 40 * 2255024 * 2
def baseEnd_2255024 : Nat := 385970399808163480643113

theorem tailTrace_2255024 : CollatzResearch.WordTrace tailWord_2255024 prefixEnd_2255024 385970399808163480643113 := by
  unfold tailWord_2255024
  simp only [CollatzResearch.WordTrace]
  refine ⟨41123741091220325141374063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54831654788293766855165417 41123741091220325141374063)
  ·
    refine ⟨61685611636830487712061095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41123741091220325141374063 61685611636830487712061095)
    ·
      refine ⟨92528417455245731568091643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61685611636830487712061095 92528417455245731568091643)
      ·
        refine ⟨138792626182868597352137465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92528417455245731568091643 138792626182868597352137465)
        ·
          refine ⟨104094469637151448014103099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138792626182868597352137465 104094469637151448014103099)
          ·
            refine ⟨156141704455727172021154649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104094469637151448014103099 156141704455727172021154649)
            ·
              refine ⟨117106278341795379015865987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156141704455727172021154649 117106278341795379015865987)
              ·
                refine ⟨175659417512693068523798981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117106278341795379015865987 175659417512693068523798981)
                ·
                  refine ⟨32936140783629950348212309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175659417512693068523798981 32936140783629950348212309)
                  ·
                    refine ⟨385970399808163480643113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32936140783629950348212309 385970399808163480643113)
                    ·
                      rfl

theorem cell23_2255024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_2255024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255024 prefixEnd_2255024 := by exact prefixLift 2255024
  have htrace : WordTrace (prefixWord ++ tailWord_2255024) baseStart_2255024 baseEnd_2255024 := by
    simpa [prefixWord, tailWord_2255024, baseEnd_2255024] using wordTrace_append hprefix tailTrace_2255024
  have hstable : (prefixWord ++ tailWord_2255024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255024).length < 2 ^ (prefixWord ++ tailWord_2255024).sum := by decide
  have hdescent : baseEnd_2255024 < baseStart_2255024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255031 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_2255031 : Nat := 118140960795 + 2255031 * 2 ^ 59
def prefixEnd_2255031 : Nat := 4983230072969 + 3 ^ 40 * 2255031 * 2
def baseEnd_2255031 : Nat := 1157914793789071914541807

theorem tailTrace_2255031 : CollatzResearch.WordTrace tailWord_2255031 prefixEnd_2255031 1157914793789071914541807 := by
  unfold tailWord_2255031
  simp only [CollatzResearch.WordTrace]
  refine ⟨82247737493415290478252947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54831824995610193652168631 82247737493415290478252947)
  ·
    refine ⟨123371606240122935717379421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82247737493415290478252947 123371606240122935717379421)
    ·
      refine ⟨46264352340046100894017283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123371606240122935717379421 46264352340046100894017283)
      ·
        refine ⟨69396528510069151341025925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46264352340046100894017283 69396528510069151341025925)
        ·
          refine ⟨13011849095637965876442361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69396528510069151341025925 13011849095637965876442361)
          ·
            refine ⟨9758886821728474407331771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13011849095637965876442361 9758886821728474407331771)
            ·
              refine ⟨14638330232592711610997657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9758886821728474407331771 14638330232592711610997657)
              ·
                refine ⟨10978747674444533708248243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14638330232592711610997657 10978747674444533708248243)
                ·
                  refine ⟨16468121511666800562372365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10978747674444533708248243 16468121511666800562372365)
                  ·
                    refine ⟨6175545566875050210889637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16468121511666800562372365 6175545566875050210889637)
                    ·
                      refine ⟨1157914793789071914541807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6175545566875050210889637 1157914793789071914541807)
                      ·
                        rfl

theorem cell23_2255031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_2255031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255031 prefixEnd_2255031 := by exact prefixLift 2255031
  have htrace : WordTrace (prefixWord ++ tailWord_2255031) baseStart_2255031 baseEnd_2255031 := by
    simpa [prefixWord, tailWord_2255031, baseEnd_2255031] using wordTrace_append hprefix tailTrace_2255031
  have hstable : (prefixWord ++ tailWord_2255031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255031).length < 2 ^ (prefixWord ++ tailWord_2255031).sum := by decide
  have hdescent : baseEnd_2255031 < baseStart_2255031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255051 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 3]
def baseStart_2255051 : Nat := 118140960795 + 2255051 * 2 ^ 59
def prefixEnd_2255051 : Nat := 4983230072969 + 3 ^ 40 * 2255051 * 2
def baseEnd_2255051 : Nat := 1157925063402161836291715

theorem tailTrace_2255051 : CollatzResearch.WordTrace tailWord_2255051 prefixEnd_2255051 1157925063402161836291715 := by
  unfold tailWord_2255051
  simp only [CollatzResearch.WordTrace]
  refine ⟨82248466953342833893981007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54832311302228555929320671 82248466953342833893981007)
  ·
    refine ⟨123372700430014250840971511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82248466953342833893981007 123372700430014250840971511)
    ·
      refine ⟨185059050645021376261457267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123372700430014250840971511 185059050645021376261457267)
      ·
        refine ⟨277588575967532064392185901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185059050645021376261457267 277588575967532064392185901)
        ·
          refine ⟨104095715987824524147069713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277588575967532064392185901 104095715987824524147069713)
          ·
            refine ⟨78071786990868393110302285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104095715987824524147069713 78071786990868393110302285)
            ·
              refine ⟨29276920121575647416363357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78071786990868393110302285 29276920121575647416363357)
              ·
                refine ⟨10978845045590867781136259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29276920121575647416363357 10978845045590867781136259)
                ·
                  refine ⟨16468267568386301671704389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10978845045590867781136259 16468267568386301671704389)
                  ·
                    refine ⟨3087800169072431563444573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16468267568386301671704389 3087800169072431563444573)
                    ·
                      refine ⟨1157925063402161836291715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3087800169072431563444573 1157925063402161836291715)
                      ·
                        rfl

theorem cell23_2255051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 3].length) (baseStart_2255051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255051 prefixEnd_2255051 := by exact prefixLift 2255051
  have htrace : WordTrace (prefixWord ++ tailWord_2255051) baseStart_2255051 baseEnd_2255051 := by
    simpa [prefixWord, tailWord_2255051, baseEnd_2255051] using wordTrace_append hprefix tailTrace_2255051
  have hstable : (prefixWord ++ tailWord_2255051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255051).length < 2 ^ (prefixWord ++ tailWord_2255051).sum := by decide
  have hdescent : baseEnd_2255051 < baseStart_2255051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255071 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 6]
def baseStart_2255071 : Nat := 118140960795 + 2255071 * 2 ^ 59
def prefixEnd_2255071 : Nat := 4983230072969 + 3 ^ 40 * 2255071 * 2
def baseEnd_2255071 : Nat := 128659481446139084226847

theorem tailTrace_2255071 : CollatzResearch.WordTrace tailWord_2255071 prefixEnd_2255071 128659481446139084226847 := by
  unfold tailWord_2255071
  simp only [CollatzResearch.WordTrace]
  refine ⟨82249196413270377309709067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54832797608846918206472711 82249196413270377309709067)
  ·
    refine ⟨123373794619905565964563601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82249196413270377309709067 123373794619905565964563601)
    ·
      refine ⟨92530345964929174473422701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123373794619905565964563601 92530345964929174473422701)
      ·
        refine ⟨34698879736848440427533513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92530345964929174473422701 34698879736848440427533513)
        ·
          refine ⟨26024159802636330320650135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34698879736848440427533513 26024159802636330320650135)
          ·
            refine ⟨39036239703954495480975203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26024159802636330320650135 39036239703954495480975203)
            ·
              refine ⟨58554359555931743221462805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39036239703954495480975203 58554359555931743221462805)
              ·
                refine ⟨2744735604184300463506069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58554359555931743221462805 2744735604184300463506069)
                ·
                  refine ⟨128659481446139084226847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2744735604184300463506069 128659481446139084226847)
                  ·
                    rfl

theorem cell23_2255071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 6].length) (baseStart_2255071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255071 prefixEnd_2255071 := by exact prefixLift 2255071
  have htrace : WordTrace (prefixWord ++ tailWord_2255071) baseStart_2255071 baseEnd_2255071 := by
    simpa [prefixWord, tailWord_2255071, baseEnd_2255071] using wordTrace_append hprefix tailTrace_2255071
  have hstable : (prefixWord ++ tailWord_2255071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255071).length < 2 ^ (prefixWord ++ tailWord_2255071).sum := by decide
  have hdescent : baseEnd_2255071 < baseStart_2255071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255125 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_2255125 : Nat := 118140960795 + 2255125 * 2 ^ 59
def prefixEnd_2255125 : Nat := 4983230072969 + 3 ^ 40 * 2255125 * 2
def baseEnd_2255125 : Nat := 1157963060970594546766375

theorem tailTrace_2255125 : CollatzResearch.WordTrace tailWord_2255125 prefixEnd_2255125 1157963060970594546766375 := by
  unfold tailWord_2255125
  simp only [CollatzResearch.WordTrace]
  refine ⟨82251165955074744532174829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54834110636716496354783219 82251165955074744532174829)
  ·
    refine ⟨30844187233153029199565561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82251165955074744532174829 30844187233153029199565561)
    ·
      refine ⟨23133140424864771899674171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30844187233153029199565561 23133140424864771899674171)
      ·
        refine ⟨34699710637297157849511257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23133140424864771899674171 34699710637297157849511257)
        ·
          refine ⟨26024782977972868387133443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34699710637297157849511257 26024782977972868387133443)
          ·
            refine ⟨39037174466959302580700165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26024782977972868387133443 39037174466959302580700165)
            ·
              refine ⟨7319470212554869233881281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39037174466959302580700165 7319470212554869233881281)
              ·
                refine ⟨5489602659416151925410961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7319470212554869233881281 5489602659416151925410961)
                ·
                  refine ⟨4117201994562113944058221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5489602659416151925410961 4117201994562113944058221)
                  ·
                    refine ⟨1543950747960792729021833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4117201994562113944058221 1543950747960792729021833)
                    ·
                      refine ⟨1157963060970594546766375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543950747960792729021833 1157963060970594546766375)
                      ·
                        rfl

theorem cell23_2255125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_2255125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255125 prefixEnd_2255125 := by exact prefixLift 2255125
  have htrace : WordTrace (prefixWord ++ tailWord_2255125) baseStart_2255125 baseEnd_2255125 := by
    simpa [prefixWord, tailWord_2255125, baseEnd_2255125] using wordTrace_append hprefix tailTrace_2255125
  have hstable : (prefixWord ++ tailWord_2255125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255125).length < 2 ^ (prefixWord ++ tailWord_2255125).sum := by decide
  have hdescent : baseEnd_2255125 < baseStart_2255125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255149 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2255149 : Nat := 118140960795 + 2255149 * 2 ^ 59
def prefixEnd_2255149 : Nat := 4983230072969 + 3 ^ 40 * 2255149 * 2
def baseEnd_2255149 : Nat := 1157975384506302452866265

theorem tailTrace_2255149 : CollatzResearch.WordTrace tailWord_2255149 prefixEnd_2255149 1157975384506302452866265 := by
  unfold tailWord_2255149
  simp only [CollatzResearch.WordTrace]
  refine ⟨82252041306987796631048501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54834694204658531087365667 82252041306987796631048501)
  ·
    refine ⟨7711128872530105934160797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82252041306987796631048501 7711128872530105934160797)
    ·
      refine ⟨2891673327198789725310299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7711128872530105934160797 2891673327198789725310299)
      ·
        refine ⟨4337509990798184587965449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2891673327198789725310299 4337509990798184587965449)
        ·
          refine ⟨3253132493098638440974087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4337509990798184587965449 3253132493098638440974087)
          ·
            refine ⟨4879698739647957661461131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253132493098638440974087 4879698739647957661461131)
            ·
              refine ⟨7319548109471936492191697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879698739647957661461131 7319548109471936492191697)
              ·
                refine ⟨5489661082103952369143773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7319548109471936492191697 5489661082103952369143773)
                ·
                  refine ⟨2058622905788982138428915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5489661082103952369143773 2058622905788982138428915)
                  ·
                    refine ⟨3087934358683473207643373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2058622905788982138428915 3087934358683473207643373)
                    ·
                      refine ⟨1157975384506302452866265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3087934358683473207643373 1157975384506302452866265)
                      ·
                        rfl

theorem cell23_2255149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2255149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255149 prefixEnd_2255149 := by exact prefixLift 2255149
  have htrace : WordTrace (prefixWord ++ tailWord_2255149) baseStart_2255149 baseEnd_2255149 := by
    simpa [prefixWord, tailWord_2255149, baseEnd_2255149] using wordTrace_append hprefix tailTrace_2255149
  have hstable : (prefixWord ++ tailWord_2255149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255149).length < 2 ^ (prefixWord ++ tailWord_2255149).sum := by decide
  have hdescent : baseEnd_2255149 < baseStart_2255149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255151 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_2255151 : Nat := 118140960795 + 2255151 * 2 ^ 59
def prefixEnd_2255151 : Nat := 4983230072969 + 3 ^ 40 * 2255151 * 2
def baseEnd_2255151 : Nat := 1157976411467611445041255

theorem tailTrace_2255151 : CollatzResearch.WordTrace tailWord_2255151 prefixEnd_2255151 1157976411467611445041255 := by
  unfold tailWord_2255151
  simp only [CollatzResearch.WordTrace]
  refine ⟨82252114252980550972621307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54834742835320367315080871 82252114252980550972621307)
  ·
    refine ⟨123378171379470826458931961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82252114252980550972621307 123378171379470826458931961)
    ·
      refine ⟨92533628534603119844198971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123378171379470826458931961 92533628534603119844198971)
      ·
        refine ⟨138800442801904679766298457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92533628534603119844198971 138800442801904679766298457)
        ·
          refine ⟨104100332101428509824723843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138800442801904679766298457 104100332101428509824723843)
          ·
            refine ⟨156150498152142764737085765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104100332101428509824723843 156150498152142764737085765)
            ·
              refine ⟨29278218403526768388203581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156150498152142764737085765 29278218403526768388203581)
              ·
                refine ⟨10979331901322538145576343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29278218403526768388203581 10979331901322538145576343)
                ·
                  refine ⟨16468997851983807218364515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10979331901322538145576343 16468997851983807218364515)
                  ·
                    refine ⟨24703496777975710827546773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16468997851983807218364515 24703496777975710827546773)
                    ·
                      refine ⟨1157976411467611445041255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24703496777975710827546773 1157976411467611445041255)
                      ·
                        rfl

theorem cell23_2255151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_2255151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255151 prefixEnd_2255151 := by exact prefixLift 2255151
  have htrace : WordTrace (prefixWord ++ tailWord_2255151) baseStart_2255151 baseEnd_2255151 := by
    simpa [prefixWord, tailWord_2255151, baseEnd_2255151] using wordTrace_append hprefix tailTrace_2255151
  have hstable : (prefixWord ++ tailWord_2255151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255151).length < 2 ^ (prefixWord ++ tailWord_2255151).sum := by decide
  have hdescent : baseEnd_2255151 < baseStart_2255151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255169 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2255169 : Nat := 118140960795 + 2255169 * 2 ^ 59
def prefixEnd_2255169 : Nat := 4983230072969 + 3 ^ 40 * 2255169 * 2
def baseEnd_2255169 : Nat := 385995218039797458205391

theorem tailTrace_2255169 : CollatzResearch.WordTrace tailWord_2255169 prefixEnd_2255169 385995218039797458205391 := by
  unfold tailWord_2255169
  simp only [CollatzResearch.WordTrace]
  refine ⟨82252770766915340046776561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54835180511276893364517707 82252770766915340046776561)
  ·
    refine ⟨61689578075186505035082421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82252770766915340046776561 61689578075186505035082421)
    ·
      refine ⟨5783397944548734847038977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61689578075186505035082421 5783397944548734847038977)
      ·
        refine ⟨4337548458411551135279233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5783397944548734847038977 4337548458411551135279233)
        ·
          refine ⟨3253161343808663351459425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4337548458411551135279233 3253161343808663351459425)
          ·
            refine ⟨2439871007856497513594569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3253161343808663351459425 2439871007856497513594569)
            ·
              refine ⟨1829903255892373135195927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439871007856497513594569 1829903255892373135195927)
              ·
                refine ⟨2744854883838559702793891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829903255892373135195927 2744854883838559702793891)
                ·
                  refine ⟨4117282325757839554190837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744854883838559702793891 4117282325757839554190837)
                  ·
                    refine ⟨385995218039797458205391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4117282325757839554190837 385995218039797458205391)
                    ·
                      rfl

theorem cell23_2255169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2255169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255169 prefixEnd_2255169 := by exact prefixLift 2255169
  have htrace : WordTrace (prefixWord ++ tailWord_2255169) baseStart_2255169 baseEnd_2255169 := by
    simpa [prefixWord, tailWord_2255169, baseEnd_2255169] using wordTrace_append hprefix tailTrace_2255169
  have hstable : (prefixWord ++ tailWord_2255169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255169).length < 2 ^ (prefixWord ++ tailWord_2255169).sum := by decide
  have hdescent : baseEnd_2255169 < baseStart_2255169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255175 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_2255175 : Nat := 118140960795 + 2255175 * 2 ^ 59
def prefixEnd_2255175 : Nat := 4983230072969 + 3 ^ 40 * 2255175 * 2
def baseEnd_2255175 : Nat := 1157988735003319351141145

theorem tailTrace_2255175 : CollatzResearch.WordTrace tailWord_2255175 prefixEnd_2255175 1157988735003319351141145 := by
  unfold tailWord_2255175
  simp only [CollatzResearch.WordTrace]
  refine ⟨82252989604893603071494979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54835326403262402047663319 82252989604893603071494979)
  ·
    refine ⟨123379484407340404607242469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82252989604893603071494979 123379484407340404607242469)
    ·
      refine ⟨23133653326376325863857963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123379484407340404607242469 23133653326376325863857963)
      ·
        refine ⟨34700479989564488795786945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23133653326376325863857963 34700479989564488795786945)
        ·
          refine ⟨26025359992173366596840209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34700479989564488795786945 26025359992173366596840209)
          ·
            refine ⟨19519019994130024947630157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26025359992173366596840209 19519019994130024947630157)
            ·
              refine ⟨7319632497798759355361309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19519019994130024947630157 7319632497798759355361309)
              ·
                refine ⟨2744862186674534758260491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7319632497798759355361309 2744862186674534758260491)
                ·
                  refine ⟨4117293280011802137390737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744862186674534758260491 4117293280011802137390737)
                  ·
                    refine ⟨3087969960008851603043053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4117293280011802137390737 3087969960008851603043053)
                    ·
                      refine ⟨1157988735003319351141145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3087969960008851603043053 1157988735003319351141145)
                      ·
                        rfl

theorem cell23_2255175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_2255175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255175 prefixEnd_2255175 := by exact prefixLift 2255175
  have htrace : WordTrace (prefixWord ++ tailWord_2255175) baseStart_2255175 baseEnd_2255175 := by
    simpa [prefixWord, tailWord_2255175, baseEnd_2255175] using wordTrace_append hprefix tailTrace_2255175
  have hstable : (prefixWord ++ tailWord_2255175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255175).length < 2 ^ (prefixWord ++ tailWord_2255175).sum := by decide
  have hdescent : baseEnd_2255175 < baseStart_2255175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255189 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_2255189 : Nat := 118140960795 + 2255189 * 2 ^ 59
def prefixEnd_2255189 : Nat := 4983230072969 + 3 ^ 40 * 2255189 * 2
def baseEnd_2255189 : Nat := 1157995923732482296366081

theorem tailTrace_2255189 : CollatzResearch.WordTrace tailWord_2255189 prefixEnd_2255189 1157995923732482296366081 := by
  unfold tailWord_2255189
  simp only [CollatzResearch.WordTrace]
  refine ⟨82253500226842883462504621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54835666817895255641669747 82253500226842883462504621)
  ·
    refine ⟨30845062585066081298439233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82253500226842883462504621 30845062585066081298439233)
    ·
      refine ⟨23133796938799560973829425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30845062585066081298439233 23133796938799560973829425)
      ·
        refine ⟨17350347704099670730372069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23133796938799560973829425 17350347704099670730372069)
        ·
          refine ⟨3253190194518688261944763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17350347704099670730372069 3253190194518688261944763)
          ·
            refine ⟨4879785291778032392917145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253190194518688261944763 4879785291778032392917145)
            ·
              refine ⟨3659838968833524294687859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4879785291778032392917145 3659838968833524294687859)
              ·
                refine ⟨5489758453250286442031789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659838968833524294687859 5489758453250286442031789)
                ·
                  refine ⟨2058659419968857415761921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5489758453250286442031789 2058659419968857415761921)
                  ·
                    refine ⟨1543994564976643061821441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2058659419968857415761921 1543994564976643061821441)
                    ·
                      refine ⟨1157995923732482296366081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1543994564976643061821441 1157995923732482296366081)
                      ·
                        rfl

theorem cell23_2255189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_2255189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255189 prefixEnd_2255189 := by exact prefixLift 2255189
  have htrace : WordTrace (prefixWord ++ tailWord_2255189) baseStart_2255189 baseEnd_2255189 := by
    simpa [prefixWord, tailWord_2255189, baseEnd_2255189] using wordTrace_append hprefix tailTrace_2255189
  have hstable : (prefixWord ++ tailWord_2255189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255189).length < 2 ^ (prefixWord ++ tailWord_2255189).sum := by decide
  have hdescent : baseEnd_2255189 < baseStart_2255189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255202 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2255202 : Nat := 118140960795 + 2255202 * 2 ^ 59
def prefixEnd_2255202 : Nat := 4983230072969 + 3 ^ 40 * 2255202 * 2
def baseEnd_2255202 : Nat := 1158002598980990745503521

theorem tailTrace_2255202 : CollatzResearch.WordTrace tailWord_2255202 prefixEnd_2255202 1158002598980990745503521 := by
  unfold tailWord_2255202
  simp only [CollatzResearch.WordTrace]
  refine ⟨20563493593948946670681965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54835982917197191121818573 20563493593948946670681965)
  ·
    refine ⟨7711310097730855001505737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20563493593948946670681965 7711310097730855001505737)
    ·
      refine ⟨5783482573298141251129303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7711310097730855001505737 5783482573298141251129303)
      ·
        refine ⟨8675223859947211876693955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783482573298141251129303 8675223859947211876693955)
        ·
          refine ⟨13012835789920817815040933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8675223859947211876693955 13012835789920817815040933)
          ·
            refine ⟨2439906710610153340320175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13012835789920817815040933 2439906710610153340320175)
            ·
              refine ⟨3659860065915230010480263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439906710610153340320175 3659860065915230010480263)
              ·
                refine ⟨5489790098872845015720395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659860065915230010480263 5489790098872845015720395)
                ·
                  refine ⟨8234685148309267523580593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5489790098872845015720395 8234685148309267523580593)
                  ·
                    refine ⟨6176013861231950642685445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8234685148309267523580593 6176013861231950642685445)
                    ·
                      refine ⟨1158002598980990745503521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6176013861231950642685445 1158002598980990745503521)
                      ·
                        rfl

theorem cell23_2255202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2255202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255202 prefixEnd_2255202 := by exact prefixLift 2255202
  have htrace : WordTrace (prefixWord ++ tailWord_2255202) baseStart_2255202 baseEnd_2255202 := by
    simpa [prefixWord, tailWord_2255202, baseEnd_2255202] using wordTrace_append hprefix tailTrace_2255202
  have hstable : (prefixWord ++ tailWord_2255202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255202).length < 2 ^ (prefixWord ++ tailWord_2255202).sum := by decide
  have hdescent : baseEnd_2255202 < baseStart_2255202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255205 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_2255205 : Nat := 118140960795 + 2255205 * 2 ^ 59
def prefixEnd_2255205 : Nat := 4983230072969 + 3 ^ 40 * 2255205 * 2
def baseEnd_2255205 : Nat := 1158004139422954233766007

theorem tailTrace_2255205 : CollatzResearch.WordTrace tailWord_2255205 prefixEnd_2255205 1158004139422954233766007 := by
  unfold tailWord_2255205
  simp only [CollatzResearch.WordTrace]
  refine ⟨82254083794784918195087069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54836055863189945463391379 82254083794784918195087069)
  ·
    refine ⟨30845281423044344323157651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82254083794784918195087069 30845281423044344323157651)
    ·
      refine ⟨46267922134566516484736477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30845281423044344323157651 46267922134566516484736477)
      ·
        refine ⟨17350470800462443681776179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46267922134566516484736477 17350470800462443681776179)
        ·
          refine ⟨26025706200693665522664269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17350470800462443681776179 26025706200693665522664269)
          ·
            refine ⟨9759639825260124570999101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26025706200693665522664269 9759639825260124570999101)
            ·
              refine ⟨3659864934472546714124663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9759639825260124570999101 3659864934472546714124663)
              ·
                refine ⟨5489797401708820071186995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659864934472546714124663 5489797401708820071186995)
                ·
                  refine ⟨8234696102563230106780493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5489797401708820071186995 8234696102563230106780493)
                  ·
                    refine ⟨3088011038461211290042685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8234696102563230106780493 3088011038461211290042685)
                    ·
                      refine ⟨1158004139422954233766007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3088011038461211290042685 1158004139422954233766007)
                      ·
                        rfl

theorem cell23_2255205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_2255205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255205 prefixEnd_2255205 := by exact prefixLift 2255205
  have htrace : WordTrace (prefixWord ++ tailWord_2255205) baseStart_2255205 baseEnd_2255205 := by
    simpa [prefixWord, tailWord_2255205, baseEnd_2255205] using wordTrace_append hprefix tailTrace_2255205
  have hstable : (prefixWord ++ tailWord_2255205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255205).length < 2 ^ (prefixWord ++ tailWord_2255205).sum := by decide
  have hdescent : baseEnd_2255205 < baseStart_2255205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255212 : List Nat := [2, 2, 1, 1, 7, 1, 2, 7]
def baseStart_2255212 : Nat := 118140960795 + 2255212 * 2 ^ 59
def prefixEnd_2255212 : Nat := 4983230072969 + 3 ^ 40 * 2255212 * 2
def baseEnd_2255212 : Nat := 42889175325464285421425

theorem tailTrace_2255212 : CollatzResearch.WordTrace tailWord_2255212 prefixEnd_2255212 42889175325464285421425 := by
  unfold tailWord_2255212
  simp only [CollatzResearch.WordTrace]
  refine ⟨41127169552879779195295945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54836226070506372260394593 41127169552879779195295945)
  ·
    refine ⟨30845377164659834396471959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41127169552879779195295945 30845377164659834396471959)
    ·
      refine ⟨46268065746989751594707939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30845377164659834396471959 46268065746989751594707939)
      ·
        refine ⟨69402098620484627392061909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46268065746989751594707939 69402098620484627392061909)
        ·
          refine ⟨1626611686417608454501451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 69402098620484627392061909 1626611686417608454501451)
          ·
            refine ⟨2439917529626412681752177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626611686417608454501451 2439917529626412681752177)
            ·
              refine ⟨1829938147219809511314133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439917529626412681752177 1829938147219809511314133)
              ·
                refine ⟨42889175325464285421425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1829938147219809511314133 42889175325464285421425)
                ·
                  rfl

theorem cell23_2255212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 7].length) (baseStart_2255212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255212 prefixEnd_2255212 := by exact prefixLift 2255212
  have htrace : WordTrace (prefixWord ++ tailWord_2255212) baseStart_2255212 baseEnd_2255212 := by
    simpa [prefixWord, tailWord_2255212, baseEnd_2255212] using wordTrace_append hprefix tailTrace_2255212
  have hstable : (prefixWord ++ tailWord_2255212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255212).length < 2 ^ (prefixWord ++ tailWord_2255212).sum := by decide
  have hdescent : baseEnd_2255212 < baseStart_2255212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255218 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2255218 : Nat := 118140960795 + 2255218 * 2 ^ 59
def prefixEnd_2255218 : Nat := 4983230072969 + 3 ^ 40 * 2255218 * 2
def baseEnd_2255218 : Nat := 1158010814671462682903447

theorem tailTrace_2255218 : CollatzResearch.WordTrace tailWord_2255218 prefixEnd_2255218 1158010814671462682903447 := by
  unfold tailWord_2255218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20563639485934455353827577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54836371962491880943540205 20563639485934455353827577)
  ·
    refine ⟨15422729614450841515370683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20563639485934455353827577 15422729614450841515370683)
    ·
      refine ⟨23134094421676262273056025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15422729614450841515370683 23134094421676262273056025)
      ·
        refine ⟨17350570816257196704792019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23134094421676262273056025 17350570816257196704792019)
        ·
          refine ⟨26025856224385795057188029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17350570816257196704792019 26025856224385795057188029)
          ·
            refine ⟨9759696084144673146445511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26025856224385795057188029 9759696084144673146445511)
            ·
              refine ⟨14639544126217009719668267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9759696084144673146445511 14639544126217009719668267)
              ·
                refine ⟨21959316189325514579502401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14639544126217009719668267 21959316189325514579502401)
                ·
                  refine ⟨16469487141994135934626801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21959316189325514579502401 16469487141994135934626801)
                  ·
                    refine ⟨12352115356495601950970101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16469487141994135934626801 12352115356495601950970101)
                    ·
                      refine ⟨1158010814671462682903447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12352115356495601950970101 1158010814671462682903447)
                      ·
                        rfl

theorem cell23_2255218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2255218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255218 prefixEnd_2255218 := by exact prefixLift 2255218
  have htrace : WordTrace (prefixWord ++ tailWord_2255218) baseStart_2255218 baseEnd_2255218 := by
    simpa [prefixWord, tailWord_2255218, baseEnd_2255218] using wordTrace_append hprefix tailTrace_2255218
  have hstable : (prefixWord ++ tailWord_2255218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255218).length < 2 ^ (prefixWord ++ tailWord_2255218).sum := by decide
  have hdescent : baseEnd_2255218 < baseStart_2255218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255256 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2255256 : Nat := 118140960795 + 2255256 * 2 ^ 59
def prefixEnd_2255256 : Nat := 4983230072969 + 3 ^ 40 * 2255256 * 2
def baseEnd_2255256 : Nat := 1158030326936333534228273

theorem tailTrace_2255256 : CollatzResearch.WordTrace tailWord_2255256 prefixEnd_2255256 1158030326936333534228273 := by
  unfold tailWord_2255256
  simp only [CollatzResearch.WordTrace]
  refine ⟨41127971958800076952596811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54837295945066769270129081 41127971958800076952596811)
  ·
    refine ⟨61691957938200115428895217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41127971958800076952596811 61691957938200115428895217)
    ·
      refine ⟨46268968453650086571671413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61691957938200115428895217 46268968453650086571671413)
      ·
        refine ⟨4337715792529695616094195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46268968453650086571671413 4337715792529695616094195)
        ·
          refine ⟨6506573688794543424141293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4337715792529695616094195 6506573688794543424141293)
          ·
            refine ⟨2439965133297953784052985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6506573688794543424141293 2439965133297953784052985)
            ·
              refine ⟨1829973849973465338039739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439965133297953784052985 1829973849973465338039739)
              ·
                refine ⟨2744960774960198007059609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829973849973465338039739 2744960774960198007059609)
                ·
                  refine ⟨2058720581220148505294707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2744960774960198007059609 2058720581220148505294707)
                  ·
                    refine ⟨3088080871830222757942061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2058720581220148505294707 3088080871830222757942061)
                    ·
                      refine ⟨1158030326936333534228273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3088080871830222757942061 1158030326936333534228273)
                      ·
                        rfl

theorem cell23_2255256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2255256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255256 prefixEnd_2255256 := by exact prefixLift 2255256
  have htrace : WordTrace (prefixWord ++ tailWord_2255256) baseStart_2255256 baseEnd_2255256 := by
    simpa [prefixWord, tailWord_2255256, baseEnd_2255256] using wordTrace_append hprefix tailTrace_2255256
  have hstable : (prefixWord ++ tailWord_2255256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255256).length < 2 ^ (prefixWord ++ tailWord_2255256).sum := by decide
  have hdescent : baseEnd_2255256 < baseStart_2255256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255268 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 7]
def baseStart_2255268 : Nat := 118140960795 + 2255268 * 2 ^ 59
def prefixEnd_2255268 : Nat := 4983230072969 + 3 ^ 40 * 2255268 * 2
def baseEnd_2255268 : Nat := 128670720967131943030913

theorem tailTrace_2255268 : CollatzResearch.WordTrace tailWord_2255268 prefixEnd_2255268 128670720967131943030913 := by
  unfold tailWord_2255268
  simp only [CollatzResearch.WordTrace]
  refine ⟨41128190796778339977315229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54837587729037786636420305 41128190796778339977315229)
  ·
    refine ⟨15423071548791877491493211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41128190796778339977315229 15423071548791877491493211)
    ·
      refine ⟨23134607323187816237239817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15423071548791877491493211 23134607323187816237239817)
      ·
        refine ⟨17350955492390862177929863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23134607323187816237239817 17350955492390862177929863)
        ·
          refine ⟨26026433238586293266894795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17350955492390862177929863 26026433238586293266894795)
          ·
            refine ⟨39039649857879439900342193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26026433238586293266894795 39039649857879439900342193)
            ·
              refine ⟨29279737393409579925256645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39039649857879439900342193 29279737393409579925256645)
              ·
                refine ⟨5489950761264296235985621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29279737393409579925256645 5489950761264296235985621)
                ·
                  refine ⟨128670720967131943030913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5489950761264296235985621 128670720967131943030913)
                  ·
                    rfl

theorem cell23_2255268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_2255268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255268 prefixEnd_2255268 := by exact prefixLift 2255268
  have htrace : WordTrace (prefixWord ++ tailWord_2255268) baseStart_2255268 baseEnd_2255268 := by
    simpa [prefixWord, tailWord_2255268, baseEnd_2255268] using wordTrace_append hprefix tailTrace_2255268
  have hstable : (prefixWord ++ tailWord_2255268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255268).length < 2 ^ (prefixWord ++ tailWord_2255268).sum := by decide
  have hdescent : baseEnd_2255268 < baseStart_2255268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255305 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 2, 5, 2]
def baseStart_2255305 : Nat := 118140960795 + 2255305 * 2 ^ 59
def prefixEnd_2255305 : Nat := 4983230072969 + 3 ^ 40 * 2255305 * 2
def baseEnd_2255305 : Nat := 1158055487488403842515547

theorem tailTrace_2255305 : CollatzResearch.WordTrace tailWord_2255305 prefixEnd_2255305 1158055487488403842515547 := by
  unfold tailWord_2255305
  simp only [CollatzResearch.WordTrace]
  refine ⟨82257731094422635273727369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54838487396281756849151579 82257731094422635273727369)
  ·
    refine ⟨61693298320816976455295527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82257731094422635273727369 61693298320816976455295527)
    ·
      refine ⟨92539947481225464682943291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61693298320816976455295527 92539947481225464682943291)
      ·
        refine ⟨138809921221838197024414937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92539947481225464682943291 138809921221838197024414937)
        ·
          refine ⟨104107440916378647768311203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138809921221838197024414937 104107440916378647768311203)
          ·
            refine ⟨156161161374567971652466805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104107440916378647768311203 156161161374567971652466805)
            ·
              refine ⟨14640108878865747342418763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156161161374567971652466805 14640108878865747342418763)
              ·
                refine ⟨21960163318298621013628145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14640108878865747342418763 21960163318298621013628145)
                ·
                  refine ⟨16470122488723965760221109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21960163318298621013628145 16470122488723965760221109)
                  ·
                    refine ⟨1544073983317871790020729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16470122488723965760221109 1544073983317871790020729)
                    ·
                      refine ⟨1158055487488403842515547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544073983317871790020729 1158055487488403842515547)
                      ·
                        rfl

theorem cell23_2255305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 5, 2].length) (baseStart_2255305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255305 prefixEnd_2255305 := by exact prefixLift 2255305
  have htrace : WordTrace (prefixWord ++ tailWord_2255305) baseStart_2255305 baseEnd_2255305 := by
    simpa [prefixWord, tailWord_2255305, baseEnd_2255305] using wordTrace_append hprefix tailTrace_2255305
  have hstable : (prefixWord ++ tailWord_2255305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255305).length < 2 ^ (prefixWord ++ tailWord_2255305).sum := by decide
  have hdescent : baseEnd_2255305 < baseStart_2255305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255335 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2255335 : Nat := 118140960795 + 2255335 * 2 ^ 59
def prefixEnd_2255335 : Nat := 4983230072969 + 3 ^ 40 * 2255335 * 2
def baseEnd_2255335 : Nat := 1158070891908038725140409

theorem tailTrace_2255335 : CollatzResearch.WordTrace tailWord_2255335 prefixEnd_2255335 1158070891908038725140409 := by
  unfold tailWord_2255335
  simp only [CollatzResearch.WordTrace]
  refine ⟨82258825284313950397319459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54839216856209300264879639 82258825284313950397319459)
  ·
    refine ⟨123388237926470925595979189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82258825284313950397319459 123388237926470925595979189)
    ·
      refine ⟨11567647305606649274623049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123388237926470925595979189 11567647305606649274623049)
      ·
        refine ⟨8675735479204986955967287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11567647305606649274623049 8675735479204986955967287)
        ·
          refine ⟨13013603218807480433950931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8675735479204986955967287 13013603218807480433950931)
          ·
            refine ⟨19520404828211220650926397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13013603218807480433950931 19520404828211220650926397)
            ·
              refine ⟨7320151810579207744097399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19520404828211220650926397 7320151810579207744097399)
              ·
                refine ⟨10980227715868811616146099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7320151810579207744097399 10980227715868811616146099)
                ·
                  refine ⟨16470341573803217424219149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10980227715868811616146099 16470341573803217424219149)
                  ·
                    refine ⟨6176378090176206534082181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16470341573803217424219149 6176378090176206534082181)
                    ·
                      refine ⟨1158070891908038725140409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6176378090176206534082181 1158070891908038725140409)
                      ·
                        rfl

theorem cell23_2255335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2255335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255335 prefixEnd_2255335 := by exact prefixLift 2255335
  have htrace : WordTrace (prefixWord ++ tailWord_2255335) baseStart_2255335 baseEnd_2255335 := by
    simpa [prefixWord, tailWord_2255335, baseEnd_2255335] using wordTrace_append hprefix tailTrace_2255335
  have hstable : (prefixWord ++ tailWord_2255335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255335).length < 2 ^ (prefixWord ++ tailWord_2255335).sum := by decide
  have hdescent : baseEnd_2255335 < baseStart_2255335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255345 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 5, 4]
def baseStart_2255345 : Nat := 118140960795 + 2255345 * 2 ^ 59
def prefixEnd_2255345 : Nat := 4983230072969 + 3 ^ 40 * 2255345 * 2
def baseEnd_2255345 : Nat := 386025342238194562005121

theorem tailTrace_2255345 : CollatzResearch.WordTrace tailWord_2255345 prefixEnd_2255345 386025342238194562005121 := by
  unfold tailWord_2255345
  simp only [CollatzResearch.WordTrace]
  refine ⟨82259190014277722105183489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54839460009518481403455659 82259190014277722105183489)
  ·
    refine ⟨61694392510708291578887617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82259190014277722105183489 61694392510708291578887617)
    ·
      refine ⟨46270794383031218684165713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61694392510708291578887617 46270794383031218684165713)
      ·
        refine ⟨34703095787273414013124285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46270794383031218684165713 34703095787273414013124285)
        ·
          refine ⟨13013660920227530254921607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34703095787273414013124285 13013660920227530254921607)
          ·
            refine ⟨19520491380341295382382411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13013660920227530254921607 19520491380341295382382411)
            ·
              refine ⟨29280737070511943073573617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19520491380341295382382411 29280737070511943073573617)
              ·
                refine ⟨21960552802883957305180213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29280737070511943073573617 21960552802883957305180213)
                ·
                  refine ⟨2058801825270370997360645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21960552802883957305180213 2058801825270370997360645)
                  ·
                    refine ⟨386025342238194562005121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2058801825270370997360645 386025342238194562005121)
                    ·
                      rfl

theorem cell23_2255345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_2255345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255345 prefixEnd_2255345 := by exact prefixLift 2255345
  have htrace : WordTrace (prefixWord ++ tailWord_2255345) baseStart_2255345 baseEnd_2255345 := by
    simpa [prefixWord, tailWord_2255345, baseEnd_2255345] using wordTrace_append hprefix tailTrace_2255345
  have hstable : (prefixWord ++ tailWord_2255345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255345).length < 2 ^ (prefixWord ++ tailWord_2255345).sum := by decide
  have hdescent : baseEnd_2255345 < baseStart_2255345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255442 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2255442 : Nat := 118140960795 + 2255442 * 2 ^ 59
def prefixEnd_2255442 : Nat := 4983230072969 + 3 ^ 40 * 2255442 * 2
def baseEnd_2255442 : Nat := 1158125834338069806502417

theorem tailTrace_2255442 : CollatzResearch.WordTrace tailWord_2255442 prefixEnd_2255442 1158125834338069806502417 := by
  unfold tailWord_2255442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20565681973731576917866145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54841818596617538447643053 20565681973731576917866145)
  ·
    refine ⟨15424261480298682688399609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20565681973731576917866145 15424261480298682688399609)
    ·
      refine ⟨11568196110224012016299707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15424261480298682688399609 11568196110224012016299707)
      ·
        refine ⟨17352294165336018024449561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11568196110224012016299707 17352294165336018024449561)
        ·
          refine ⟨13014220624002013518337171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17352294165336018024449561 13014220624002013518337171)
          ·
            refine ⟨19521330936003020277505757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13014220624002013518337171 19521330936003020277505757)
            ·
              refine ⟨7320499101001132604064659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19521330936003020277505757 7320499101001132604064659)
              ·
                refine ⟨10980748651501698906096989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7320499101001132604064659 10980748651501698906096989)
                ·
                  refine ⟨4117780744313137089786371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10980748651501698906096989 4117780744313137089786371)
                  ·
                    refine ⟨6176671116469705634679557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4117780744313137089786371 6176671116469705634679557)
                    ·
                      refine ⟨1158125834338069806502417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6176671116469705634679557 1158125834338069806502417)
                      ·
                        rfl

theorem cell23_2255442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2255442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255442 prefixEnd_2255442 := by exact prefixLift 2255442
  have htrace : WordTrace (prefixWord ++ tailWord_2255442) baseStart_2255442 baseEnd_2255442 := by
    simpa [prefixWord, tailWord_2255442, baseEnd_2255442] using wordTrace_append hprefix tailTrace_2255442
  have hstable : (prefixWord ++ tailWord_2255442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255442).length < 2 ^ (prefixWord ++ tailWord_2255442).sum := by decide
  have hdescent : baseEnd_2255442 < baseStart_2255442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255445 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2255445 : Nat := 118140960795 + 2255445 * 2 ^ 59
def prefixEnd_2255445 : Nat := 4983230072969 + 3 ^ 40 * 2255445 * 2
def baseEnd_2255445 : Nat := 1158127374780033294764903

theorem tailTrace_2255445 : CollatzResearch.WordTrace tailWord_2255445 prefixEnd_2255445 1158127374780033294764903 := by
  unfold tailWord_2255445
  simp only [CollatzResearch.WordTrace]
  refine ⟨82262837313915439183823789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54841891542610292789215859 82262837313915439183823789)
  ·
    refine ⟨30848563992718289693933921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82262837313915439183823789 30848563992718289693933921)
    ·
      refine ⟨23136422994538717270450441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30848563992718289693933921 23136422994538717270450441)
      ·
        refine ⟨17352317245904037952837831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23136422994538717270450441 17352317245904037952837831)
        ·
          refine ⟨26028475868856056929256747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17352317245904037952837831 26028475868856056929256747)
          ·
            refine ⟨39042713803284085393885121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26028475868856056929256747 39042713803284085393885121)
            ·
              refine ⟨29282035352463064045413841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39042713803284085393885121 29282035352463064045413841)
              ·
                refine ⟨21961526514347298034060381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29282035352463064045413841 21961526514347298034060381)
                ·
                  refine ⟨8235572442880236762772643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21961526514347298034060381 8235572442880236762772643)
                  ·
                    refine ⟨12353358664320355144158965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8235572442880236762772643 12353358664320355144158965)
                    ·
                      refine ⟨1158127374780033294764903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12353358664320355144158965 1158127374780033294764903)
                      ·
                        rfl

theorem cell23_2255445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2255445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255445 prefixEnd_2255445 := by exact prefixLift 2255445
  have htrace : WordTrace (prefixWord ++ tailWord_2255445) baseStart_2255445 baseEnd_2255445 := by
    simpa [prefixWord, tailWord_2255445, baseEnd_2255445] using wordTrace_append hprefix tailTrace_2255445
  have hstable : (prefixWord ++ tailWord_2255445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255445).length < 2 ^ (prefixWord ++ tailWord_2255445).sum := by decide
  have hdescent : baseEnd_2255445 < baseStart_2255445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255459 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 1, 1, 4]
def baseStart_2255459 : Nat := 118140960795 + 2255459 * 2 ^ 59
def prefixEnd_2255459 : Nat := 4983230072969 + 3 ^ 40 * 2255459 * 2
def baseEnd_2255459 : Nat := 1158134563509196239989839

theorem tailTrace_2255459 : CollatzResearch.WordTrace tailWord_2255459 prefixEnd_2255459 1158134563509196239989839 := by
  unfold tailWord_2255459
  simp only [CollatzResearch.WordTrace]
  refine ⟨82263347935864719574833431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54842231957243146383222287 82263347935864719574833431)
  ·
    refine ⟨123395021903797079362250147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82263347935864719574833431 123395021903797079362250147)
    ·
      refine ⟨185092532855695619043375221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123395021903797079362250147 185092532855695619043375221)
      ·
        refine ⟨17352424955221464285316427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185092532855695619043375221 17352424955221464285316427)
        ·
          refine ⟨26028637432832196427974641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17352424955221464285316427 26028637432832196427974641)
          ·
            refine ⟨19521478074624147320980981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26028637432832196427974641 19521478074624147320980981)
            ·
              refine ⟨1830138569496013811341967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19521478074624147320980981 1830138569496013811341967)
              ·
                refine ⟨2745207854244020717012951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830138569496013811341967 2745207854244020717012951)
                ·
                  refine ⟨4117811781366031075519427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745207854244020717012951 4117811781366031075519427)
                  ·
                    refine ⟨6176717672049046613279141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4117811781366031075519427 6176717672049046613279141)
                    ·
                      refine ⟨1158134563509196239989839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6176717672049046613279141 1158134563509196239989839)
                      ·
                        rfl

theorem cell23_2255459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_2255459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255459 prefixEnd_2255459 := by exact prefixLift 2255459
  have htrace : WordTrace (prefixWord ++ tailWord_2255459) baseStart_2255459 baseEnd_2255459 := by
    simpa [prefixWord, tailWord_2255459, baseEnd_2255459] using wordTrace_append hprefix tailTrace_2255459
  have hstable : (prefixWord ++ tailWord_2255459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255459).length < 2 ^ (prefixWord ++ tailWord_2255459).sum := by decide
  have hdescent : baseEnd_2255459 < baseStart_2255459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255469 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2255469 : Nat := 118140960795 + 2255469 * 2 ^ 59
def prefixEnd_2255469 : Nat := 4983230072969 + 3 ^ 40 * 2255469 * 2
def baseEnd_2255469 : Nat := 386046566105247066954931

theorem tailTrace_2255469 : CollatzResearch.WordTrace tailWord_2255469 prefixEnd_2255469 386046566105247066954931 := by
  unfold tailWord_2255469
  simp only [CollatzResearch.WordTrace]
  refine ⟨82263712665828491282697461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54842475110552327521798307 82263712665828491282697461)
  ·
    refine ⟨7712223062421421057752887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82263712665828491282697461 7712223062421421057752887)
    ·
      refine ⟨11568334593632131586629331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7712223062421421057752887 11568334593632131586629331)
      ·
        refine ⟨17352501890448197379943997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11568334593632131586629331 17352501890448197379943997)
        ·
          refine ⟨6507188208918074017478999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17352501890448197379943997 6507188208918074017478999)
          ·
            refine ⟨9760782313377111026218499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6507188208918074017478999 9760782313377111026218499)
            ·
              refine ⟨14641173470065666539327749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9760782313377111026218499 14641173470065666539327749)
              ·
                refine ⟨2745220025637312476123953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14641173470065666539327749 2745220025637312476123953)
                ·
                  refine ⟨2058915019227984357092965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2745220025637312476123953 2058915019227984357092965)
                  ·
                    refine ⟨386046566105247066954931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2058915019227984357092965 386046566105247066954931)
                    ·
                      rfl

theorem cell23_2255469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2255469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255469 prefixEnd_2255469 := by exact prefixLift 2255469
  have htrace : WordTrace (prefixWord ++ tailWord_2255469) baseStart_2255469 baseEnd_2255469 := by
    simpa [prefixWord, tailWord_2255469, baseEnd_2255469] using wordTrace_append hprefix tailTrace_2255469
  have hstable : (prefixWord ++ tailWord_2255469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255469).length < 2 ^ (prefixWord ++ tailWord_2255469).sum := by decide
  have hdescent : baseEnd_2255469 < baseStart_2255469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255470 : List Nat := [4, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_2255470 : Nat := 118140960795 + 2255470 * 2 ^ 59
def prefixEnd_2255470 : Nat := 4983230072969 + 3 ^ 40 * 2255470 * 2
def baseEnd_2255470 : Nat := 1158140211796395696952289

theorem tailTrace_2255470 : CollatzResearch.WordTrace tailWord_2255470 prefixEnd_2255470 1158140211796395696952289 := by
  unfold tailWord_2255470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10282968642353108556685483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54842499425883245635655909 10282968642353108556685483)
  ·
    refine ⟨15424452963529662835028225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10282968642353108556685483 15424452963529662835028225)
    ·
      refine ⟨11568339722647247126271169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15424452963529662835028225 11568339722647247126271169)
      ·
        refine ⟨8676254791985435344703377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11568339722647247126271169 8676254791985435344703377)
        ·
          refine ⟨6507191093989076508527533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8676254791985435344703377 6507191093989076508527533)
          ·
            refine ⟨2440196660245903690697825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6507191093989076508527533 2440196660245903690697825)
            ·
              refine ⟨1830147495184427768023369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2440196660245903690697825 1830147495184427768023369)
              ·
                refine ⟨1372610621388320826017527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1830147495184427768023369 1372610621388320826017527)
                ·
                  refine ⟨2058915932082481239026291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372610621388320826017527 2058915932082481239026291)
                  ·
                    refine ⟨3088373898123721858539437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2058915932082481239026291 3088373898123721858539437)
                    ·
                      refine ⟨1158140211796395696952289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3088373898123721858539437 1158140211796395696952289)
                      ·
                        rfl

theorem cell23_2255470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_2255470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255470 prefixEnd_2255470 := by exact prefixLift 2255470
  have htrace : WordTrace (prefixWord ++ tailWord_2255470) baseStart_2255470 baseEnd_2255470 := by
    simpa [prefixWord, tailWord_2255470, baseEnd_2255470] using wordTrace_append hprefix tailTrace_2255470
  have hstable : (prefixWord ++ tailWord_2255470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255470).length < 2 ^ (prefixWord ++ tailWord_2255470).sum := by decide
  have hdescent : baseEnd_2255470 < baseStart_2255470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255495 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 2, 7]
def baseStart_2255495 : Nat := 118140960795 + 2255495 * 2 ^ 59
def prefixEnd_2255495 : Nat := 4983230072969 + 3 ^ 40 * 2255495 * 2
def baseEnd_2255495 : Nat := 386051016270919366379891

theorem tailTrace_2255495 : CollatzResearch.WordTrace tailWord_2255495 prefixEnd_2255495 386051016270919366379891 := by
  unfold tailWord_2255495
  simp only [CollatzResearch.WordTrace]
  refine ⟨82264660963734297723143939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54843107309156198482095959 82264660963734297723143939)
  ·
    refine ⟨123396991445601446584715909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82264660963734297723143939 123396991445601446584715909)
    ·
      refine ⟨23136935896050271234634233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123396991445601446584715909 23136935896050271234634233)
      ·
        refine ⟨17352701922037703425975675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23136935896050271234634233 17352701922037703425975675)
        ·
          refine ⟨26029052883056555138963513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17352701922037703425975675 26029052883056555138963513)
          ·
            refine ⟨19521789662292416354222635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26029052883056555138963513 19521789662292416354222635)
            ·
              refine ⟨29282684493438624531333953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19521789662292416354222635 29282684493438624531333953)
              ·
                refine ⟨21962013370078968398500465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29282684493438624531333953 21962013370078968398500465)
                ·
                  refine ⟨16471510027559226298875349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21962013370078968398500465 16471510027559226298875349)
                  ·
                    refine ⟨386051016270919366379891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16471510027559226298875349 386051016270919366379891)
                    ·
                      rfl

theorem cell23_2255495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_2255495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255495 prefixEnd_2255495 := by exact prefixLift 2255495
  have htrace : WordTrace (prefixWord ++ tailWord_2255495) baseStart_2255495 baseEnd_2255495 := by
    simpa [prefixWord, tailWord_2255495, baseEnd_2255495] using wordTrace_append hprefix tailTrace_2255495
  have hstable : (prefixWord ++ tailWord_2255495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255495).length < 2 ^ (prefixWord ++ tailWord_2255495).sum := by decide
  have hdescent : baseEnd_2255495 < baseStart_2255495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255532 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 10, 2]
def baseStart_2255532 : Nat := 118140960795 + 2255532 * 2 ^ 59
def prefixEnd_2255532 : Nat := 4983230072969 + 3 ^ 40 * 2255532 * 2
def baseEnd_2255532 : Nat := 1158172047596974454377003

theorem tailTrace_2255532 : CollatzResearch.WordTrace tailWord_2255532 prefixEnd_2255532 1158172047596974454377003 := by
  unfold tailWord_2255532
  simp only [CollatzResearch.WordTrace]
  refine ⟨41133005232300126521120425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54844006976400168694827233 41133005232300126521120425)
  ·
    refine ⟨30849753924225094890840319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41133005232300126521120425 30849753924225094890840319)
    ·
      refine ⟨46274630886337642336260479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30849753924225094890840319 46274630886337642336260479)
      ·
        refine ⟨69411946329506463504390719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46274630886337642336260479 69411946329506463504390719)
        ·
          refine ⟨104117919494259695256586079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69411946329506463504390719 104117919494259695256586079)
          ·
            refine ⟨156176879241389542884879119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104117919494259695256586079 156176879241389542884879119)
            ·
              refine ⟨234265318862084314327318679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156176879241389542884879119 234265318862084314327318679)
              ·
                refine ⟨351397978293126471490978019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234265318862084314327318679 351397978293126471490978019)
                ·
                  refine ⟨527096967439689707236467029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351397978293126471490978019 527096967439689707236467029)
                  ·
                    refine ⟨1544229396795965939169337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 527096967439689707236467029 1544229396795965939169337)
                    ·
                      refine ⟨1158172047596974454377003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544229396795965939169337 1158172047596974454377003)
                      ·
                        rfl

theorem cell23_2255532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_2255532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255532 prefixEnd_2255532 := by exact prefixLift 2255532
  have htrace : WordTrace (prefixWord ++ tailWord_2255532) baseStart_2255532 baseEnd_2255532 := by
    simpa [prefixWord, tailWord_2255532, baseEnd_2255532] using wordTrace_append hprefix tailTrace_2255532
  have hstable : (prefixWord ++ tailWord_2255532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255532).length < 2 ^ (prefixWord ++ tailWord_2255532).sum := by decide
  have hdescent : baseEnd_2255532 < baseStart_2255532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255543 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 2, 1, 3]
def baseStart_2255543 : Nat := 118140960795 + 2255543 * 2 ^ 59
def prefixEnd_2255543 : Nat := 4983230072969 + 3 ^ 40 * 2255543 * 2
def baseEnd_2255543 : Nat := 1158177695884173911339453

theorem tailTrace_2255543 : CollatzResearch.WordTrace tailWord_2255543 prefixEnd_2255543 1158177695884173911339453 := by
  unfold tailWord_2255543
  simp only [CollatzResearch.WordTrace]
  refine ⟨82266411667560401920891283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54844274445040267947260855 82266411667560401920891283)
  ·
    refine ⟨123399617501340602881336925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82266411667560401920891283 123399617501340602881336925)
    ·
      refine ⟨46274856563002726080501347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123399617501340602881336925 46274856563002726080501347)
      ·
        refine ⟨69412284844504089120752021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46274856563002726080501347 69412284844504089120752021)
        ·
          refine ⟨3253700852086129177535251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69412284844504089120752021 3253700852086129177535251)
          ·
            refine ⟨4880551278129193766302877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253700852086129177535251 4880551278129193766302877)
            ·
              refine ⟨1830206729298447662363579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4880551278129193766302877 1830206729298447662363579)
              ·
                refine ⟨2745310093947671493545369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830206729298447662363579 2745310093947671493545369)
                ·
                  refine ⟨2058982570460753620159027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2745310093947671493545369 2058982570460753620159027)
                  ·
                    refine ⟨3088473855691130430238541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2058982570460753620159027 3088473855691130430238541)
                    ·
                      refine ⟨1158177695884173911339453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3088473855691130430238541 1158177695884173911339453)
                      ·
                        rfl

theorem cell23_2255543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_2255543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255543 prefixEnd_2255543 := by exact prefixLift 2255543
  have htrace : WordTrace (prefixWord ++ tailWord_2255543) baseStart_2255543 baseEnd_2255543 := by
    simpa [prefixWord, tailWord_2255543, baseEnd_2255543] using wordTrace_append hprefix tailTrace_2255543
  have hstable : (prefixWord ++ tailWord_2255543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255543).length < 2 ^ (prefixWord ++ tailWord_2255543).sum := by decide
  have hdescent : baseEnd_2255543 < baseStart_2255543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255566 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_2255566 : Nat := 118140960795 + 2255566 * 2 ^ 59
def prefixEnd_2255566 : Nat := 4983230072969 + 3 ^ 40 * 2255566 * 2
def baseEnd_2255566 : Nat := 1158189505939227321351847

theorem tailTrace_2255566 : CollatzResearch.WordTrace tailWord_2255566 prefixEnd_2255566 1158189505939227321351847 := by
  unfold tailWord_2255566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10283406318309634606122319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54844833697651384565985701 10283406318309634606122319)
  ·
    refine ⟨15425109477464451909183479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10283406318309634606122319 15425109477464451909183479)
    ·
      refine ⟨23137664216196677863775219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15425109477464451909183479 23137664216196677863775219)
      ·
        refine ⟨34706496324295016795662829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23137664216196677863775219 34706496324295016795662829)
        ·
          refine ⟨13014936121610631298373561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34706496324295016795662829 13014936121610631298373561)
          ·
            refine ⟨9761202091207973473780171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13014936121610631298373561 9761202091207973473780171)
            ·
              refine ⟨14641803136811960210670257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9761202091207973473780171 14641803136811960210670257)
              ·
                refine ⟨10981352352608970158002693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14641803136811960210670257 10981352352608970158002693)
                ·
                  refine ⟨2059003566114181904625505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10981352352608970158002693 2059003566114181904625505)
                  ·
                    refine ⟨1544252674585636428469129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2059003566114181904625505 1544252674585636428469129)
                    ·
                      refine ⟨1158189505939227321351847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544252674585636428469129 1158189505939227321351847)
                      ·
                        rfl

theorem cell23_2255566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_2255566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255566 prefixEnd_2255566 := by exact prefixLift 2255566
  have htrace : WordTrace (prefixWord ++ tailWord_2255566) baseStart_2255566 baseEnd_2255566 := by
    simpa [prefixWord, tailWord_2255566, baseEnd_2255566] using wordTrace_append hprefix tailTrace_2255566
  have hstable : (prefixWord ++ tailWord_2255566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255566).length < 2 ^ (prefixWord ++ tailWord_2255566).sum := by decide
  have hdescent : baseEnd_2255566 < baseStart_2255566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255589 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 7]
def baseStart_2255589 : Nat := 118140960795 + 2255589 * 2 ^ 59
def prefixEnd_2255589 : Nat := 4983230072969 + 3 ^ 40 * 2255589 * 2
def baseEnd_2255589 : Nat := 128689035110475636818249

theorem tailTrace_2255589 : CollatzResearch.WordTrace tailWord_2255589 prefixEnd_2255589 128689035110475636818249 := by
  unfold tailWord_2255589
  simp only [CollatzResearch.WordTrace]
  refine ⟨82268089425393751777065821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54845392950262501184710547 82268089425393751777065821)
  ·
    refine ⟨30850533534522656916399683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82268089425393751777065821 30850533534522656916399683)
    ·
      refine ⟨46275800301783985374599525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30850533534522656916399683 46275800301783985374599525)
      ·
        refine ⟨8676712556584497257737411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46275800301783985374599525 8676712556584497257737411)
        ·
          refine ⟨13015068834876745886606117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8676712556584497257737411 13015068834876745886606117)
          ·
            refine ⟨2440325406539389853738647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13015068834876745886606117 2440325406539389853738647)
            ·
              refine ⟨3660488109809084780607971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440325406539389853738647 3660488109809084780607971)
              ·
                refine ⟨5490732164713627170911957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660488109809084780607971 5490732164713627170911957)
                ·
                  refine ⟨128689035110475636818249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5490732164713627170911957 128689035110475636818249)
                  ·
                    rfl

theorem cell23_2255589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_2255589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255589 prefixEnd_2255589 := by exact prefixLift 2255589
  have htrace : WordTrace (prefixWord ++ tailWord_2255589) baseStart_2255589 baseEnd_2255589 := by
    simpa [prefixWord, tailWord_2255589, baseEnd_2255589] using wordTrace_append hprefix tailTrace_2255589
  have hstable : (prefixWord ++ tailWord_2255589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255589).length < 2 ^ (prefixWord ++ tailWord_2255589).sum := by decide
  have hdescent : baseEnd_2255589 < baseStart_2255589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255604 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2255604 : Nat := 118140960795 + 2255604 * 2 ^ 59
def prefixEnd_2255604 : Nat := 4983230072969 + 3 ^ 40 * 2255604 * 2
def baseEnd_2255604 : Nat := 1158209018204098172676673

theorem tailTrace_2255604 : CollatzResearch.WordTrace tailWord_2255604 prefixEnd_2255604 1158209018204098172676673 := by
  unfold tailWord_2255604
  simp only [CollatzResearch.WordTrace]
  refine ⟨41134318260169704669430933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54845757680226272892574577 41134318260169704669430933)
  ·
    refine ⟨1928171168445454906379575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41134318260169704669430933 1928171168445454906379575)
    ·
      refine ⟨2892256752668182359569363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1928171168445454906379575 2892256752668182359569363)
      ·
        refine ⟨4338385129002273539354045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2892256752668182359569363 4338385129002273539354045)
        ·
          refine ⟨1626894423375852577257767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4338385129002273539354045 1626894423375852577257767)
          ·
            refine ⟨2440341635063778865886651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626894423375852577257767 2440341635063778865886651)
            ·
              refine ⟨3660512452595668298829977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440341635063778865886651 3660512452595668298829977)
              ·
                refine ⟨2745384339446751224122483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3660512452595668298829977 2745384339446751224122483)
                ·
                  refine ⟨4118076509170126836183725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745384339446751224122483 4118076509170126836183725)
                  ·
                    refine ⟨1544278690938797563568897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4118076509170126836183725 1544278690938797563568897)
                    ·
                      refine ⟨1158209018204098172676673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544278690938797563568897 1158209018204098172676673)
                      ·
                        rfl

theorem cell23_2255604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2255604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255604 prefixEnd_2255604 := by exact prefixLift 2255604
  have htrace : WordTrace (prefixWord ++ tailWord_2255604) baseStart_2255604 baseEnd_2255604 := by
    simpa [prefixWord, tailWord_2255604, baseEnd_2255604] using wordTrace_append hprefix tailTrace_2255604
  have hstable : (prefixWord ++ tailWord_2255604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255604).length < 2 ^ (prefixWord ++ tailWord_2255604).sum := by decide
  have hdescent : baseEnd_2255604 < baseStart_2255604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255642 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_2255642 : Nat := 118140960795 + 2255642 * 2 ^ 59
def prefixEnd_2255642 : Nat := 4983230072969 + 3 ^ 40 * 2255642 * 2
def baseEnd_2255642 : Nat := 1158228530468969024001497

theorem tailTrace_2255642 : CollatzResearch.WordTrace tailWord_2255642 prefixEnd_2255642 1158228530468969024001497 := by
  unfold tailWord_2255642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20567505623550435457186295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54846681662801161219163453 20567505623550435457186295)
  ·
    refine ⟨30851258435325653185779443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20567505623550435457186295 30851258435325653185779443)
    ·
      refine ⟨46276887652988479778669165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30851258435325653185779443 46276887652988479778669165)
      ·
        refine ⟨17353832869870679917000937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46276887652988479778669165 17353832869870679917000937)
        ·
          refine ⟨13015374652403009937750703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17353832869870679917000937 13015374652403009937750703)
          ·
            refine ⟨19523061978604514906626055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13015374652403009937750703 19523061978604514906626055)
            ·
              refine ⟨29284592967906772359939083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19523061978604514906626055 29284592967906772359939083)
              ·
                refine ⟨43926889451860158539908625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29284592967906772359939083 43926889451860158539908625)
                ·
                  refine ⟨32945167088895118904931469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43926889451860158539908625 32945167088895118904931469)
                  ·
                    refine ⟨12354437658335669589349301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32945167088895118904931469 12354437658335669589349301)
                    ·
                      refine ⟨1158228530468969024001497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12354437658335669589349301 1158228530468969024001497)
                      ·
                        rfl

theorem cell23_2255642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_2255642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255642 prefixEnd_2255642 := by exact prefixLift 2255642
  have htrace : WordTrace (prefixWord ++ tailWord_2255642) baseStart_2255642 baseEnd_2255642 := by
    simpa [prefixWord, tailWord_2255642, baseEnd_2255642] using wordTrace_append hprefix tailTrace_2255642
  have hstable : (prefixWord ++ tailWord_2255642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255642).length < 2 ^ (prefixWord ++ tailWord_2255642).sum := by decide
  have hdescent : baseEnd_2255642 < baseStart_2255642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255649 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 3, 4]
def baseStart_2255649 : Nat := 118140960795 + 2255649 * 2 ^ 59
def prefixEnd_2255649 : Nat := 4983230072969 + 3 ^ 40 * 2255649 * 2
def baseEnd_2255649 : Nat := 386077374944516832204655

theorem tailTrace_2255649 : CollatzResearch.WordTrace tailWord_2255649 prefixEnd_2255649 386077374944516832204655 := by
  unfold tailWord_2255649
  simp only [CollatzResearch.WordTrace]
  refine ⟨82270277805176382024250001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54846851870117588016166667 82270277805176382024250001)
  ·
    refine ⟨61702708353882286518187501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82270277805176382024250001 61702708353882286518187501)
    ·
      refine ⟨23138515632705857444320313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61702708353882286518187501 23138515632705857444320313)
      ·
        refine ⟨17353886724529393083240235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23138515632705857444320313 17353886724529393083240235)
        ·
          refine ⟨26030830086794089624860353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17353886724529393083240235 26030830086794089624860353)
          ·
            refine ⟨19523122565095567218645265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26030830086794089624860353 19523122565095567218645265)
            ·
              refine ⟨14642341923821675413983949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19523122565095567218645265 14642341923821675413983949)
              ·
                refine ⟨5490878221433128280243981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14642341923821675413983949 5490878221433128280243981)
                ·
                  refine ⟨2059079333037423105091493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5490878221433128280243981 2059079333037423105091493)
                  ·
                    refine ⟨386077374944516832204655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2059079333037423105091493 386077374944516832204655)
                    ·
                      rfl

theorem cell23_2255649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_2255649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255649 prefixEnd_2255649 := by exact prefixLift 2255649
  have htrace : WordTrace (prefixWord ++ tailWord_2255649) baseStart_2255649 baseEnd_2255649 := by
    simpa [prefixWord, tailWord_2255649, baseEnd_2255649] using wordTrace_append hprefix tailTrace_2255649
  have hstable : (prefixWord ++ tailWord_2255649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255649).length < 2 ^ (prefixWord ++ tailWord_2255649).sum := by decide
  have hdescent : baseEnd_2255649 < baseStart_2255649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255656 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_2255656 : Nat := 118140960795 + 2255656 * 2 ^ 59
def prefixEnd_2255656 : Nat := 4983230072969 + 3 ^ 40 * 2255656 * 2
def baseEnd_2255656 : Nat := 1158235719198131969226433

theorem tailTrace_2255656 : CollatzResearch.WordTrace tailWord_2255656 prefixEnd_2255656 1158235719198131969226433 := by
  unfold tailWord_2255656
  simp only [CollatzResearch.WordTrace]
  refine ⟨41135266558075511109877411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54847022077434014813169881 41135266558075511109877411)
  ·
    refine ⟨61702899837113266664816117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41135266558075511109877411 61702899837113266664816117)
    ·
      refine ⟨5784646859729368749826511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61702899837113266664816117 5784646859729368749826511)
      ·
        refine ⟨8676970289594053124739767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784646859729368749826511 8676970289594053124739767)
        ·
          refine ⟨13015455434391079687109651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8676970289594053124739767 13015455434391079687109651)
          ·
            refine ⟨19523183151586619530664477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13015455434391079687109651 19523183151586619530664477)
            ·
              refine ⟨7321193681844982323999179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19523183151586619530664477 7321193681844982323999179)
              ·
                refine ⟨10981790522767473485998769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321193681844982323999179 10981790522767473485998769)
                ·
                  refine ⟨8236342892075605114499077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10981790522767473485998769 8236342892075605114499077)
                  ·
                    refine ⟨1544314292264175958968577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8236342892075605114499077 1544314292264175958968577)
                    ·
                      refine ⟨1158235719198131969226433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544314292264175958968577 1158235719198131969226433)
                      ·
                        rfl

theorem cell23_2255656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_2255656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255656 prefixEnd_2255656 := by exact prefixLift 2255656
  have htrace : WordTrace (prefixWord ++ tailWord_2255656) baseStart_2255656 baseEnd_2255656 := by
    simpa [prefixWord, tailWord_2255656, baseEnd_2255656] using wordTrace_append hprefix tailTrace_2255656
  have hstable : (prefixWord ++ tailWord_2255656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255656).length < 2 ^ (prefixWord ++ tailWord_2255656).sum := by decide
  have hdescent : baseEnd_2255656 < baseStart_2255656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255670 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2255670 : Nat := 118140960795 + 2255670 * 2 ^ 59
def prefixEnd_2255670 : Nat := 4983230072969 + 3 ^ 40 * 2255670 * 2
def baseEnd_2255670 : Nat := 386080969309098304817123

theorem tailTrace_2255670 : CollatzResearch.WordTrace tailWord_2255670 prefixEnd_2255670 386080969309098304817123 := by
  unfold tailWord_2255670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141940233631268913172779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54847362492066868407176309 5141940233631268913172779)
  ·
    refine ⟨7712910350446903369759169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5141940233631268913172779 7712910350446903369759169)
    ·
      refine ⟨5784682762835177527319377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7712910350446903369759169 5784682762835177527319377)
      ·
        refine ⟨4338512072126383145489533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5784682762835177527319377 4338512072126383145489533)
        ·
          refine ⟨1626942027047393679558575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4338512072126383145489533 1626942027047393679558575)
          ·
            refine ⟨2440413040571090519337863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626942027047393679558575 2440413040571090519337863)
            ·
              refine ⟨3660619560856635779006795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440413040571090519337863 3660619560856635779006795)
              ·
                refine ⟨5490929341284953668510193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660619560856635779006795 5490929341284953668510193)
                ·
                  refine ⟨4118197005963715251382645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5490929341284953668510193 4118197005963715251382645)
                  ·
                    refine ⟨386080969309098304817123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4118197005963715251382645 386080969309098304817123)
                    ·
                      rfl

theorem cell23_2255670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2255670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255670 prefixEnd_2255670 := by exact prefixLift 2255670
  have htrace : WordTrace (prefixWord ++ tailWord_2255670) baseStart_2255670 baseEnd_2255670 := by
    simpa [prefixWord, tailWord_2255670, baseEnd_2255670] using wordTrace_append hprefix tailTrace_2255670
  have hstable : (prefixWord ++ tailWord_2255670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255670).length < 2 ^ (prefixWord ++ tailWord_2255670).sum := by decide
  have hdescent : baseEnd_2255670 < baseStart_2255670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255706 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_2255706 : Nat := 118140960795 + 2255706 * 2 ^ 59
def prefixEnd_2255706 : Nat := 4983230072969 + 3 ^ 40 * 2255706 * 2
def baseEnd_2255706 : Nat := 1158261393230856773601203

theorem tailTrace_2255706 : CollatzResearch.WordTrace tailWord_2255706 prefixEnd_2255706 1158261393230856773601203 := by
  unfold tailWord_2255706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20568089191492470189768743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54848237843979920506049981 20568089191492470189768743)
  ·
    refine ⟨30852133787238705284653115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20568089191492470189768743 30852133787238705284653115)
    ·
      refine ⟨46278200680858057926979673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30852133787238705284653115 46278200680858057926979673)
      ·
        refine ⟨34708650510643543445234755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46278200680858057926979673 34708650510643543445234755)
        ·
          refine ⟨52062975765965315167852133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34708650510643543445234755 52062975765965315167852133)
          ·
            refine ⟨9761807956118496593972275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52062975765965315167852133 9761807956118496593972275)
            ·
              refine ⟨14642711934177744890958413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9761807956118496593972275 14642711934177744890958413)
              ·
                refine ⟨5491016975316654334109405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14642711934177744890958413 5491016975316654334109405)
                ·
                  refine ⟨2059131365743745375291027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5491016975316654334109405 2059131365743745375291027)
                  ·
                    refine ⟨3088697048615618062936541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2059131365743745375291027 3088697048615618062936541)
                    ·
                      refine ⟨1158261393230856773601203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3088697048615618062936541 1158261393230856773601203)
                      ·
                        rfl

theorem cell23_2255706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_2255706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255706 prefixEnd_2255706 := by exact prefixLift 2255706
  have htrace : WordTrace (prefixWord ++ tailWord_2255706) baseStart_2255706 baseEnd_2255706 := by
    simpa [prefixWord, tailWord_2255706, baseEnd_2255706] using wordTrace_append hprefix tailTrace_2255706
  have hstable : (prefixWord ++ tailWord_2255706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255706).length < 2 ^ (prefixWord ++ tailWord_2255706).sum := by decide
  have hdescent : baseEnd_2255706 < baseStart_2255706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255716 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_2255716 : Nat := 118140960795 + 2255716 * 2 ^ 59
def prefixEnd_2255716 : Nat := 4983230072969 + 3 ^ 40 * 2255716 * 2
def baseEnd_2255716 : Nat := 1158266528037401734476157

theorem tailTrace_2255716 : CollatzResearch.WordTrace tailWord_2255716 prefixEnd_2255716 1158266528037401734476157 := by
  unfold tailWord_2255716
  simp only [CollatzResearch.WordTrace]
  refine ⟨41136360747966826233469501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54848480997289101644626001 41136360747966826233469501)
  ·
    refine ⟨15426135280487559837551063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41136360747966826233469501 15426135280487559837551063)
    ·
      refine ⟨23139202920731339756326595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15426135280487559837551063 23139202920731339756326595)
      ·
        refine ⟨34708804381097009634489893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23139202920731339756326595 34708804381097009634489893)
        ·
          refine ⟨6507900821455689306466855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34708804381097009634489893 6507900821455689306466855)
          ·
            refine ⟨9761851232183533959700283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6507900821455689306466855 9761851232183533959700283)
            ·
              refine ⟨14642776848275300939550425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9761851232183533959700283 14642776848275300939550425)
              ·
                refine ⟨10982082636206475704662819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14642776848275300939550425 10982082636206475704662819)
                ·
                  refine ⟨16473123954309713556994229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10982082636206475704662819 16473123954309713556994229)
                  ·
                    refine ⟨1544355370716535645968209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16473123954309713556994229 1544355370716535645968209)
                    ·
                      refine ⟨1158266528037401734476157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544355370716535645968209 1158266528037401734476157)
                      ·
                        rfl

theorem cell23_2255716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_2255716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255716 prefixEnd_2255716 := by exact prefixLift 2255716
  have htrace : WordTrace (prefixWord ++ tailWord_2255716) baseStart_2255716 baseEnd_2255716 := by
    simpa [prefixWord, tailWord_2255716, baseEnd_2255716] using wordTrace_append hprefix tailTrace_2255716
  have hstable : (prefixWord ++ tailWord_2255716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255716).length < 2 ^ (prefixWord ++ tailWord_2255716).sum := by decide
  have hdescent : baseEnd_2255716 < baseStart_2255716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255739 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 4, 4]
def baseStart_2255739 : Nat := 118140960795 + 2255739 * 2 ^ 59
def prefixEnd_2255739 : Nat := 4983230072969 + 3 ^ 40 * 2255739 * 2
def baseEnd_2255739 : Nat := 386092779364151714829517

theorem tailTrace_2255739 : CollatzResearch.WordTrace tailWord_2255739 prefixEnd_2255739 386092779364151714829517 := by
  unfold tailWord_2255739
  simp only [CollatzResearch.WordTrace]
  refine ⟨82273560374850327395026271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54849040249900218263350847 82273560374850327395026271)
  ·
    refine ⟨123410340562275491092539407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82273560374850327395026271 123410340562275491092539407)
    ·
      refine ⟨185115510843413236638809111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123410340562275491092539407 185115510843413236638809111)
      ·
        refine ⟨277673266265119854958213667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185115510843413236638809111 277673266265119854958213667)
        ·
          refine ⟨416509899397679782437320501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277673266265119854958213667 416509899397679782437320501)
          ·
            refine ⟨39047803068532479603498797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 416509899397679782437320501 39047803068532479603498797)
            ·
              refine ⟨14642926150699679851312049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39047803068532479603498797 14642926150699679851312049)
              ·
                refine ⟨10982194613024759888484037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14642926150699679851312049 10982194613024759888484037)
                ·
                  refine ⟨2059161489942142479090757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10982194613024759888484037 2059161489942142479090757)
                  ·
                    refine ⟨386092779364151714829517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2059161489942142479090757 386092779364151714829517)
                    ·
                      rfl

theorem cell23_2255739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 4].length) (baseStart_2255739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255739 prefixEnd_2255739 := by exact prefixLift 2255739
  have htrace : WordTrace (prefixWord ++ tailWord_2255739) baseStart_2255739 baseEnd_2255739 := by
    simpa [prefixWord, tailWord_2255739, baseEnd_2255739] using wordTrace_append hprefix tailTrace_2255739
  have hstable : (prefixWord ++ tailWord_2255739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255739).length < 2 ^ (prefixWord ++ tailWord_2255739).sum := by decide
  have hdescent : baseEnd_2255739 < baseStart_2255739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255749 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_2255749 : Nat := 118140960795 + 2255749 * 2 ^ 59
def prefixEnd_2255749 : Nat := 4983230072969 + 3 ^ 40 * 2255749 * 2
def baseEnd_2255749 : Nat := 1158283472899000105363505

theorem tailTrace_2255749 : CollatzResearch.WordTrace tailWord_2255749 prefixEnd_2255749 1158283472899000105363505 := by
  unfold tailWord_2255749
  simp only [CollatzResearch.WordTrace]
  refine ⟨82273925104814099102890301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54849283403209399401926867 82273925104814099102890301)
  ·
    refine ⟨30852721914305287163583863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82273925104814099102890301 30852721914305287163583863)
    ·
      refine ⟨46279082871457930745375795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30852721914305287163583863 46279082871457930745375795)
      ·
        refine ⟨69418624307186896118063693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46279082871457930745375795 69418624307186896118063693)
        ·
          refine ⟨26031984115195086044273885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69418624307186896118063693 26031984115195086044273885)
          ·
            refine ⟨9761994043198157266602707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26031984115195086044273885 9761994043198157266602707)
            ·
              refine ⟨14642991064797235899904061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9761994043198157266602707 14642991064797235899904061)
              ·
                refine ⟨5491121649298963462464023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14642991064797235899904061 5491121649298963462464023)
                ·
                  refine ⟨8236682473948445193696035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491121649298963462464023 8236682473948445193696035)
                  ·
                    refine ⟨12355023710922667790544053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8236682473948445193696035 12355023710922667790544053)
                    ·
                      refine ⟨1158283472899000105363505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12355023710922667790544053 1158283472899000105363505)
                      ·
                        rfl

theorem cell23_2255749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_2255749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255749 prefixEnd_2255749 := by exact prefixLift 2255749
  have htrace : WordTrace (prefixWord ++ tailWord_2255749) baseStart_2255749 baseEnd_2255749 := by
    simpa [prefixWord, tailWord_2255749, baseEnd_2255749] using wordTrace_append hprefix tailTrace_2255749
  have hstable : (prefixWord ++ tailWord_2255749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255749).length < 2 ^ (prefixWord ++ tailWord_2255749).sum := by decide
  have hdescent : baseEnd_2255749 < baseStart_2255749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255783 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2255783 : Nat := 118140960795 + 2255783 * 2 ^ 59
def prefixEnd_2255783 : Nat := 4983230072969 + 3 ^ 40 * 2255783 * 2
def baseEnd_2255783 : Nat := 1158300931241252972338349

theorem tailTrace_2255783 : CollatzResearch.WordTrace tailWord_2255783 prefixEnd_2255783 1158300931241252972338349 := by
  unfold tailWord_2255783
  simp only [CollatzResearch.WordTrace]
  refine ⟨82275165186690922909628003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54850110124460615273085335 82275165186690922909628003)
  ·
    refine ⟨123412747780036384364442005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82275165186690922909628003 123412747780036384364442005)
    ·
      refine ⟨5784972552189205517083219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123412747780036384364442005 5784972552189205517083219)
      ·
        refine ⟨8677458828283808275624829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784972552189205517083219 8677458828283808275624829)
        ·
          refine ⟨3254047060606428103359311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8677458828283808275624829 3254047060606428103359311)
          ·
            refine ⟨4881070590909642155038967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3254047060606428103359311 4881070590909642155038967)
            ·
              refine ⟨7321605886364463232558451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881070590909642155038967 7321605886364463232558451)
              ·
                refine ⟨10982408829546694848837677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321605886364463232558451 10982408829546694848837677)
                ·
                  refine ⟨4118403311080010568314129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10982408829546694848837677 4118403311080010568314129)
                  ·
                    refine ⟨3088802483310007926235597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4118403311080010568314129 3088802483310007926235597)
                    ·
                      refine ⟨1158300931241252972338349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3088802483310007926235597 1158300931241252972338349)
                      ·
                        rfl

theorem cell23_2255783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2255783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255783 prefixEnd_2255783 := by exact prefixLift 2255783
  have htrace : WordTrace (prefixWord ++ tailWord_2255783) baseStart_2255783 baseEnd_2255783 := by
    simpa [prefixWord, tailWord_2255783, baseEnd_2255783] using wordTrace_append hprefix tailTrace_2255783
  have hstable : (prefixWord ++ tailWord_2255783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255783).length < 2 ^ (prefixWord ++ tailWord_2255783).sum := by decide
  have hdescent : baseEnd_2255783 < baseStart_2255783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255819 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 4]
def baseStart_2255819 : Nat := 118140960795 + 2255819 * 2 ^ 59
def prefixEnd_2255819 : Nat := 4983230072969 + 3 ^ 40 * 2255819 * 2
def baseEnd_2255819 : Nat := 1158319416544814831488183

theorem tailTrace_2255819 : CollatzResearch.WordTrace tailWord_2255819 prefixEnd_2255819 1158319416544814831488183 := by
  unfold tailWord_2255819
  simp only [CollatzResearch.WordTrace]
  refine ⟨82276478214560501057938511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54850985476373667371959007 82276478214560501057938511)
  ·
    refine ⟨123414717321840751586907767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82276478214560501057938511 123414717321840751586907767)
    ·
      refine ⟨185122075982761127380361651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123414717321840751586907767 185122075982761127380361651)
      ·
        refine ⟨277683113974141691070542477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185122075982761127380361651 277683113974141691070542477)
        ·
          refine ⟨104131167740303134151453429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277683113974141691070542477 104131167740303134151453429)
          ·
            refine ⟨9762296975653418826698759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104131167740303134151453429 9762296975653418826698759)
            ·
              refine ⟨14643445463480128240048139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9762296975653418826698759 14643445463480128240048139)
              ·
                refine ⟨21965168195220192360072209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14643445463480128240048139 21965168195220192360072209)
                ·
                  refine ⟨16473876146415144270054157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21965168195220192360072209 16473876146415144270054157)
                  ·
                    refine ⟨6177703554905679101270309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16473876146415144270054157 6177703554905679101270309)
                    ·
                      refine ⟨1158319416544814831488183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6177703554905679101270309 1158319416544814831488183)
                      ·
                        rfl

theorem cell23_2255819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 4].length) (baseStart_2255819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255819 prefixEnd_2255819 := by exact prefixLift 2255819
  have htrace : WordTrace (prefixWord ++ tailWord_2255819) baseStart_2255819 baseEnd_2255819 := by
    simpa [prefixWord, tailWord_2255819, baseEnd_2255819] using wordTrace_append hprefix tailTrace_2255819
  have hstable : (prefixWord ++ tailWord_2255819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255819).length < 2 ^ (prefixWord ++ tailWord_2255819).sum := by decide
  have hdescent : baseEnd_2255819 < baseStart_2255819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255830 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2255830 : Nat := 118140960795 + 2255830 * 2 ^ 59
def prefixEnd_2255830 : Nat := 4983230072969 + 3 ^ 40 * 2255830 * 2
def baseEnd_2255830 : Nat := 1158325064832014288450633

theorem tailTrace_2255830 : CollatzResearch.WordTrace tailWord_2255830 prefixEnd_2255830 1158325064832014288450633 := by
  unfold tailWord_2255830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5142304963595040621036809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54851252945013766624392629 5142304963595040621036809)
  ·
    refine ⟨3856728722696280465777607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5142304963595040621036809 3856728722696280465777607)
    ·
      refine ⟨5785093084044420698666411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856728722696280465777607 5785093084044420698666411)
      ·
        refine ⟨8677639626066631047999617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5785093084044420698666411 8677639626066631047999617)
        ·
          refine ⟨6508229719549973285999713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8677639626066631047999617 6508229719549973285999713)
          ·
            refine ⟨4881172289662479964499785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6508229719549973285999713 4881172289662479964499785)
            ·
              refine ⟨3660879217246859973374839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4881172289662479964499785 3660879217246859973374839)
              ·
                refine ⟨5491318825870289960062259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660879217246859973374839 5491318825870289960062259)
                ·
                  refine ⟨8236978238805434940093389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491318825870289960062259 8236978238805434940093389)
                  ·
                    refine ⟨3088866839552038102535021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8236978238805434940093389 3088866839552038102535021)
                    ·
                      refine ⟨1158325064832014288450633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3088866839552038102535021 1158325064832014288450633)
                      ·
                        rfl

theorem cell23_2255830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2255830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255830 prefixEnd_2255830 := by exact prefixLift 2255830
  have htrace : WordTrace (prefixWord ++ tailWord_2255830) baseStart_2255830 baseEnd_2255830 := by
    simpa [prefixWord, tailWord_2255830, baseEnd_2255830] using wordTrace_append hprefix tailTrace_2255830
  have hstable : (prefixWord ++ tailWord_2255830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255830).length < 2 ^ (prefixWord ++ tailWord_2255830).sum := by decide
  have hdescent : baseEnd_2255830 < baseStart_2255830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255857 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 1, 3, 2]
def baseStart_2255857 : Nat := 118140960795 + 2255857 * 2 ^ 59
def prefixEnd_2255857 : Nat := 4983230072969 + 3 ^ 40 * 2255857 * 2
def baseEnd_2255857 : Nat := 1158338928809685682813009

theorem tailTrace_2255857 : CollatzResearch.WordTrace tailWord_2255857 prefixEnd_2255857 1158338928809685682813009 := by
  unfold tailWord_2255857
  simp only [CollatzResearch.WordTrace]
  refine ⟨82277864188422833547821825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54851909458948555698547883 82277864188422833547821825)
  ·
    refine ⟨61708398141317125160866369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82277864188422833547821825 61708398141317125160866369)
    ·
      refine ⟨46281298605987843870649777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61708398141317125160866369 46281298605987843870649777)
      ·
        refine ⟨34710973954490882902987333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46281298605987843870649777 34710973954490882902987333)
        ·
          refine ⟨6508307616467040544310125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34710973954490882902987333 6508307616467040544310125)
          ·
            refine ⟨2440615356175140204116297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6508307616467040544310125 2440615356175140204116297)
            ·
              refine ⟨1830461517131355153087223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2440615356175140204116297 1830461517131355153087223)
              ·
                refine ⟨2745692275697032729630835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830461517131355153087223 2745692275697032729630835)
                ·
                  refine ⟨4118538413545549094446253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745692275697032729630835 4118538413545549094446253)
                  ·
                    refine ⟨1544451905079580910417345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4118538413545549094446253 1544451905079580910417345)
                    ·
                      refine ⟨1158338928809685682813009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544451905079580910417345 1158338928809685682813009)
                      ·
                        rfl

theorem cell23_2255857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_2255857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255857 prefixEnd_2255857 := by exact prefixLift 2255857
  have htrace : WordTrace (prefixWord ++ tailWord_2255857) baseStart_2255857 baseEnd_2255857 := by
    simpa [prefixWord, tailWord_2255857, baseEnd_2255857] using wordTrace_append hprefix tailTrace_2255857
  have hstable : (prefixWord ++ tailWord_2255857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255857).length < 2 ^ (prefixWord ++ tailWord_2255857).sum := by decide
  have hdescent : baseEnd_2255857 < baseStart_2255857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255906 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2255906 : Nat := 118140960795 + 2255906 * 2 ^ 59
def prefixEnd_2255906 : Nat := 4983230072969 + 3 ^ 40 * 2255906 * 2
def baseEnd_2255906 : Nat := 386121363120585330366761

theorem tailTrace_2255906 : CollatzResearch.WordTrace tailWord_2255906 prefixEnd_2255906 386121363120585330366761 := by
  unfold tailWord_2255906
  simp only [CollatzResearch.WordTrace]
  refine ⟨20569912841311328729088893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54853100910163543277570381 20569912841311328729088893)
  ·
    refine ⟨7713717315491748273408335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20569912841311328729088893 7713717315491748273408335)
    ·
      refine ⟨11570575973237622410112503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7713717315491748273408335 11570575973237622410112503)
      ·
        refine ⟨17355863959856433615168755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11570575973237622410112503 17355863959856433615168755)
        ·
          refine ⟨26033795939784650422753133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17355863959856433615168755 26033795939784650422753133)
          ·
            refine ⟨9762673477419243908532425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26033795939784650422753133 9762673477419243908532425)
            ·
              refine ⟨7322005108064432931399319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9762673477419243908532425 7322005108064432931399319)
              ·
                refine ⟨10983007662096649397098979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322005108064432931399319 10983007662096649397098979)
                ·
                  refine ⟨16474511493144974095648469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10983007662096649397098979 16474511493144974095648469)
                  ·
                    refine ⟨386121363120585330366761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16474511493144974095648469 386121363120585330366761)
                    ·
                      rfl

theorem cell23_2255906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2255906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255906 prefixEnd_2255906 := by exact prefixLift 2255906
  have htrace : WordTrace (prefixWord ++ tailWord_2255906) baseStart_2255906 baseEnd_2255906 := by
    simpa [prefixWord, tailWord_2255906, baseEnd_2255906] using wordTrace_append hprefix tailTrace_2255906
  have hstable : (prefixWord ++ tailWord_2255906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255906).length < 2 ^ (prefixWord ++ tailWord_2255906).sum := by decide
  have hdescent : baseEnd_2255906 < baseStart_2255906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255946 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_2255946 : Nat := 118140960795 + 2255946 * 2 ^ 59
def prefixEnd_2255946 : Nat := 4983230072969 + 3 ^ 40 * 2255946 * 2
def baseEnd_2255946 : Nat := 1158384628587935834600099

theorem tailTrace_2255946 : CollatzResearch.WordTrace tailWord_2255946 prefixEnd_2255946 1158384628587935834600099 := by
  unfold tailWord_2255946
  simp only [CollatzResearch.WordTrace]
  refine ⟨20570277571275100436952923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54854073523400267831874461 20570277571275100436952923)
  ·
    refine ⟨30855416356912650655429385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20570277571275100436952923 30855416356912650655429385)
    ·
      refine ⟨23141562267684487991572039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30855416356912650655429385 23141562267684487991572039)
      ·
        refine ⟨34712343401526731987358059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23141562267684487991572039 34712343401526731987358059)
        ·
          refine ⟨52068515102290097981037089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34712343401526731987358059 52068515102290097981037089)
          ·
            refine ⟨39051386326717573485777817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52068515102290097981037089 39051386326717573485777817)
            ·
              refine ⟨29288539745038180114333363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39051386326717573485777817 29288539745038180114333363)
              ·
                refine ⟨43932809617557270171500045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29288539745038180114333363 43932809617557270171500045)
                ·
                  refine ⟨16474803606583976314312517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43932809617557270171500045 16474803606583976314312517)
                  ·
                    refine ⟨3089025676234495558933597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16474803606583976314312517 3089025676234495558933597)
                    ·
                      refine ⟨1158384628587935834600099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3089025676234495558933597 1158384628587935834600099)
                      ·
                        rfl

theorem cell23_2255946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_2255946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255946 prefixEnd_2255946 := by exact prefixLift 2255946
  have htrace : WordTrace (prefixWord ++ tailWord_2255946) baseStart_2255946 baseEnd_2255946 := by
    simpa [prefixWord, tailWord_2255946, baseEnd_2255946] using wordTrace_append hprefix tailTrace_2255946
  have hstable : (prefixWord ++ tailWord_2255946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255946).length < 2 ^ (prefixWord ++ tailWord_2255946).sum := by decide
  have hdescent : baseEnd_2255946 < baseStart_2255946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255956 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2255956 : Nat := 118140960795 + 2255956 * 2 ^ 59
def prefixEnd_2255956 : Nat := 4983230072969 + 3 ^ 40 * 2255956 * 2
def baseEnd_2255956 : Nat := 1158389763394480795475053

theorem tailTrace_2255956 : CollatzResearch.WordTrace tailWord_2255956 prefixEnd_2255956 1158389763394480795475053 := by
  unfold tailWord_2255956
  simp only [CollatzResearch.WordTrace]
  refine ⟨41140737507532086727837861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54854316676709448970450481 41140737507532086727837861)
  ·
    refine ⟨7713888282662266261469599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41140737507532086727837861 7713888282662266261469599)
    ·
      refine ⟨11570832423993399392204399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7713888282662266261469599 11570832423993399392204399)
      ·
        refine ⟨17356248635990099088306599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11570832423993399392204399 17356248635990099088306599)
        ·
          refine ⟨26034372953985148632459899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17356248635990099088306599 26034372953985148632459899)
          ·
            refine ⟨39051559430977722948689849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26034372953985148632459899 39051559430977722948689849)
            ·
              refine ⟨29288669573233292211517387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39051559430977722948689849 29288669573233292211517387)
              ·
                refine ⟨43933004359849938317276081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29288669573233292211517387 43933004359849938317276081)
                ·
                  refine ⟨32949753269887453737957061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43933004359849938317276081 32949753269887453737957061)
                  ·
                    refine ⟨6178078738103897575866949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32949753269887453737957061 6178078738103897575866949)
                    ·
                      refine ⟨1158389763394480795475053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6178078738103897575866949 1158389763394480795475053)
                      ·
                        rfl

theorem cell23_2255956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2255956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255956 prefixEnd_2255956 := by exact prefixLift 2255956
  have htrace : WordTrace (prefixWord ++ tailWord_2255956) baseStart_2255956 baseEnd_2255956 := by
    simpa [prefixWord, tailWord_2255956, baseEnd_2255956] using wordTrace_append hprefix tailTrace_2255956
  have hstable : (prefixWord ++ tailWord_2255956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255956).length < 2 ^ (prefixWord ++ tailWord_2255956).sum := by decide
  have hdescent : baseEnd_2255956 < baseStart_2255956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255986 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2255986 : Nat := 118140960795 + 2255986 * 2 ^ 59
def prefixEnd_2255986 : Nat := 4983230072969 + 3 ^ 40 * 2255986 * 2
def baseEnd_2255986 : Nat := 1158405167814115678099915

theorem tailTrace_2255986 : CollatzResearch.WordTrace tailWord_2255986 prefixEnd_2255986 1158405167814115678099915 := by
  unfold tailWord_2255986
  simp only [CollatzResearch.WordTrace]
  refine ⟨20570642301238872144816953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54855046136636992386178541 20570642301238872144816953)
  ·
    refine ⟨15427981725929154108612715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20570642301238872144816953 15427981725929154108612715)
    ·
      refine ⟨23141972588893731162919073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15427981725929154108612715 23141972588893731162919073)
      ·
        refine ⟨17356479441670298372189305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23141972588893731162919073 17356479441670298372189305)
        ·
          refine ⟨13017359581252723779141979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17356479441670298372189305 13017359581252723779141979)
          ·
            refine ⟨19526039371879085668712969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13017359581252723779141979 19526039371879085668712969)
            ·
              refine ⟨14644529528909314251534727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19526039371879085668712969 14644529528909314251534727)
              ·
                refine ⟨21966794293363971377302091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14644529528909314251534727 21966794293363971377302091)
                ·
                  refine ⟨32950191440045957065953137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21966794293363971377302091 32950191440045957065953137)
                  ·
                    refine ⟨24712643580034467799464853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32950191440045957065953137 24712643580034467799464853)
                    ·
                      refine ⟨1158405167814115678099915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24712643580034467799464853 1158405167814115678099915)
                      ·
                        rfl

theorem cell23_2255986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2255986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255986 prefixEnd_2255986 := by exact prefixLift 2255986
  have htrace : WordTrace (prefixWord ++ tailWord_2255986) baseStart_2255986 baseEnd_2255986 := by
    simpa [prefixWord, tailWord_2255986, baseEnd_2255986] using wordTrace_append hprefix tailTrace_2255986
  have hstable : (prefixWord ++ tailWord_2255986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255986).length < 2 ^ (prefixWord ++ tailWord_2255986).sum := by decide
  have hdescent : baseEnd_2255986 < baseStart_2255986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255996 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_2255996 : Nat := 118140960795 + 2255996 * 2 ^ 59
def prefixEnd_2255996 : Nat := 4983230072969 + 3 ^ 40 * 2255996 * 2
def baseEnd_2255996 : Nat := 386136767540220212991623

theorem tailTrace_2255996 : CollatzResearch.WordTrace tailWord_2255996 prefixEnd_2255996 386136767540220212991623 := by
  unfold tailWord_2255996
  simp only [CollatzResearch.WordTrace]
  refine ⟨41141466967459630143565921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54855289289946173524754561 41141466967459630143565921)
  ·
    refine ⟨30856100225594722607674441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41141466967459630143565921 30856100225594722607674441)
    ·
      refine ⟨23142075169196041955755831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30856100225594722607674441 23142075169196041955755831)
      ·
        refine ⟨34713112753794062933633747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23142075169196041955755831 34713112753794062933633747)
        ·
          refine ⟨52069669130691094400450621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34713112753794062933633747 52069669130691094400450621)
          ·
            refine ⟨19526125924009160400168983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52069669130691094400450621 19526125924009160400168983)
            ·
              refine ⟨29289188886013740600253475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19526125924009160400168983 29289188886013740600253475)
              ·
                refine ⟨43933783329020610900380213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29289188886013740600253475 43933783329020610900380213)
                ·
                  refine ⟨4118792187095682271910645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43933783329020610900380213 4118792187095682271910645)
                  ·
                    refine ⟨386136767540220212991623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4118792187095682271910645 386136767540220212991623)
                    ·
                      rfl

theorem cell23_2255996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_2255996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2255996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2255996 prefixEnd_2255996 := by exact prefixLift 2255996
  have htrace : WordTrace (prefixWord ++ tailWord_2255996) baseStart_2255996 baseEnd_2255996 := by
    simpa [prefixWord, tailWord_2255996, baseEnd_2255996] using wordTrace_append hprefix tailTrace_2255996
  have hstable : (prefixWord ++ tailWord_2255996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255996).length < 2 ^ (prefixWord ++ tailWord_2255996).sum := by decide
  have hdescent : baseEnd_2255996 < baseStart_2255996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256003 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 1, 5, 2]
def baseStart_2256003 : Nat := 118140960795 + 2256003 * 2 ^ 59
def prefixEnd_2256003 : Nat := 4983230072969 + 3 ^ 40 * 2256003 * 2
def baseEnd_2256003 : Nat := 1158413896985242111587337

theorem tailTrace_2256003 : CollatzResearch.WordTrace tailWord_2256003 prefixEnd_2256003 1158413896985242111587337 := by
  unfold tailWord_2256003
  simp only [CollatzResearch.WordTrace]
  refine ⟨82283189245893900482636663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54855459497262600321757775 82283189245893900482636663)
  ·
    refine ⟨123424783868840850723954995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82283189245893900482636663 123424783868840850723954995)
    ·
      refine ⟨185137175803261276085932493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123424783868840850723954995 185137175803261276085932493)
      ·
        refine ⟨69426440926222978532224685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185137175803261276085932493 69426440926222978532224685)
        ·
          refine ⟨26034915347333616949584257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69426440926222978532224685 26034915347333616949584257)
          ·
            refine ⟨19526186510500212712188193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26034915347333616949584257 19526186510500212712188193)
            ·
              refine ⟨14644639882875159534141145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19526186510500212712188193 14644639882875159534141145)
              ·
                refine ⟨10983479912156369650605859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14644639882875159534141145 10983479912156369650605859)
                ·
                  refine ⟨16475219868234554475908789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10983479912156369650605859 16475219868234554475908789)
                  ·
                    refine ⟨1544551862646989482116449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16475219868234554475908789 1544551862646989482116449)
                    ·
                      refine ⟨1158413896985242111587337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544551862646989482116449 1158413896985242111587337)
                      ·
                        rfl

theorem cell23_2256003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_2256003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256003 prefixEnd_2256003 := by exact prefixLift 2256003
  have htrace : WordTrace (prefixWord ++ tailWord_2256003) baseStart_2256003 baseEnd_2256003 := by
    simpa [prefixWord, tailWord_2256003, baseEnd_2256003] using wordTrace_append hprefix tailTrace_2256003
  have hstable : (prefixWord ++ tailWord_2256003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256003).length < 2 ^ (prefixWord ++ tailWord_2256003).sum := by decide
  have hdescent : baseEnd_2256003 < baseStart_2256003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256010 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2256010 : Nat := 118140960795 + 2256010 * 2 ^ 59
def prefixEnd_2256010 : Nat := 4983230072969 + 3 ^ 40 * 2256010 * 2
def baseEnd_2256010 : Nat := 1158417491349823584199805

theorem tailTrace_2256010 : CollatzResearch.WordTrace tailWord_2256010 prefixEnd_2256010 1158417491349823584199805 := by
  unfold tailWord_2256010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20570861139217135169535371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54855629704579027118760989 20570861139217135169535371)
  ·
    refine ⟨30856291708825702754303057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20570861139217135169535371 30856291708825702754303057)
    ·
      refine ⟨23142218781619277065727293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30856291708825702754303057 23142218781619277065727293)
      ·
        refine ⟨8678332043107228899647735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23142218781619277065727293 8678332043107228899647735)
        ·
          refine ⟨13017498064660843349471603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8678332043107228899647735 13017498064660843349471603)
          ·
            refine ⟨19526247096991265024207405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13017498064660843349471603 19526247096991265024207405)
            ·
              refine ⟨7322342661371724384077777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19526247096991265024207405 7322342661371724384077777)
              ·
                refine ⟨5491756996028793288058333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7322342661371724384077777 5491756996028793288058333)
                ·
                  refine ⟨2059408873510797483021875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5491756996028793288058333 2059408873510797483021875)
                  ·
                    refine ⟨3089113310266196224532813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2059408873510797483021875 3089113310266196224532813)
                    ·
                      refine ⟨1158417491349823584199805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3089113310266196224532813 1158417491349823584199805)
                      ·
                        rfl

theorem cell23_2256010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2256010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256010 prefixEnd_2256010 := by exact prefixLift 2256010
  have htrace : WordTrace (prefixWord ++ tailWord_2256010) baseStart_2256010 baseEnd_2256010 := by
    simpa [prefixWord, tailWord_2256010, baseEnd_2256010] using wordTrace_append hprefix tailTrace_2256010
  have hstable : (prefixWord ++ tailWord_2256010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256010).length < 2 ^ (prefixWord ++ tailWord_2256010).sum := by decide
  have hdescent : baseEnd_2256010 < baseStart_2256010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256060 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_2256060 : Nat := 118140960795 + 2256060 * 2 ^ 59
def prefixEnd_2256060 : Nat := 4983230072969 + 3 ^ 40 * 2256060 * 2
def baseEnd_2256060 : Nat := 386147721794182796191525

theorem tailTrace_2256060 : CollatzResearch.WordTrace tailWord_2256060 prefixEnd_2256060 386147721794182796191525 := by
  unfold tailWord_2256060
  simp only [CollatzResearch.WordTrace]
  refine ⟨41142634103343699608730817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54856845471124932811641089 41142634103343699608730817)
  ·
    refine ⟨30856975577507774706548113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41142634103343699608730817 30856975577507774706548113)
    ·
      refine ⟨23142731683130831029911085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30856975577507774706548113 23142731683130831029911085)
      ·
        refine ⟨8678524381174061636216657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23142731683130831029911085 8678524381174061636216657)
        ·
          refine ⟨6508893285880546227162493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8678524381174061636216657 6508893285880546227162493)
          ·
            refine ⟨2440834982205204835185935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6508893285880546227162493 2440834982205204835185935)
            ·
              refine ⟨3661252473307807252778903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440834982205204835185935 3661252473307807252778903)
              ·
                refine ⟨5491878709961710879168355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3661252473307807252778903 5491878709961710879168355)
                ·
                  refine ⟨8237818064942566318752533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491878709961710879168355 8237818064942566318752533)
                  ·
                    refine ⟨386147721794182796191525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8237818064942566318752533 386147721794182796191525)
                    ·
                      rfl

theorem cell23_2256060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_2256060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256060 prefixEnd_2256060 := by exact prefixLift 2256060
  have htrace : WordTrace (prefixWord ++ tailWord_2256060) baseStart_2256060 baseEnd_2256060 := by
    simpa [prefixWord, tailWord_2256060, baseEnd_2256060] using wordTrace_append hprefix tailTrace_2256060
  have hstable : (prefixWord ++ tailWord_2256060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256060).length < 2 ^ (prefixWord ++ tailWord_2256060).sum := by decide
  have hdescent : baseEnd_2256060 < baseStart_2256060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256063 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 4]
def baseStart_2256063 : Nat := 118140960795 + 2256063 * 2 ^ 59
def prefixEnd_2256063 : Nat := 4983230072969 + 3 ^ 40 * 2256063 * 2
def baseEnd_2256063 : Nat := 1158444705824511876837061

theorem tailTrace_2256063 : CollatzResearch.WordTrace tailWord_2256063 prefixEnd_2256063 1158444705824511876837061 := by
  unfold tailWord_2256063
  simp only [CollatzResearch.WordTrace]
  refine ⟨82285377625676530729820843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54856918417117687153213895 82285377625676530729820843)
  ·
    refine ⟨123428066438514796094731265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82285377625676530729820843 123428066438514796094731265)
    ·
      refine ⟨92571049828886097071048449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123428066438514796094731265 92571049828886097071048449)
      ·
        refine ⟨69428287371664572803286337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92571049828886097071048449 69428287371664572803286337)
        ·
          refine ⟨52071215528748429602464753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69428287371664572803286337 52071215528748429602464753)
          ·
            refine ⟨39053411646561322201848565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52071215528748429602464753 39053411646561322201848565)
            ·
              refine ⟨3661257341865123956423303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39053411646561322201848565 3661257341865123956423303)
              ·
                refine ⟨5491886012797685934634955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3661257341865123956423303 5491886012797685934634955)
                ·
                  refine ⟨8237829019196528901952433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491886012797685934634955 8237829019196528901952433)
                  ·
                    refine ⟨6178371764397396676464325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8237829019196528901952433 6178371764397396676464325)
                    ·
                      refine ⟨1158444705824511876837061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6178371764397396676464325 1158444705824511876837061)
                      ·
                        rfl

theorem cell23_2256063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_2256063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256063 prefixEnd_2256063 := by exact prefixLift 2256063
  have htrace : WordTrace (prefixWord ++ tailWord_2256063) baseStart_2256063 baseEnd_2256063 := by
    simpa [prefixWord, tailWord_2256063, baseEnd_2256063] using wordTrace_append hprefix tailTrace_2256063
  have hstable : (prefixWord ++ tailWord_2256063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256063).length < 2 ^ (prefixWord ++ tailWord_2256063).sum := by decide
  have hdescent : baseEnd_2256063 < baseStart_2256063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256100 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_2256100 : Nat := 118140960795 + 2256100 * 2 ^ 59
def prefixEnd_2256100 : Nat := 4983230072969 + 3 ^ 40 * 2256100 * 2
def baseEnd_2256100 : Nat := 1158463704608728232074391

theorem tailTrace_2256100 : CollatzResearch.WordTrace tailWord_2256100 prefixEnd_2256100 1158463704608728232074391 := by
  unfold tailWord_2256100
  simp only [CollatzResearch.WordTrace]
  refine ⟨41143363563271243024458877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54857818084361657365945169 41143363563271243024458877)
  ·
    refine ⟨15428761336226716134172079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41143363563271243024458877 15428761336226716134172079)
    ·
      refine ⟨23143142004340074201258119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15428761336226716134172079 23143142004340074201258119)
      ·
        refine ⟨34714713006510111301887179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23143142004340074201258119 34714713006510111301887179)
        ·
          refine ⟨52072069509765166952830769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34714713006510111301887179 52072069509765166952830769)
          ·
            refine ⟨39054052132323875214623077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52072069509765166952830769 39054052132323875214623077)
            ·
              refine ⟨7322634774810726602741827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39054052132323875214623077 7322634774810726602741827)
              ·
                refine ⟨10983952162216089904112741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322634774810726602741827 10983952162216089904112741)
                ·
                  refine ⟨2059491030415516857021139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10983952162216089904112741 2059491030415516857021139)
                  ·
                    refine ⟨3089236545623275285531709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2059491030415516857021139 3089236545623275285531709)
                    ·
                      refine ⟨1158463704608728232074391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3089236545623275285531709 1158463704608728232074391)
                      ·
                        rfl

theorem cell23_2256100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_2256100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256100 prefixEnd_2256100 := by exact prefixLift 2256100
  have htrace : WordTrace (prefixWord ++ tailWord_2256100) baseStart_2256100 baseEnd_2256100 := by
    simpa [prefixWord, tailWord_2256100, baseEnd_2256100] using wordTrace_append hprefix tailTrace_2256100
  have hstable : (prefixWord ++ tailWord_2256100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256100).length < 2 ^ (prefixWord ++ tailWord_2256100).sum := by decide
  have hdescent : baseEnd_2256100 < baseStart_2256100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256101 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 3, 2, 2]
def baseStart_2256101 : Nat := 118140960795 + 2256101 * 2 ^ 59
def prefixEnd_2256101 : Nat := 4983230072969 + 3 ^ 40 * 2256101 * 2
def baseEnd_2256101 : Nat := 1158464218089382728161887

theorem tailTrace_2256101 : CollatzResearch.WordTrace tailWord_2256101 prefixEnd_2256101 1158464218089382728161887 := by
  unfold tailWord_2256101
  simp only [CollatzResearch.WordTrace]
  refine ⟨82286763599538863219704157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54857842399692575479802771 82286763599538863219704157)
  ·
    refine ⟨30857536349827073707389059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82286763599538863219704157 30857536349827073707389059)
    ·
      refine ⟨46286304524740610561083589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30857536349827073707389059 46286304524740610561083589)
      ·
        refine ⟨8678682098388864480203173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46286304524740610561083589 8678682098388864480203173)
        ·
          refine ⟨1627252893447912090038095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8678682098388864480203173 1627252893447912090038095)
          ·
            refine ⟨2440879340171868135057143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627252893447912090038095 2440879340171868135057143)
            ·
              refine ⟨3661319010257802202585715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440879340171868135057143 3661319010257802202585715)
              ·
                refine ⟨5491978515386703303878573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3661319010257802202585715 5491978515386703303878573)
                ·
                  refine ⟨2059491943270013738954465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5491978515386703303878573 2059491943270013738954465)
                  ·
                    refine ⟨1544618957452510304215849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2059491943270013738954465 1544618957452510304215849)
                    ·
                      refine ⟨1158464218089382728161887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544618957452510304215849 1158464218089382728161887)
                      ·
                        rfl

theorem cell23_2256101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_2256101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256101 prefixEnd_2256101 := by exact prefixLift 2256101
  have htrace : WordTrace (prefixWord ++ tailWord_2256101) baseStart_2256101 baseEnd_2256101 := by
    simpa [prefixWord, tailWord_2256101, baseEnd_2256101] using wordTrace_append hprefix tailTrace_2256101
  have hstable : (prefixWord ++ tailWord_2256101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256101).length < 2 ^ (prefixWord ++ tailWord_2256101).sum := by decide
  have hdescent : baseEnd_2256101 < baseStart_2256101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256127 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 1, 3, 2]
def baseStart_2256127 : Nat := 118140960795 + 2256127 * 2 ^ 59
def prefixEnd_2256127 : Nat := 4983230072969 + 3 ^ 40 * 2256127 * 2
def baseEnd_2256127 : Nat := 1158477568586399626436767

theorem tailTrace_2256127 : CollatzResearch.WordTrace tailWord_2256127 prefixEnd_2256127 1158477568586399626436767 := by
  unfold tailWord_2256127
  simp only [CollatzResearch.WordTrace]
  refine ⟨82287711897444669660150635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54858474598296446440100423 82287711897444669660150635)
  ·
    refine ⟨123431567846167004490225953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82287711897444669660150635 123431567846167004490225953)
    ·
      refine ⟨92573675884625253367669465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123431567846167004490225953 92573675884625253367669465)
      ·
        refine ⟨69430256913468940025752099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92573675884625253367669465 69430256913468940025752099)
        ·
          refine ⟨104145385370203410038628149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69430256913468940025752099 104145385370203410038628149)
          ·
            refine ⟨9763629878456569691121389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104145385370203410038628149 9763629878456569691121389)
            ·
              refine ⟨3661361204421213634170521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9763629878456569691121389 3661361204421213634170521)
              ·
                refine ⟨2746020903315910225627891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3661361204421213634170521 2746020903315910225627891)
                ·
                  refine ⟨4119031354973865338441837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2746020903315910225627891 4119031354973865338441837)
                  ·
                    refine ⟨1544636758115199501915689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4119031354973865338441837 1544636758115199501915689)
                    ·
                      refine ⟨1158477568586399626436767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544636758115199501915689 1158477568586399626436767)
                      ·
                        rfl

theorem cell23_2256127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_2256127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256127 prefixEnd_2256127 := by exact prefixLift 2256127
  have htrace : WordTrace (prefixWord ++ tailWord_2256127) baseStart_2256127 baseEnd_2256127 := by
    simpa [prefixWord, tailWord_2256127, baseEnd_2256127] using wordTrace_append hprefix tailTrace_2256127
  have hstable : (prefixWord ++ tailWord_2256127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256127).length < 2 ^ (prefixWord ++ tailWord_2256127).sum := by decide
  have hdescent : baseEnd_2256127 < baseStart_2256127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256140 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 3, 4, 2]
def baseStart_2256140 : Nat := 118140960795 + 2256140 * 2 ^ 59
def prefixEnd_2256140 : Nat := 4983230072969 + 3 ^ 40 * 2256140 * 2
def baseEnd_2256140 : Nat := 1158484243834908075574207

theorem tailTrace_2256140 : CollatzResearch.WordTrace tailWord_2256140 prefixEnd_2256140 1158484243834908075574207 := by
  unfold tailWord_2256140
  simp only [CollatzResearch.WordTrace]
  refine ⟨41144093023198786440186937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54858790697598381920249249 41144093023198786440186937)
  ·
    refine ⟨30858069767399089830140203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41144093023198786440186937 30858069767399089830140203)
    ·
      refine ⟨46287104651098634745210305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30858069767399089830140203 46287104651098634745210305)
      ·
        refine ⟨34715328488323976058907729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46287104651098634745210305 34715328488323976058907729)
        ·
          refine ⟨26036496366242982044180797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34715328488323976058907729 26036496366242982044180797)
          ·
            refine ⟨9763686137341118266567799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26036496366242982044180797 9763686137341118266567799)
            ·
              refine ⟨14645529206011677399851699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9763686137341118266567799 14645529206011677399851699)
              ·
                refine ⟨21968293809017516099777549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14645529206011677399851699 21968293809017516099777549)
                ·
                  refine ⟨8238110178381568537416581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21968293809017516099777549 8238110178381568537416581)
                  ·
                    refine ⟨1544645658446544100765609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8238110178381568537416581 1544645658446544100765609)
                    ·
                      refine ⟨1158484243834908075574207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544645658446544100765609 1158484243834908075574207)
                      ·
                        rfl

theorem cell23_2256140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_2256140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256140 prefixEnd_2256140 := by exact prefixLift 2256140
  have htrace : WordTrace (prefixWord ++ tailWord_2256140) baseStart_2256140 baseEnd_2256140 := by
    simpa [prefixWord, tailWord_2256140, baseEnd_2256140] using wordTrace_append hprefix tailTrace_2256140
  have hstable : (prefixWord ++ tailWord_2256140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256140).length < 2 ^ (prefixWord ++ tailWord_2256140).sum := by decide
  have hdescent : baseEnd_2256140 < baseStart_2256140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256170 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2256170 : Nat := 118140960795 + 2256170 * 2 ^ 59
def prefixEnd_2256170 : Nat := 4983230072969 + 3 ^ 40 * 2256170 * 2
def baseEnd_2256170 : Nat := 1158499648254542958199069

theorem tailTrace_2256170 : CollatzResearch.WordTrace tailWord_2256170 prefixEnd_2256170 1158499648254542958199069 := by
  unfold tailWord_2256170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20572320059072222000991491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54859520157525925335977309 20572320059072222000991491)
  ·
    refine ⟨30858480088608333001487237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20572320059072222000991491 30858480088608333001487237)
    ·
      refine ⟨5785965016614062437778857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30858480088608333001487237 5785965016614062437778857)
      ·
        refine ⟨4339473762460546828334143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5785965016614062437778857 4339473762460546828334143)
        ·
          refine ⟨6509210643690820242501215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339473762460546828334143 6509210643690820242501215)
          ·
            refine ⟨9763815965536230363751823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509210643690820242501215 9763815965536230363751823)
            ·
              refine ⟨14645723948304345545627735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9763815965536230363751823 14645723948304345545627735)
              ·
                refine ⟨21968585922456518318441603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14645723948304345545627735 21968585922456518318441603)
                ·
                  refine ⟨32952878883684777477662405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21968585922456518318441603 32952878883684777477662405)
                  ·
                    refine ⟨6178664790690895777061701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32952878883684777477662405 6178664790690895777061701)
                    ·
                      refine ⟨1158499648254542958199069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6178664790690895777061701 1158499648254542958199069)
                      ·
                        rfl

theorem cell23_2256170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2256170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256170 prefixEnd_2256170 := by exact prefixLift 2256170
  have htrace : WordTrace (prefixWord ++ tailWord_2256170) baseStart_2256170 baseEnd_2256170 := by
    simpa [prefixWord, tailWord_2256170, baseEnd_2256170] using wordTrace_append hprefix tailTrace_2256170
  have hstable : (prefixWord ++ tailWord_2256170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256170).length < 2 ^ (prefixWord ++ tailWord_2256170).sum := by decide
  have hdescent : baseEnd_2256170 < baseStart_2256170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256180 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 7]
def baseStart_2256180 : Nat := 118140960795 + 2256180 * 2 ^ 59
def prefixEnd_2256180 : Nat := 4983230072969 + 3 ^ 40 * 2256180 * 2
def baseEnd_2256180 : Nat := 128722753673454213230447

theorem tailTrace_2256180 : CollatzResearch.WordTrace tailWord_2256180 prefixEnd_2256180 128722753673454213230447 := by
  unfold tailWord_2256180
  simp only [CollatzResearch.WordTrace]
  refine ⟨41144822483126329855914997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54859763310835106474553329 41144822483126329855914997)
  ·
    refine ⟨3857327107793093423992031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41144822483126329855914997 3857327107793093423992031)
    ·
      refine ⟨5785990661689640135988047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3857327107793093423992031 5785990661689640135988047)
      ·
        refine ⟨8678985992534460203982071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5785990661689640135988047 8678985992534460203982071)
        ·
          refine ⟨13018478988801690305973107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8678985992534460203982071 13018478988801690305973107)
          ·
            refine ⟨19527718483202535458959661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13018478988801690305973107 19527718483202535458959661)
            ·
              refine ⟨7322894431200950797109873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19527718483202535458959661 7322894431200950797109873)
              ·
                refine ⟨5492170823400713097832405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7322894431200950797109873 5492170823400713097832405)
                ·
                  refine ⟨128722753673454213230447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5492170823400713097832405 128722753673454213230447)
                  ·
                    rfl

theorem cell23_2256180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_2256180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256180 prefixEnd_2256180 := by exact prefixLift 2256180
  have htrace : WordTrace (prefixWord ++ tailWord_2256180) baseStart_2256180 baseEnd_2256180 := by
    simpa [prefixWord, tailWord_2256180, baseEnd_2256180] using wordTrace_append hprefix tailTrace_2256180
  have hstable : (prefixWord ++ tailWord_2256180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256180).length < 2 ^ (prefixWord ++ tailWord_2256180).sum := by decide
  have hdescent : baseEnd_2256180 < baseStart_2256180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256190 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2256190 : Nat := 118140960795 + 2256190 * 2 ^ 59
def prefixEnd_2256190 : Nat := 4983230072969 + 3 ^ 40 * 2256190 * 2
def baseEnd_2256190 : Nat := 1158509917867632879948977

theorem tailTrace_2256190 : CollatzResearch.WordTrace tailWord_2256190 prefixEnd_2256190 1158509917867632879948977 := by
  unfold tailWord_2256190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10286251212027053927461753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54860006464144287613129349 10286251212027053927461753)
  ·
    refine ⟨7714688409020290445596315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10286251212027053927461753 7714688409020290445596315)
    ·
      refine ⟨11572032613530435668394473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7714688409020290445596315 11572032613530435668394473)
      ·
        refine ⟨8679024460147826751295855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11572032613530435668394473 8679024460147826751295855)
        ·
          refine ⟨13018536690221740126943783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8679024460147826751295855 13018536690221740126943783)
          ·
            refine ⟨19527805035332610190415675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13018536690221740126943783 19527805035332610190415675)
            ·
              refine ⟨29291707552998915285623513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19527805035332610190415675 29291707552998915285623513)
              ·
                refine ⟨21968780664749186464217635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29291707552998915285623513 21968780664749186464217635)
                ·
                  refine ⟨32953170997123779696326453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21968780664749186464217635 32953170997123779696326453)
                  ·
                    refine ⟨3089359780980354346530605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32953170997123779696326453 3089359780980354346530605)
                    ·
                      refine ⟨1158509917867632879948977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3089359780980354346530605 1158509917867632879948977)
                      ·
                        rfl

theorem cell23_2256190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2256190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256190 prefixEnd_2256190 := by exact prefixLift 2256190
  have htrace : WordTrace (prefixWord ++ tailWord_2256190) baseStart_2256190 baseEnd_2256190 := by
    simpa [prefixWord, tailWord_2256190, baseEnd_2256190] using wordTrace_append hprefix tailTrace_2256190
  have hstable : (prefixWord ++ tailWord_2256190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256190).length < 2 ^ (prefixWord ++ tailWord_2256190).sum := by decide
  have hdescent : baseEnd_2256190 < baseStart_2256190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256240 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 3, 4]
def baseStart_2256240 : Nat := 118140960795 + 2256240 * 2 ^ 59
def prefixEnd_2256240 : Nat := 4983230072969 + 3 ^ 40 * 2256240 * 2
def baseEnd_2256240 : Nat := 386178530633452561441249

theorem tailTrace_2256240 : CollatzResearch.WordTrace tailWord_2256240 prefixEnd_2256240 386178530633452561441249 := by
  unfold tailWord_2256240
  simp only [CollatzResearch.WordTrace]
  refine ⟨41145916673017644979507087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54861222230690193306009449 41145916673017644979507087)
  ·
    refine ⟨61718875009526467469260631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41145916673017644979507087 61718875009526467469260631)
    ·
      refine ⟨92578312514289701203890947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61718875009526467469260631 92578312514289701203890947)
      ·
        refine ⟨138867468771434551805836421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92578312514289701203890947 138867468771434551805836421)
        ·
          refine ⟨26037650394643978463594329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138867468771434551805836421 26037650394643978463594329)
          ·
            refine ⟨19528237795982983847695747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26037650394643978463594329 19528237795982983847695747)
            ·
              refine ⟨29292356693974475771543621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19528237795982983847695747 29292356693974475771543621)
              ·
                refine ⟨5492316880120214207164429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29292356693974475771543621 5492316880120214207164429)
                ·
                  refine ⟨2059618830045080327686661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5492316880120214207164429 2059618830045080327686661)
                  ·
                    refine ⟨386178530633452561441249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2059618830045080327686661 386178530633452561441249)
                    ·
                      rfl

theorem cell23_2256240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 4].length) (baseStart_2256240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256240 prefixEnd_2256240 := by exact prefixLift 2256240
  have htrace : WordTrace (prefixWord ++ tailWord_2256240) baseStart_2256240 baseEnd_2256240 := by
    simpa [prefixWord, tailWord_2256240, baseEnd_2256240] using wordTrace_append hprefix tailTrace_2256240
  have hstable : (prefixWord ++ tailWord_2256240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256240).length < 2 ^ (prefixWord ++ tailWord_2256240).sum := by decide
  have hdescent : baseEnd_2256240 < baseStart_2256240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256253 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 10]
def baseStart_2256253 : Nat := 118140960795 + 2256253 * 2 ^ 59
def prefixEnd_2256253 : Nat := 4983230072969 + 3 ^ 40 * 2256253 * 2
def baseEnd_2256253 : Nat := 128726918572096237051243

theorem tailTrace_2256253 : CollatzResearch.WordTrace tailWord_2256253 prefixEnd_2256253 128726918572096237051243 := by
  unfold tailWord_2256253
  simp only [CollatzResearch.WordTrace]
  refine ⟨82292307494988193179237413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54861538329992128786158275 82292307494988193179237413)
  ·
    refine ⟨15429807655310286221107015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82292307494988193179237413 15429807655310286221107015)
    ·
      refine ⟨23144711482965429331660523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15429807655310286221107015 23144711482965429331660523)
      ·
        refine ⟨34717067224448143997490785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23144711482965429331660523 34717067224448143997490785)
        ·
          refine ⟨26037800418336107998118089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34717067224448143997490785 26037800418336107998118089)
          ·
            refine ⟨19528350313752080998588567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26037800418336107998118089 19528350313752080998588567)
            ·
              refine ⟨29292525470628121497882851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19528350313752080998588567 29292525470628121497882851)
              ·
                refine ⟨43938788205942182246824277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29292525470628121497882851 43938788205942182246824277)
                ·
                  refine ⟨128726918572096237051243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43938788205942182246824277 128726918572096237051243)
                  ·
                    rfl

theorem cell23_2256253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_2256253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256253 prefixEnd_2256253 := by exact prefixLift 2256253
  have htrace : WordTrace (prefixWord ++ tailWord_2256253) baseStart_2256253 baseEnd_2256253 := by
    simpa [prefixWord, tailWord_2256253, baseEnd_2256253] using wordTrace_append hprefix tailTrace_2256253
  have hstable : (prefixWord ++ tailWord_2256253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256253).length < 2 ^ (prefixWord ++ tailWord_2256253).sum := by decide
  have hdescent : baseEnd_2256253 < baseStart_2256253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256287 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 6]
def baseStart_2256287 : Nat := 118140960795 + 2256287 * 2 ^ 59
def prefixEnd_2256287 : Nat := 4983230072969 + 3 ^ 40 * 2256287 * 2
def baseEnd_2256287 : Nat := 128728858387902111159559

theorem tailTrace_2256287 : CollatzResearch.WordTrace tailWord_2256287 prefixEnd_2256287 128728858387902111159559 := by
  unfold tailWord_2256287
  simp only [CollatzResearch.WordTrace]
  refine ⟨82293547576865016985975115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54862365051243344657316743 82293547576865016985975115)
  ·
    refine ⟨123440321365297525478962673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82293547576865016985975115 123440321365297525478962673)
    ·
      refine ⟨92580241023973144109222005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123440321365297525478962673 92580241023973144109222005)
      ·
        refine ⟨8679397595997482260239563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92580241023973144109222005 8679397595997482260239563)
        ·
          refine ⟨13019096393996223390359345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8679397595997482260239563 13019096393996223390359345)
          ·
            refine ⟨9764322295497167542769509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13019096393996223390359345 9764322295497167542769509)
            ·
              refine ⟨1830810430405718914269283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9764322295497167542769509 1830810430405718914269283)
              ·
                refine ⟨2746215645608578371403925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830810430405718914269283 2746215645608578371403925)
                ·
                  refine ⟨128728858387902111159559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2746215645608578371403925 128728858387902111159559)
                  ·
                    rfl

theorem cell23_2256287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 6].length) (baseStart_2256287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256287 prefixEnd_2256287 := by exact prefixLift 2256287
  have htrace : WordTrace (prefixWord ++ tailWord_2256287) baseStart_2256287 baseEnd_2256287 := by
    simpa [prefixWord, tailWord_2256287, baseEnd_2256287] using wordTrace_append hprefix tailTrace_2256287
  have hstable : (prefixWord ++ tailWord_2256287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256287).length < 2 ^ (prefixWord ++ tailWord_2256287).sum := by decide
  have hdescent : baseEnd_2256287 < baseStart_2256287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256293 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_2256293 : Nat := 118140960795 + 2256293 * 2 ^ 59
def prefixEnd_2256293 : Nat := 4983230072969 + 3 ^ 40 * 2256293 * 2
def baseEnd_2256293 : Nat := 1158562806375045976961003

theorem tailTrace_2256293 : CollatzResearch.WordTrace tailWord_2256293 prefixEnd_2256293 1158562806375045976961003 := by
  unfold tailWord_2256293
  simp only [CollatzResearch.WordTrace]
  refine ⟨82293766414843280010693533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54862510943228853340462355 82293766414843280010693533)
  ·
    refine ⟨30860162405566230004010075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82293766414843280010693533 30860162405566230004010075)
    ·
      refine ⟨46290243608349345006015113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30860162405566230004010075 46290243608349345006015113)
      ·
        refine ⟨34717682706262008754511335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46290243608349345006015113 34717682706262008754511335)
        ·
          refine ⟨52076524059393013131767003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34717682706262008754511335 52076524059393013131767003)
          ·
            refine ⟨78114786089089519697650505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52076524059393013131767003 78114786089089519697650505)
            ·
              refine ⟨58586089566817139773237879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78114786089089519697650505 58586089566817139773237879)
              ·
                refine ⟨87879134350225709659856819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58586089566817139773237879 87879134350225709659856819)
                ·
                  refine ⟨131818701525338564489785229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87879134350225709659856819 131818701525338564489785229)
                  ·
                    refine ⟨49432013072001961683669461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131818701525338564489785229 49432013072001961683669461)
                    ·
                      refine ⟨1158562806375045976961003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49432013072001961683669461 1158562806375045976961003)
                      ·
                        rfl

theorem cell23_2256293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_2256293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256293 prefixEnd_2256293 := by exact prefixLift 2256293
  have htrace : WordTrace (prefixWord ++ tailWord_2256293) baseStart_2256293 baseEnd_2256293 := by
    simpa [prefixWord, tailWord_2256293, baseEnd_2256293] using wordTrace_append hprefix tailTrace_2256293
  have hstable : (prefixWord ++ tailWord_2256293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256293).length < 2 ^ (prefixWord ++ tailWord_2256293).sum := by decide
  have hdescent : baseEnd_2256293 < baseStart_2256293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256331 : List Nat := [1, 1, 1, 1, 3, 3, 6, 2, 1, 1, 3]
def baseStart_2256331 : Nat := 118140960795 + 2256331 * 2 ^ 59
def prefixEnd_2256331 : Nat := 4983230072969 + 3 ^ 40 * 2256331 * 2
def baseEnd_2256331 : Nat := 1158582318639916828285829

theorem tailTrace_2256331 : CollatzResearch.WordTrace tailWord_2256331 prefixEnd_2256331 1158582318639916828285829 := by
  unfold tailWord_2256331
  simp only [CollatzResearch.WordTrace]
  refine ⟨82295152388705612500576847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54863434925803741667051231 82295152388705612500576847)
  ·
    refine ⟨123442728583058418750865271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82295152388705612500576847 123442728583058418750865271)
    ·
      refine ⟨185164092874587628126297907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123442728583058418750865271 185164092874587628126297907)
      ·
        refine ⟨277746139311881442189446861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185164092874587628126297907 277746139311881442189446861)
        ·
          refine ⟨104154802241955540821042573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277746139311881442189446861 104154802241955540821042573)
          ·
            refine ⟨39058050840733327807890965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104154802241955540821042573 39058050840733327807890965)
            ·
              refine ⟨1830846133159374740994889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39058050840733327807890965 1830846133159374740994889)
              ·
                refine ⟨1373134599869531055746167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1830846133159374740994889 1373134599869531055746167)
                ·
                  refine ⟨2059701899804296583619251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373134599869531055746167 2059701899804296583619251)
                  ·
                    refine ⟨3089552849706444875428877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2059701899804296583619251 3089552849706444875428877)
                    ·
                      refine ⟨1158582318639916828285829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3089552849706444875428877 1158582318639916828285829)
                      ·
                        rfl

theorem cell23_2256331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 1, 3].length) (baseStart_2256331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256331 prefixEnd_2256331 := by exact prefixLift 2256331
  have htrace : WordTrace (prefixWord ++ tailWord_2256331) baseStart_2256331 baseEnd_2256331 := by
    simpa [prefixWord, tailWord_2256331, baseEnd_2256331] using wordTrace_append hprefix tailTrace_2256331
  have hstable : (prefixWord ++ tailWord_2256331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256331).length < 2 ^ (prefixWord ++ tailWord_2256331).sum := by decide
  have hdescent : baseEnd_2256331 < baseStart_2256331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256388 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_2256388 : Nat := 118140960795 + 2256388 * 2 ^ 59
def prefixEnd_2256388 : Nat := 4983230072969 + 3 ^ 40 * 2256388 * 2
def baseEnd_2256388 : Nat := 1158611587037223105273067

theorem tailTrace_2256388 : CollatzResearch.WordTrace tailWord_2256388 prefixEnd_2256388 1158611587037223105273067 := by
  unfold tailWord_2256388
  simp only [CollatzResearch.WordTrace]
  refine ⟨41148615674749555617700909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54864820899666074156934545 41148615674749555617700909)
  ·
    refine ⟨15430730878031083356637841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41148615674749555617700909 15430730878031083356637841)
    ·
      refine ⟨11573048158523312517478381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15430730878031083356637841 11573048158523312517478381)
      ·
        refine ⟨4339893059446242194054393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11573048158523312517478381 4339893059446242194054393)
        ·
          refine ⟨3254919794584681645540795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4339893059446242194054393 3254919794584681645540795)
          ·
            refine ⟨4882379691877022468311193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3254919794584681645540795 4882379691877022468311193)
            ·
              refine ⟨3661784768907766851233395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4882379691877022468311193 3661784768907766851233395)
              ·
                refine ⟨5492677153361650276850093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3661784768907766851233395 5492677153361650276850093)
                ·
                  refine ⟨2059753932510618853818785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5492677153361650276850093 2059753932510618853818785)
                  ·
                    refine ⟨1544815449382964140364089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2059753932510618853818785 1544815449382964140364089)
                    ·
                      refine ⟨1158611587037223105273067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544815449382964140364089 1158611587037223105273067)
                      ·
                        rfl

theorem cell23_2256388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_2256388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256388 prefixEnd_2256388 := by exact prefixLift 2256388
  have htrace : WordTrace (prefixWord ++ tailWord_2256388) baseStart_2256388 baseEnd_2256388 := by
    simpa [prefixWord, tailWord_2256388, baseEnd_2256388] using wordTrace_append hprefix tailTrace_2256388
  have hstable : (prefixWord ++ tailWord_2256388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256388).length < 2 ^ (prefixWord ++ tailWord_2256388).sum := by decide
  have hdescent : baseEnd_2256388 < baseStart_2256388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256455 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_2256455 : Nat := 118140960795 + 2256455 * 2 ^ 59
def prefixEnd_2256455 : Nat := 4983230072969 + 3 ^ 40 * 2256455 * 2
def baseEnd_2256455 : Nat := 1158645990241074343135259

theorem tailTrace_2256455 : CollatzResearch.WordTrace tailWord_2256455 prefixEnd_2256455 1158645990241074343135259 := by
  unfold tailWord_2256455
  simp only [CollatzResearch.WordTrace]
  refine ⟨82299675040256381678090819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54866450026837587785393879 82299675040256381678090819)
  ·
    refine ⟨123449512560384572517136229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82299675040256381678090819 123449512560384572517136229)
    ·
      refine ⟨23146783605072107346963043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123449512560384572517136229 23146783605072107346963043)
      ·
        refine ⟨34720175407608161020444565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23146783605072107346963043 34720175407608161020444565)
        ·
          refine ⟨1627508222231632547833339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34720175407608161020444565 1627508222231632547833339)
          ·
            refine ⟨2441262333347448821750009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627508222231632547833339 2441262333347448821750009)
            ·
              refine ⟨1830946750010586616312507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2441262333347448821750009 1830946750010586616312507)
              ·
                refine ⟨2746420125015879924468761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830946750010586616312507 2746420125015879924468761)
                ·
                  refine ⟨2059815093761909943351571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2746420125015879924468761 2059815093761909943351571)
                  ·
                    refine ⟨3089722640642864915027357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2059815093761909943351571 3089722640642864915027357)
                    ·
                      refine ⟨1158645990241074343135259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3089722640642864915027357 1158645990241074343135259)
                      ·
                        rfl

theorem cell23_2256455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_2256455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256455 prefixEnd_2256455 := by exact prefixLift 2256455
  have htrace : WordTrace (prefixWord ++ tailWord_2256455) baseStart_2256455 baseEnd_2256455 := by
    simpa [prefixWord, tailWord_2256455, baseEnd_2256455] using wordTrace_append hprefix tailTrace_2256455
  have hstable : (prefixWord ++ tailWord_2256455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256455).length < 2 ^ (prefixWord ++ tailWord_2256455).sum := by decide
  have hdescent : baseEnd_2256455 < baseStart_2256455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256501 : List Nat := [1, 3, 4, 2, 1, 2, 1, 4, 5]
def baseStart_2256501 : Nat := 118140960795 + 2256501 * 2 ^ 59
def prefixEnd_2256501 : Nat := 4983230072969 + 3 ^ 40 * 2256501 * 2
def baseEnd_2256501 : Nat := 128741067816797907017783

theorem tailTrace_2256501 : CollatzResearch.WordTrace tailWord_2256501 prefixEnd_2256501 128741067816797907017783 := by
  unfold tailWord_2256501
  simp only [CollatzResearch.WordTrace]
  refine ⟨82301352798089731534265357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54867568532059821022843571 82301352798089731534265357)
  ·
    refine ⟨30863007299283649325349509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82301352798089731534265357 30863007299283649325349509)
    ·
      refine ⟨5786813868615684248503033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30863007299283649325349509 5786813868615684248503033)
      ·
        refine ⟨4340110401461763186377275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5786813868615684248503033 4340110401461763186377275)
        ·
          refine ⟨6510165602192644779565913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4340110401461763186377275 6510165602192644779565913)
          ·
            refine ⟨4882624201644483584674435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6510165602192644779565913 4882624201644483584674435)
            ·
              refine ⟨7323936302466725377011653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4882624201644483584674435 7323936302466725377011653)
              ·
                refine ⟨1373238056712511008189685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7323936302466725377011653 1373238056712511008189685)
                ·
                  refine ⟨128741067816797907017783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1373238056712511008189685 128741067816797907017783)
                  ·
                    rfl

theorem cell23_2256501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_2256501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256501 prefixEnd_2256501 := by exact prefixLift 2256501
  have htrace : WordTrace (prefixWord ++ tailWord_2256501) baseStart_2256501 baseEnd_2256501 := by
    simpa [prefixWord, tailWord_2256501, baseEnd_2256501] using wordTrace_append hprefix tailTrace_2256501
  have hstable : (prefixWord ++ tailWord_2256501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256501).length < 2 ^ (prefixWord ++ tailWord_2256501).sum := by decide
  have hdescent : baseEnd_2256501 < baseStart_2256501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256517 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_2256517 : Nat := 118140960795 + 2256517 * 2 ^ 59
def prefixEnd_2256517 : Nat := 4983230072969 + 3 ^ 40 * 2256517 * 2
def baseEnd_2256517 : Nat := 1158677826041653100559973

theorem tailTrace_2256517 : CollatzResearch.WordTrace tailWord_2256517 prefixEnd_2256517 1158677826041653100559973 := by
  unfold tailWord_2256517
  simp only [CollatzResearch.WordTrace]
  refine ⟨82301936366031766266847805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54867957577354510844565203 82301936366031766266847805)
  ·
    refine ⟨30863226137261912350067927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82301936366031766266847805 30863226137261912350067927)
    ·
      refine ⟨46294839205892868525101891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30863226137261912350067927 46294839205892868525101891)
      ·
        refine ⟨69442258808839302787652837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46294839205892868525101891 69442258808839302787652837)
        ·
          refine ⟨13020423526657369272684907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69442258808839302787652837 13020423526657369272684907)
          ·
            refine ⟨19530635289986053909027361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13020423526657369272684907 19530635289986053909027361)
            ·
              refine ⟨14647976467489540431770521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19530635289986053909027361 14647976467489540431770521)
              ·
                refine ⟨10985982350617155323827891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14647976467489540431770521 10985982350617155323827891)
                ·
                  refine ⟨16478973525925732985741837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10985982350617155323827891 16478973525925732985741837)
                  ·
                    refine ⟨6179615072222149869653189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16478973525925732985741837 6179615072222149869653189)
                    ·
                      refine ⟨1158677826041653100559973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6179615072222149869653189 1158677826041653100559973)
                      ·
                        rfl

theorem cell23_2256517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_2256517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256517 prefixEnd_2256517 := by exact prefixLift 2256517
  have htrace : WordTrace (prefixWord ++ tailWord_2256517) baseStart_2256517 baseEnd_2256517 := by
    simpa [prefixWord, tailWord_2256517, baseEnd_2256517] using wordTrace_append hprefix tailTrace_2256517
  have hstable : (prefixWord ++ tailWord_2256517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256517).length < 2 ^ (prefixWord ++ tailWord_2256517).sum := by decide
  have hdescent : baseEnd_2256517 < baseStart_2256517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256587 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 3, 5]
def baseStart_2256587 : Nat := 118140960795 + 2256587 * 2 ^ 59
def prefixEnd_2256587 : Nat := 4983230072969 + 3 ^ 40 * 2256587 * 2
def baseEnd_2256587 : Nat := 386237923229155942228217

theorem tailTrace_2256587 : CollatzResearch.WordTrace tailWord_2256587 prefixEnd_2256587 386237923229155942228217 := by
  unfold tailWord_2256587
  simp only [CollatzResearch.WordTrace]
  refine ⟨82304489475778168221896015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54869659650518778814597343 82304489475778168221896015)
  ·
    refine ⟨123456734213667252332844023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82304489475778168221896015 123456734213667252332844023)
    ·
      refine ⟨185185101320500878499266035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123456734213667252332844023 185185101320500878499266035)
      ·
        refine ⟨277777651980751317748899053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185185101320500878499266035 277777651980751317748899053)
        ·
          refine ⟨104166619492781744155837145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277777651980751317748899053 104166619492781744155837145)
          ·
            refine ⟨78124964619586308116877859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104166619492781744155837145 78124964619586308116877859)
            ·
              refine ⟨117187446929379462175316789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78124964619586308116877859 117187446929379462175316789)
              ·
                refine ⟨10986323149629324578935949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117187446929379462175316789 10986323149629324578935949)
                ·
                  refine ⟨4119871181110996717100981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10986323149629324578935949 4119871181110996717100981)
                  ·
                    refine ⟨386237923229155942228217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4119871181110996717100981 386237923229155942228217)
                    ·
                      rfl

theorem cell23_2256587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 5].length) (baseStart_2256587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256587 prefixEnd_2256587 := by exact prefixLift 2256587
  have htrace : WordTrace (prefixWord ++ tailWord_2256587) baseStart_2256587 baseEnd_2256587 := by
    simpa [prefixWord, tailWord_2256587, baseEnd_2256587] using wordTrace_append hprefix tailTrace_2256587
  have hstable : (prefixWord ++ tailWord_2256587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256587).length < 2 ^ (prefixWord ++ tailWord_2256587).sum := by decide
  have hdescent : baseEnd_2256587 < baseStart_2256587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256618 : List Nat := [3, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_2256618 : Nat := 118140960795 + 2256618 * 2 ^ 59
def prefixEnd_2256618 : Nat := 4983230072969 + 3 ^ 40 * 2256618 * 2
def baseEnd_2256618 : Nat := 1158729687587757205397009

theorem tailTrace_2256618 : CollatzResearch.WordTrace tailWord_2256618 prefixEnd_2256618 1158729687587757205397009 := by
  unfold tailWord_2256618
  simp only [CollatzResearch.WordTrace]
  refine ⟨20576405034666465129068627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54870413425777240344183005 20576405034666465129068627)
  ·
    refine ⟨30864607551999697693602941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20576405034666465129068627 30864607551999697693602941)
    ·
      refine ⟨11574227831999886635101103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30864607551999697693602941 11574227831999886635101103)
      ·
        refine ⟨17361341747999829952651655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11574227831999886635101103 17361341747999829952651655)
        ·
          refine ⟨26042012621999744928977483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17361341747999829952651655 26042012621999744928977483)
          ·
            refine ⟨39063018932999617393466225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26042012621999744928977483 39063018932999617393466225)
            ·
              refine ⟨29297264199749713045099669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39063018932999617393466225 29297264199749713045099669)
              ·
                refine ⟨1373309259363267798989047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29297264199749713045099669 1373309259363267798989047)
                ·
                  refine ⟨2059963889044901698483571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373309259363267798989047 2059963889044901698483571)
                  ·
                    refine ⟨3089945833567352547725357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2059963889044901698483571 3089945833567352547725357)
                    ·
                      refine ⟨1158729687587757205397009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3089945833567352547725357 1158729687587757205397009)
                      ·
                        rfl

theorem cell23_2256618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_2256618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256618 prefixEnd_2256618 := by exact prefixLift 2256618
  have htrace : WordTrace (prefixWord ++ tailWord_2256618) baseStart_2256618 baseEnd_2256618 := by
    simpa [prefixWord, tailWord_2256618, baseEnd_2256618] using wordTrace_append hprefix tailTrace_2256618
  have hstable : (prefixWord ++ tailWord_2256618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256618).length < 2 ^ (prefixWord ++ tailWord_2256618).sum := by decide
  have hdescent : baseEnd_2256618 < baseStart_2256618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256624 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 2, 6, 2]
def baseStart_2256624 : Nat := 118140960795 + 2256624 * 2 ^ 59
def prefixEnd_2256624 : Nat := 4983230072969 + 3 ^ 40 * 2256624 * 2
def baseEnd_2256624 : Nat := 1158732768471684181921981

theorem tailTrace_2256624 : CollatzResearch.WordTrace tailWord_2256624 prefixEnd_2256624 1158732768471684181921981 := by
  unfold tailWord_2256624
  simp only [CollatzResearch.WordTrace]
  refine ⟨41152919488322061770496463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54870559317762749027328617 41152919488322061770496463)
  ·
    refine ⟨61729379232483092655744695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41152919488322061770496463 61729379232483092655744695)
    ·
      refine ⟨92594068848724638983617043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61729379232483092655744695 92594068848724638983617043)
      ·
        refine ⟨138891103273086958475425565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92594068848724638983617043 138891103273086958475425565)
        ·
          refine ⟨52084163727407609428284587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138891103273086958475425565 52084163727407609428284587)
          ·
            refine ⟨78126245591111414142426881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52084163727407609428284587 78126245591111414142426881)
            ·
              refine ⟨58594684193333560606820161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78126245591111414142426881 58594684193333560606820161)
              ·
                refine ⟨43946013145000170455115121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58594684193333560606820161 43946013145000170455115121)
                ·
                  refine ⟨32959509858750127841336341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43946013145000170455115121 32959509858750127841336341)
                  ·
                    refine ⟨1544977024628912242562641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32959509858750127841336341 1544977024628912242562641)
                    ·
                      refine ⟨1158732768471684181921981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1544977024628912242562641 1158732768471684181921981)
                      ·
                        rfl

theorem cell23_2256624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 6, 2].length) (baseStart_2256624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256624 prefixEnd_2256624 := by exact prefixLift 2256624
  have htrace : WordTrace (prefixWord ++ tailWord_2256624) baseStart_2256624 baseEnd_2256624 := by
    simpa [prefixWord, tailWord_2256624, baseEnd_2256624] using wordTrace_append hprefix tailTrace_2256624
  have hstable : (prefixWord ++ tailWord_2256624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256624).length < 2 ^ (prefixWord ++ tailWord_2256624).sum := by decide
  have hdescent : baseEnd_2256624 < baseStart_2256624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256641 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_2256641 : Nat := 118140960795 + 2256641 * 2 ^ 59
def prefixEnd_2256641 : Nat := 4983230072969 + 3 ^ 40 * 2256641 * 2
def baseEnd_2256641 : Nat := 1158741497642810615409403

theorem tailTrace_2256641 : CollatzResearch.WordTrace tailWord_2256641 prefixEnd_2256641 1158741497642810615409403 := by
  unfold tailWord_2256641
  simp only [CollatzResearch.WordTrace]
  refine ⟨82306459017582535444361777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54870972678388356962907851 82306459017582535444361777)
  ·
    refine ⟨61729844263186901583271333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82306459017582535444361777 61729844263186901583271333)
    ·
      refine ⟨11574345799347544046863375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61729844263186901583271333 11574345799347544046863375)
      ·
        refine ⟨17361518699021316070295063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11574345799347544046863375 17361518699021316070295063)
        ·
          refine ⟨26042278048531974105442595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17361518699021316070295063 26042278048531974105442595)
          ·
            refine ⟨39063417072797961158163893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26042278048531974105442595 39063417072797961158163893)
            ·
              refine ⟨3662195350574808858577865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39063417072797961158163893 3662195350574808858577865)
              ·
                refine ⟨2746646512931106643933399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3662195350574808858577865 2746646512931106643933399)
                ·
                  refine ⟨4119969769396659965900099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2746646512931106643933399 4119969769396659965900099)
                  ·
                    refine ⟨6179954654094989948850149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4119969769396659965900099 6179954654094989948850149)
                    ·
                      refine ⟨1158741497642810615409403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6179954654094989948850149 1158741497642810615409403)
                      ·
                        rfl

theorem cell23_2256641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_2256641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256641 prefixEnd_2256641 := by exact prefixLift 2256641
  have htrace : WordTrace (prefixWord ++ tailWord_2256641) baseStart_2256641 baseEnd_2256641 := by
    simpa [prefixWord, tailWord_2256641, baseEnd_2256641] using wordTrace_append hprefix tailTrace_2256641
  have hstable : (prefixWord ++ tailWord_2256641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256641).length < 2 ^ (prefixWord ++ tailWord_2256641).sum := by decide
  have hdescent : baseEnd_2256641 < baseStart_2256641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256654 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2256654 : Nat := 118140960795 + 2256654 * 2 ^ 59
def prefixEnd_2256654 : Nat := 4983230072969 + 3 ^ 40 * 2256654 * 2
def baseEnd_2256654 : Nat := 1158748172891319064546843

theorem tailTrace_2256654 : CollatzResearch.WordTrace tailWord_2256654 prefixEnd_2256654 1158748172891319064546843 := by
  unfold tailWord_2256654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10288366645816929833073127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54871288777690292443056677 10288366645816929833073127)
  ·
    refine ⟨15432549968725394749609691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10288366645816929833073127 15432549968725394749609691)
    ·
      refine ⟨23148824953088092124414537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15432549968725394749609691 23148824953088092124414537)
      ·
        refine ⟨17361618714816069093310903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23148824953088092124414537 17361618714816069093310903)
        ·
          refine ⟨26042428072224103639966355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17361618714816069093310903 26042428072224103639966355)
          ·
            refine ⟨39063642108336155459949533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26042428072224103639966355 39063642108336155459949533)
            ·
              refine ⟨14648865790626058297481075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39063642108336155459949533 14648865790626058297481075)
              ·
                refine ⟨21973298685939087446221613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14648865790626058297481075 21973298685939087446221613)
                ·
                  refine ⟨8239987007227157792333105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21973298685939087446221613 8239987007227157792333105)
                  ·
                    refine ⟨6179990255420368344249829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8239987007227157792333105 6179990255420368344249829)
                    ·
                      refine ⟨1158748172891319064546843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6179990255420368344249829 1158748172891319064546843)
                      ·
                        rfl

theorem cell23_2256654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2256654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256654 prefixEnd_2256654 := by exact prefixLift 2256654
  have htrace : WordTrace (prefixWord ++ tailWord_2256654) baseStart_2256654 baseEnd_2256654 := by
    simpa [prefixWord, tailWord_2256654, baseEnd_2256654] using wordTrace_append hprefix tailTrace_2256654
  have hstable : (prefixWord ++ tailWord_2256654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256654).length < 2 ^ (prefixWord ++ tailWord_2256654).sum := by decide
  have hdescent : baseEnd_2256654 < baseStart_2256654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256661 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_2256661 : Nat := 118140960795 + 2256661 * 2 ^ 59
def prefixEnd_2256661 : Nat := 4983230072969 + 3 ^ 40 * 2256661 * 2
def baseEnd_2256661 : Nat := 1158751767255900537159311

theorem tailTrace_2256661 : CollatzResearch.WordTrace tailWord_2256661 prefixEnd_2256661 1158751767255900537159311 := by
  unfold tailWord_2256661
  simp only [CollatzResearch.WordTrace]
  refine ⟨82307188477510078860089837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54871458985006719240059891 82307188477510078860089837)
  ·
    refine ⟨30865195679066279572533689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82307188477510078860089837 30865195679066279572533689)
    ·
      refine ⟨23148896759299709679400267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30865195679066279572533689 23148896759299709679400267)
      ·
        refine ⟨34723345138949564519100401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23148896759299709679400267 34723345138949564519100401)
        ·
          refine ⟨26042508854212173389325301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34723345138949564519100401 26042508854212173389325301)
          ·
            refine ⟨2441485205082391255249247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26042508854212173389325301 2441485205082391255249247)
            ·
              refine ⟨3662227807623586882873871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441485205082391255249247 3662227807623586882873871)
              ·
                refine ⟨5493341711435380324310807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662227807623586882873871 5493341711435380324310807)
                ·
                  refine ⟨8240012567153070486466211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5493341711435380324310807 8240012567153070486466211)
                  ·
                    refine ⟨12360018850729605729699317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8240012567153070486466211 12360018850729605729699317)
                    ·
                      refine ⟨1158751767255900537159311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12360018850729605729699317 1158751767255900537159311)
                      ·
                        rfl

theorem cell23_2256661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_2256661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256661 prefixEnd_2256661 := by exact prefixLift 2256661
  have htrace : WordTrace (prefixWord ++ tailWord_2256661) baseStart_2256661 baseEnd_2256661 := by
    simpa [prefixWord, tailWord_2256661, baseEnd_2256661] using wordTrace_append hprefix tailTrace_2256661
  have hstable : (prefixWord ++ tailWord_2256661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256661).length < 2 ^ (prefixWord ++ tailWord_2256661).sum := by decide
  have hdescent : baseEnd_2256661 < baseStart_2256661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256725 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_2256725 : Nat := 118140960795 + 2256725 * 2 ^ 59
def prefixEnd_2256725 : Nat := 4983230072969 + 3 ^ 40 * 2256725 * 2
def baseEnd_2256725 : Nat := 1158784630017788286759017

theorem tailTrace_2256725 : CollatzResearch.WordTrace tailWord_2256725 prefixEnd_2256725 1158784630017788286759017 := by
  unfold tailWord_2256725
  simp only [CollatzResearch.WordTrace]
  refine ⟨82309522749278217790419629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54873015166185478526946419 82309522749278217790419629)
  ·
    refine ⟨30866071030979331671407361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82309522749278217790419629 30866071030979331671407361)
    ·
      refine ⟨23149553273234498753555521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30866071030979331671407361 23149553273234498753555521)
      ·
        refine ⟨17362164954925874065166641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23149553273234498753555521 17362164954925874065166641)
        ·
          refine ⟨13021623716194405548874981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17362164954925874065166641 13021623716194405548874981)
          ·
            refine ⟨2441554446786451040414059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13021623716194405548874981 2441554446786451040414059)
            ·
              refine ⟨3662331670179676560621089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441554446786451040414059 3662331670179676560621089)
              ·
                refine ⟨2746748752634757420465817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3662331670179676560621089 2746748752634757420465817)
                ·
                  refine ⟨2060061564476068065349363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2746748752634757420465817 2060061564476068065349363)
                  ·
                    refine ⟨3090092346714102098024045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2060061564476068065349363 3090092346714102098024045)
                    ·
                      refine ⟨1158784630017788286759017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3090092346714102098024045 1158784630017788286759017)
                      ·
                        rfl

theorem cell23_2256725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_2256725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256725 prefixEnd_2256725 := by exact prefixLift 2256725
  have htrace : WordTrace (prefixWord ++ tailWord_2256725) baseStart_2256725 baseEnd_2256725 := by
    simpa [prefixWord, tailWord_2256725, baseEnd_2256725] using wordTrace_append hprefix tailTrace_2256725
  have hstable : (prefixWord ++ tailWord_2256725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256725).length < 2 ^ (prefixWord ++ tailWord_2256725).sum := by decide
  have hdescent : baseEnd_2256725 < baseStart_2256725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256748 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 1, 4, 2]
def baseStart_2256748 : Nat := 118140960795 + 2256748 * 2 ^ 59
def prefixEnd_2256748 : Nat := 4983230072969 + 3 ^ 40 * 2256748 * 2
def baseEnd_2256748 : Nat := 1158796440072841696771411

theorem tailTrace_2256748 : CollatzResearch.WordTrace tailWord_2256748 prefixEnd_2256748 1158796440072841696771411 := by
  unfold tailWord_2256748
  simp only [CollatzResearch.WordTrace]
  refine ⟨41155180814097446359253449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54873574418796595145671265 41155180814097446359253449)
  ·
    refine ⟨30866385610573084769440087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41155180814097446359253449 30866385610573084769440087)
    ·
      refine ⟨46299578415859627154160131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30866385610573084769440087 46299578415859627154160131)
      ·
        refine ⟨69449367623789440731240197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46299578415859627154160131 69449367623789440731240197)
        ·
          refine ⟨13021756429460520137107537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69449367623789440731240197 13021756429460520137107537)
          ·
            refine ⟨9766317322095390102830653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13021756429460520137107537 9766317322095390102830653)
            ·
              refine ⟨3662368995785771288561495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9766317322095390102830653 3662368995785771288561495)
              ·
                refine ⟨5493553493678656932842243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662368995785771288561495 5493553493678656932842243)
                ·
                  refine ⟨8240330240517985399263365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5493553493678656932842243 8240330240517985399263365)
                  ·
                    refine ⟨1545061920097122262361881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8240330240517985399263365 1545061920097122262361881)
                    ·
                      refine ⟨1158796440072841696771411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545061920097122262361881 1158796440072841696771411)
                      ·
                        rfl

theorem cell23_2256748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_2256748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256748 prefixEnd_2256748 := by exact prefixLift 2256748
  have htrace : WordTrace (prefixWord ++ tailWord_2256748) baseStart_2256748 baseEnd_2256748 := by
    simpa [prefixWord, tailWord_2256748, baseEnd_2256748] using wordTrace_append hprefix tailTrace_2256748
  have hstable : (prefixWord ++ tailWord_2256748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256748).length < 2 ^ (prefixWord ++ tailWord_2256748).sum := by decide
  have hdescent : baseEnd_2256748 < baseStart_2256748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256784 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 4, 5]
def baseStart_2256784 : Nat := 118140960795 + 2256784 * 2 ^ 59
def prefixEnd_2256784 : Nat := 4983230072969 + 3 ^ 40 * 2256784 * 2
def baseEnd_2256784 : Nat := 386271641792134518640415

theorem tailTrace_2256784 : CollatzResearch.WordTrace tailWord_2256784 prefixEnd_2256784 386271641792134518640415 := by
  unfold tailWord_2256784
  simp only [CollatzResearch.WordTrace]
  refine ⟨41155837328032235433408703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54874449770709647244544937 41155837328032235433408703)
  ·
    refine ⟨61733755992048353150113055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41155837328032235433408703 61733755992048353150113055)
    ·
      refine ⟨92600633988072529725169583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61733755992048353150113055 92600633988072529725169583)
      ·
        refine ⟨138900950982108794587754375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92600633988072529725169583 138900950982108794587754375)
        ·
          refine ⟨208351426473163191881631563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138900950982108794587754375 208351426473163191881631563)
          ·
            refine ⟨312527139709744787822447345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208351426473163191881631563 312527139709744787822447345)
            ·
              refine ⟨234395354782308590866835509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312527139709744787822447345 234395354782308590866835509)
              ·
                refine ⟨21974564510841430393765829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234395354782308590866835509 21974564510841430393765829)
                ·
                  refine ⟨4120230845782768198831093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21974564510841430393765829 4120230845782768198831093)
                  ·
                    refine ⟨386271641792134518640415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4120230845782768198831093 386271641792134518640415)
                    ·
                      rfl

theorem cell23_2256784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_2256784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256784 prefixEnd_2256784 := by exact prefixLift 2256784
  have htrace : WordTrace (prefixWord ++ tailWord_2256784) baseStart_2256784 baseEnd_2256784 := by
    simpa [prefixWord, tailWord_2256784, baseEnd_2256784] using wordTrace_append hprefix tailTrace_2256784
  have hstable : (prefixWord ++ tailWord_2256784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256784).length < 2 ^ (prefixWord ++ tailWord_2256784).sum := by decide
  have hdescent : baseEnd_2256784 < baseStart_2256784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256788 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 7]
def baseStart_2256788 : Nat := 118140960795 + 2256788 * 2 ^ 59
def prefixEnd_2256788 : Nat := 4983230072969 + 3 ^ 40 * 2256788 * 2
def baseEnd_2256788 : Nat := 128757442144335726696803

theorem tailTrace_2256788 : CollatzResearch.WordTrace tailWord_2256788 prefixEnd_2256788 128757442144335726696803 := by
  unfold tailWord_2256788
  simp only [CollatzResearch.WordTrace]
  refine ⟨41155910274024989774981509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54874547032033319699975345 41155910274024989774981509)
  ·
    refine ⟨7716733176379685582809033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41155910274024989774981509 7716733176379685582809033)
    ·
      refine ⟨5787549882284764187106775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7716733176379685582809033 5787549882284764187106775)
      ·
        refine ⟨8681324823427146280660163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5787549882284764187106775 8681324823427146280660163)
        ·
          refine ⟨13021987235140719420990245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8681324823427146280660163 13021987235140719420990245)
          ·
            refine ⟨2441622606588884891435671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13021987235140719420990245 2441622606588884891435671)
            ·
              refine ⟨3662433909883327337153507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441622606588884891435671 3662433909883327337153507)
              ·
                refine ⟨5493650864824991005730261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662433909883327337153507 5493650864824991005730261)
                ·
                  refine ⟨128757442144335726696803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5493650864824991005730261 128757442144335726696803)
                  ·
                    rfl

theorem cell23_2256788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_2256788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256788 prefixEnd_2256788 := by exact prefixLift 2256788
  have htrace : WordTrace (prefixWord ++ tailWord_2256788) baseStart_2256788 baseEnd_2256788 := by
    simpa [prefixWord, tailWord_2256788, baseEnd_2256788] using wordTrace_append hprefix tailTrace_2256788
  have hstable : (prefixWord ++ tailWord_2256788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256788).length < 2 ^ (prefixWord ++ tailWord_2256788).sum := by decide
  have hdescent : baseEnd_2256788 < baseStart_2256788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256799 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 2, 2, 2]
def baseStart_2256799 : Nat := 118140960795 + 2256799 * 2 ^ 59
def prefixEnd_2256799 : Nat := 4983230072969 + 3 ^ 40 * 2256799 * 2
def baseEnd_2256799 : Nat := 1158822627586220997233677

theorem tailTrace_2256799 : CollatzResearch.WordTrace tailWord_2256799 prefixEnd_2256799 1158822627586220997233677 := by
  unfold tailWord_2256799
  simp only [CollatzResearch.WordTrace]
  refine ⟨82312221751010128428613451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54874814500673418952408967 82312221751010128428613451)
  ·
    refine ⟨123468332626515192642920177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82312221751010128428613451 123468332626515192642920177)
    ·
      refine ⟨92601249469886394482190133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123468332626515192642920177 92601249469886394482190133)
      ·
        refine ⟨8681367137801849482705325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92601249469886394482190133 8681367137801849482705325)
        ·
          refine ⟨3255512676675693556014497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8681367137801849482705325 3255512676675693556014497)
          ·
            refine ⟨2441634507506770167010873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3255512676675693556014497 2441634507506770167010873)
            ·
              refine ⟨1831225880630077625258155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2441634507506770167010873 1831225880630077625258155)
              ·
                refine ⟨2746838820945116437887233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1831225880630077625258155 2746838820945116437887233)
                ·
                  refine ⟨2060129115708837328415425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2746838820945116437887233 2060129115708837328415425)
                  ·
                    refine ⟨1545096836781627996311569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060129115708837328415425 1545096836781627996311569)
                    ·
                      refine ⟨1158822627586220997233677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545096836781627996311569 1158822627586220997233677)
                      ·
                        rfl

theorem cell23_2256799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_2256799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256799 prefixEnd_2256799 := by exact prefixLift 2256799
  have htrace : WordTrace (prefixWord ++ tailWord_2256799) baseStart_2256799 baseEnd_2256799 := by
    simpa [prefixWord, tailWord_2256799, baseEnd_2256799] using wordTrace_append hprefix tailTrace_2256799
  have hstable : (prefixWord ++ tailWord_2256799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256799).length < 2 ^ (prefixWord ++ tailWord_2256799).sum := by decide
  have hdescent : baseEnd_2256799 < baseStart_2256799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256925 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_2256925 : Nat := 118140960795 + 2256925 * 2 ^ 59
def prefixEnd_2256925 : Nat := 4983230072969 + 3 ^ 40 * 2256925 * 2
def baseEnd_2256925 : Nat := 386295775382895834752699

theorem tailTrace_2256925 : CollatzResearch.WordTrace tailWord_2256925 prefixEnd_2256925 386295775382895834752699 := by
  unfold tailWord_2256925
  simp only [CollatzResearch.WordTrace]
  refine ⟨82316817348553651947700229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54877878232369101298466819 82316817348553651947700229)
  ·
    refine ⟨15434403252853809740193793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82316817348553651947700229 15434403252853809740193793)
    ·
      refine ⟨11575802439640357305145345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15434403252853809740193793 11575802439640357305145345)
      ·
        refine ⟨8681851829730267978859009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11575802439640357305145345 8681851829730267978859009)
        ·
          refine ⟨6511388872297700984144257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8681851829730267978859009 6511388872297700984144257)
          ·
            refine ⟨4883541654223275738108193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6511388872297700984144257 4883541654223275738108193)
            ·
              refine ⟨3662656240667456803581145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4883541654223275738108193 3662656240667456803581145)
              ·
                refine ⟨2746992180500592602685859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3662656240667456803581145 2746992180500592602685859)
                ·
                  refine ⟨4120488270750888904028789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2746992180500592602685859 4120488270750888904028789)
                  ·
                    refine ⟨386295775382895834752699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4120488270750888904028789 386295775382895834752699)
                    ·
                      rfl

theorem cell23_2256925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_2256925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256925 prefixEnd_2256925 := by exact prefixLift 2256925
  have htrace : WordTrace (prefixWord ++ tailWord_2256925) baseStart_2256925 baseEnd_2256925 := by
    simpa [prefixWord, tailWord_2256925, baseEnd_2256925] using wordTrace_append hprefix tailTrace_2256925
  have hstable : (prefixWord ++ tailWord_2256925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256925).length < 2 ^ (prefixWord ++ tailWord_2256925).sum := by decide
  have hdescent : baseEnd_2256925 < baseStart_2256925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256931 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 5]
def baseStart_2256931 : Nat := 118140960795 + 2256931 * 2 ^ 59
def prefixEnd_2256931 : Nat := 4983230072969 + 3 ^ 40 * 2256931 * 2
def baseEnd_2256931 : Nat := 1158890407032614480783069

theorem tailTrace_2256931 : CollatzResearch.WordTrace tailWord_2256931 prefixEnd_2256931 1158890407032614480783069 := by
  unfold tailWord_2256931
  simp only [CollatzResearch.WordTrace]
  refine ⟨82317036186531914972418647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54878024124354609981612431 82317036186531914972418647)
  ·
    refine ⟨123475554279797872458627971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82317036186531914972418647 123475554279797872458627971)
    ·
      refine ⟨185213331419696808687941957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123475554279797872458627971 185213331419696808687941957)
      ·
        refine ⟨34727499641193151628989117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185213331419696808687941957 34727499641193151628989117)
        ·
          refine ⟨13022812365447431860870919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34727499641193151628989117 13022812365447431860870919)
          ·
            refine ⟨19534218548171147791306379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13022812365447431860870919 19534218548171147791306379)
            ·
              refine ⟨29301327822256721686959569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19534218548171147791306379 29301327822256721686959569)
              ·
                refine ⟨21975995866692541265219677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29301327822256721686959569 21975995866692541265219677)
                ·
                  refine ⟨8240998450009702974457379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21975995866692541265219677 8240998450009702974457379)
                  ·
                    refine ⟨12361497675014554461686069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8240998450009702974457379 12361497675014554461686069)
                    ·
                      refine ⟨1158890407032614480783069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12361497675014554461686069 1158890407032614480783069)
                      ·
                        rfl

theorem cell23_2256931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_2256931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256931 prefixEnd_2256931 := by exact prefixLift 2256931
  have htrace : WordTrace (prefixWord ++ tailWord_2256931) baseStart_2256931 baseEnd_2256931 := by
    simpa [prefixWord, tailWord_2256931, baseEnd_2256931] using wordTrace_append hprefix tailTrace_2256931
  have hstable : (prefixWord ++ tailWord_2256931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256931).length < 2 ^ (prefixWord ++ tailWord_2256931).sum := by decide
  have hdescent : baseEnd_2256931 < baseStart_2256931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256991 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_2256991 : Nat := 118140960795 + 2256991 * 2 ^ 59
def prefixEnd_2256991 : Nat := 4983230072969 + 3 ^ 40 * 2256991 * 2
def baseEnd_2256991 : Nat := 1158921215871884246032793

theorem tailTrace_2256991 : CollatzResearch.WordTrace tailWord_2256991 prefixEnd_2256991 1158921215871884246032793 := by
  unfold tailWord_2256991
  simp only [CollatzResearch.WordTrace]
  refine ⟨82319224566314545219602827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54879483044209696813068551 82319224566314545219602827)
  ·
    refine ⟨123478836849471817829404241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82319224566314545219602827 123478836849471817829404241)
    ·
      refine ⟨92609127637103863372053181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123478836849471817829404241 92609127637103863372053181)
      ·
        refine ⟨34728422863913948764519943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92609127637103863372053181 34728422863913948764519943)
        ·
          refine ⟨52092634295870923146779915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34728422863913948764519943 52092634295870923146779915)
          ·
            refine ⟨78138951443806384720169873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52092634295870923146779915 78138951443806384720169873)
            ·
              refine ⟨58604213582854788540127405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78138951443806384720169873 58604213582854788540127405)
              ·
                refine ⟨21976580093570545702547777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58604213582854788540127405 21976580093570545702547777)
                ·
                  refine ⟨16482435070177909276910833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21976580093570545702547777 16482435070177909276910833)
                  ·
                    refine ⟨12361826302633431957683125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16482435070177909276910833 12361826302633431957683125)
                    ·
                      refine ⟨1158921215871884246032793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12361826302633431957683125 1158921215871884246032793)
                      ·
                        rfl

theorem cell23_2256991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_2256991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2256991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2256991 prefixEnd_2256991 := by exact prefixLift 2256991
  have htrace : WordTrace (prefixWord ++ tailWord_2256991) baseStart_2256991 baseEnd_2256991 := by
    simpa [prefixWord, tailWord_2256991, baseEnd_2256991] using wordTrace_append hprefix tailTrace_2256991
  have hstable : (prefixWord ++ tailWord_2256991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256991).length < 2 ^ (prefixWord ++ tailWord_2256991).sum := by decide
  have hdescent : baseEnd_2256991 < baseStart_2256991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257028 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_2257028 : Nat := 118140960795 + 2257028 * 2 ^ 59
def prefixEnd_2257028 : Nat := 4983230072969 + 3 ^ 40 * 2257028 * 2
def baseEnd_2257028 : Nat := 386313404885366867090041

theorem tailTrace_2257028 : CollatzResearch.WordTrace tailWord_2257028 prefixEnd_2257028 386313404885366867090041 := by
  unfold tailWord_2257028
  simp only [CollatzResearch.WordTrace]
  refine ⟨41160287033590250269349869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54880382711453667025799825 41160287033590250269349869)
  ·
    refine ⟨15435107637596343851006201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41160287033590250269349869 15435107637596343851006201)
    ·
      refine ⟨11576330728197257888254651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15435107637596343851006201 11576330728197257888254651)
      ·
        refine ⟨17364496092295886832381977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11576330728197257888254651 17364496092295886832381977)
        ·
          refine ⟨13023372069221915124286483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17364496092295886832381977 13023372069221915124286483)
          ·
            refine ⟨19535058103832872686429725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13023372069221915124286483 19535058103832872686429725)
            ·
              refine ⟨7325646788937327257411147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19535058103832872686429725 7325646788937327257411147)
              ·
                refine ⟨10988470183405990886116721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7325646788937327257411147 10988470183405990886116721)
                ·
                  refine ⟨8241352637554493164587541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10988470183405990886116721 8241352637554493164587541)
                  ·
                    refine ⟨386313404885366867090041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8241352637554493164587541 386313404885366867090041)
                    ·
                      rfl

theorem cell23_2257028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_2257028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257028 prefixEnd_2257028 := by exact prefixLift 2257028
  have htrace : WordTrace (prefixWord ++ tailWord_2257028) baseStart_2257028 baseEnd_2257028 := by
    simpa [prefixWord, tailWord_2257028, baseEnd_2257028] using wordTrace_append hprefix tailTrace_2257028
  have hstable : (prefixWord ++ tailWord_2257028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257028).length < 2 ^ (prefixWord ++ tailWord_2257028).sum := by decide
  have hdescent : baseEnd_2257028 < baseStart_2257028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257035 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 8, 2, 2]
def baseStart_2257035 : Nat := 118140960795 + 2257035 * 2 ^ 59
def prefixEnd_2257035 : Nat := 4983230072969 + 3 ^ 40 * 2257035 * 2
def baseEnd_2257035 : Nat := 1158943809020682073882591

theorem tailTrace_2257035 : CollatzResearch.WordTrace tailWord_2257035 prefixEnd_2257035 1158943809020682073882591 := by
  unfold tailWord_2257035
  simp only [CollatzResearch.WordTrace]
  refine ⟨82320829378155140734204559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54880552918770093822803039 82320829378155140734204559)
  ·
    refine ⟨123481244067232711101306839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82320829378155140734204559 123481244067232711101306839)
    ·
      refine ⟨185221866100849066651960259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123481244067232711101306839 185221866100849066651960259)
      ·
        refine ⟨277832799151273599977940389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185221866100849066651960259 277832799151273599977940389)
        ·
          refine ⟨52093649840863799995863823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277832799151273599977940389 52093649840863799995863823)
          ·
            refine ⟨78140474761295699993795735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52093649840863799995863823 78140474761295699993795735)
            ·
              refine ⟨117210712141943549990693603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78140474761295699993795735 117210712141943549990693603)
              ·
                refine ⟨175816068212915324986040405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117210712141943549990693603 175816068212915324986040405)
                ·
                  refine ⟨2060344549370101464680161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 175816068212915324986040405 2060344549370101464680161)
                  ·
                    refine ⟨1545258412027576098510121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060344549370101464680161 1545258412027576098510121)
                    ·
                      refine ⟨1158943809020682073882591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545258412027576098510121 1158943809020682073882591)
                      ·
                        rfl

theorem cell23_2257035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 2, 2].length) (baseStart_2257035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257035 prefixEnd_2257035 := by exact prefixLift 2257035
  have htrace : WordTrace (prefixWord ++ tailWord_2257035) baseStart_2257035 baseEnd_2257035 := by
    simpa [prefixWord, tailWord_2257035, baseEnd_2257035] using wordTrace_append hprefix tailTrace_2257035
  have hstable : (prefixWord ++ tailWord_2257035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257035).length < 2 ^ (prefixWord ++ tailWord_2257035).sum := by decide
  have hdescent : baseEnd_2257035 < baseStart_2257035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257052 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_2257052 : Nat := 118140960795 + 2257052 * 2 ^ 59
def prefixEnd_2257052 : Nat := 4983230072969 + 3 ^ 40 * 2257052 * 2
def baseEnd_2257052 : Nat := 1158952538191808507370013

theorem tailTrace_2257052 : CollatzResearch.WordTrace tailWord_2257052 prefixEnd_2257052 1158952538191808507370013 := by
  unfold tailWord_2257052
  simp only [CollatzResearch.WordTrace]
  refine ⟨41160724709546776318786705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54880966279395701758382273 41160724709546776318786705)
  ·
    refine ⟨30870543532160082239090029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41160724709546776318786705 30870543532160082239090029)
    ·
      refine ⟨11576453824560030839658761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30870543532160082239090029 11576453824560030839658761)
      ·
        refine ⟨8682340368420023129744071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11576453824560030839658761 8682340368420023129744071)
        ·
          refine ⟨13023510552630034694616107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8682340368420023129744071 13023510552630034694616107)
          ·
            refine ⟨19535265828945052041924161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13023510552630034694616107 19535265828945052041924161)
            ·
              refine ⟨14651449371708789031443121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19535265828945052041924161 14651449371708789031443121)
              ·
                refine ⟨10988587028781591773582341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14651449371708789031443121 10988587028781591773582341)
                ·
                  refine ⟨2060360067896548457546689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10988587028781591773582341 2060360067896548457546689)
                  ·
                    refine ⟨1545270050922411343160017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060360067896548457546689 1545270050922411343160017)
                    ·
                      refine ⟨1158952538191808507370013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545270050922411343160017 1158952538191808507370013)
                      ·
                        rfl

theorem cell23_2257052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_2257052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257052 prefixEnd_2257052 := by exact prefixLift 2257052
  have htrace : WordTrace (prefixWord ++ tailWord_2257052) baseStart_2257052 baseEnd_2257052 := by
    simpa [prefixWord, tailWord_2257052, baseEnd_2257052] using wordTrace_append hprefix tailTrace_2257052
  have hstable : (prefixWord ++ tailWord_2257052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257052).length < 2 ^ (prefixWord ++ tailWord_2257052).sum := by decide
  have hdescent : baseEnd_2257052 < baseStart_2257052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257069 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_2257069 : Nat := 118140960795 + 2257069 * 2 ^ 59
def prefixEnd_2257069 : Nat := 4983230072969 + 3 ^ 40 * 2257069 * 2
def baseEnd_2257069 : Nat := 1158961267362934940857435

theorem tailTrace_2257069 : CollatzResearch.WordTrace tailWord_2257069 prefixEnd_2257069 1158961267362934940857435 := by
  unfold tailWord_2257069
  simp only [CollatzResearch.WordTrace]
  refine ⟨82322069460031964540942261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54881379640021309693961507 82322069460031964540942261)
  ·
    refine ⟨7717694011877996675713337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82322069460031964540942261 7717694011877996675713337)
    ·
      refine ⟨5788270508908497506785003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7717694011877996675713337 5788270508908497506785003)
      ·
        refine ⟨8682405763362746260177505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5788270508908497506785003 8682405763362746260177505)
        ·
          refine ⟨6511804322522059695133129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8682405763362746260177505 6511804322522059695133129)
          ·
            refine ⟨4883853241891544771349847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6511804322522059695133129 4883853241891544771349847)
            ·
              refine ⟨7325779862837317157024771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4883853241891544771349847 7325779862837317157024771)
              ·
                refine ⟨10988669794255975735537157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7325779862837317157024771 10988669794255975735537157)
                ·
                  refine ⟨2060375586422995450413217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10988669794255975735537157 2060375586422995450413217)
                  ·
                    refine ⟨1545281689817246587809913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060375586422995450413217 1545281689817246587809913)
                    ·
                      refine ⟨1158961267362934940857435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545281689817246587809913 1158961267362934940857435)
                      ·
                        rfl

theorem cell23_2257069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_2257069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257069 prefixEnd_2257069 := by exact prefixLift 2257069
  have htrace : WordTrace (prefixWord ++ tailWord_2257069) baseStart_2257069 baseEnd_2257069 := by
    simpa [prefixWord, tailWord_2257069, baseEnd_2257069] using wordTrace_append hprefix tailTrace_2257069
  have hstable : (prefixWord ++ tailWord_2257069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257069).length < 2 ^ (prefixWord ++ tailWord_2257069).sum := by decide
  have hdescent : baseEnd_2257069 < baseStart_2257069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257086 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_2257086 : Nat := 118140960795 + 2257086 * 2 ^ 59
def prefixEnd_2257086 : Nat := 4983230072969 + 3 ^ 40 * 2257086 * 2
def baseEnd_2257086 : Nat := 1158969996534061374344857

theorem tailTrace_2257086 : CollatzResearch.WordTrace tailWord_2257086 prefixEnd_2257086 1158969996534061374344857 := by
  unfold tailWord_2257086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10290336187621297055538889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54881793000646917629540741 10290336187621297055538889)
  ·
    refine ⟨7717752140715972791654167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10290336187621297055538889 7717752140715972791654167)
    ·
      refine ⟨11576628211073959187481251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7717752140715972791654167 11576628211073959187481251)
      ·
        refine ⟨17364942316610938781221877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11576628211073959187481251 17364942316610938781221877)
        ·
          refine ⟨1627963342182275510739551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17364942316610938781221877 1627963342182275510739551)
          ·
            refine ⟨2441945013273413266109327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627963342182275510739551 2441945013273413266109327)
            ·
              refine ⟨3662917519910119899163991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441945013273413266109327 3662917519910119899163991)
              ·
                refine ⟨5494376279865179848745987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662917519910119899163991 5494376279865179848745987)
                ·
                  refine ⟨8241564419797769773118981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5494376279865179848745987 8241564419797769773118981)
                  ·
                    refine ⟨1545293328712081832459809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8241564419797769773118981 1545293328712081832459809)
                    ·
                      refine ⟨1158969996534061374344857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545293328712081832459809 1158969996534061374344857)
                      ·
                        rfl

theorem cell23_2257086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_2257086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257086 prefixEnd_2257086 := by exact prefixLift 2257086
  have htrace : WordTrace (prefixWord ++ tailWord_2257086) baseStart_2257086 baseEnd_2257086 := by
    simpa [prefixWord, tailWord_2257086, baseEnd_2257086] using wordTrace_append hprefix tailTrace_2257086
  have hstable : (prefixWord ++ tailWord_2257086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257086).length < 2 ^ (prefixWord ++ tailWord_2257086).sum := by decide
  have hdescent : baseEnd_2257086 < baseStart_2257086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257088 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 1, 7]
def baseStart_2257088 : Nat := 118140960795 + 2257088 * 2 ^ 59
def prefixEnd_2257088 : Nat := 4983230072969 + 3 ^ 40 * 2257088 * 2
def baseEnd_2257088 : Nat := 386323674498456788839949

theorem tailTrace_2257088 : CollatzResearch.WordTrace tailWord_2257088 prefixEnd_2257088 386323674498456788839949 := by
  unfold tailWord_2257088
  simp only [CollatzResearch.WordTrace]
  refine ⟨41161381223481565392941959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54881841631308753857255945 41161381223481565392941959)
  ·
    refine ⟨61742071835222348089412939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41161381223481565392941959 61742071835222348089412939)
    ·
      refine ⟨92613107752833522134119409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61742071835222348089412939 92613107752833522134119409)
      ·
        refine ⟨69459830814625141600589557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92613107752833522134119409 69459830814625141600589557)
        ·
          refine ⟨6511859138871107025055271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69459830814625141600589557 6511859138871107025055271)
          ·
            refine ⟨9767788708306660537582907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6511859138871107025055271 9767788708306660537582907)
            ·
              refine ⟨14651683062459990806374361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9767788708306660537582907 14651683062459990806374361)
              ·
                refine ⟨10988762296844993104780771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14651683062459990806374361 10988762296844993104780771)
                ·
                  refine ⟨16483143445267489657171157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10988762296844993104780771 16483143445267489657171157)
                  ·
                    refine ⟨386323674498456788839949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16483143445267489657171157 386323674498456788839949)
                    ·
                      rfl

theorem cell23_2257088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_2257088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257088 prefixEnd_2257088 := by exact prefixLift 2257088
  have htrace : WordTrace (prefixWord ++ tailWord_2257088) baseStart_2257088 baseEnd_2257088 := by
    simpa [prefixWord, tailWord_2257088, baseEnd_2257088] using wordTrace_append hprefix tailTrace_2257088
  have hstable : (prefixWord ++ tailWord_2257088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257088).length < 2 ^ (prefixWord ++ tailWord_2257088).sum := by decide
  have hdescent : baseEnd_2257088 < baseStart_2257088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257109 : List Nat := [1, 3, 2, 4, 2, 2, 1, 3, 5]
def baseStart_2257109 : Nat := 118140960795 + 2257109 * 2 ^ 59
def prefixEnd_2257109 : Nat := 4983230072969 + 3 ^ 40 * 2257109 * 2
def baseEnd_2257109 : Nat := 128775756287679420484139

theorem tailTrace_2257109 : CollatzResearch.WordTrace tailWord_2257109 prefixEnd_2257109 128775756287679420484139 := by
  unfold tailWord_2257109
  simp only [CollatzResearch.WordTrace]
  refine ⟨82323528379887051372398381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54882352253258034248265587 82323528379887051372398381)
  ·
    refine ⟨30871323142457644264649393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82323528379887051372398381 30871323142457644264649393)
    ·
      refine ⟨23153492356843233198487045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30871323142457644264649393 23153492356843233198487045)
      ·
        refine ⟨4341279816908106224716321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23153492356843233198487045 4341279816908106224716321)
        ·
          refine ⟨3255959862681079668537241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4341279816908106224716321 3255959862681079668537241)
          ·
            refine ⟨2441969897010809751402931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3255959862681079668537241 2441969897010809751402931)
            ·
              refine ⟨3662954845516214627104397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441969897010809751402931 3662954845516214627104397)
              ·
                refine ⟨1373608067068580485164149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3662954845516214627104397 1373608067068580485164149)
                ·
                  refine ⟨128775756287679420484139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1373608067068580485164149 128775756287679420484139)
                  ·
                    rfl

theorem cell23_2257109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_2257109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257109 prefixEnd_2257109 := by exact prefixLift 2257109
  have htrace : WordTrace (prefixWord ++ tailWord_2257109) baseStart_2257109 baseEnd_2257109 := by
    simpa [prefixWord, tailWord_2257109, baseEnd_2257109] using wordTrace_append hprefix tailTrace_2257109
  have hstable : (prefixWord ++ tailWord_2257109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257109).length < 2 ^ (prefixWord ++ tailWord_2257109).sum := by decide
  have hdescent : baseEnd_2257109 < baseStart_2257109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257125 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2257125 : Nat := 118140960795 + 2257125 * 2 ^ 59
def prefixEnd_2257125 : Nat := 4983230072969 + 3 ^ 40 * 2257125 * 2
def baseEnd_2257125 : Nat := 1158990022279586721757177

theorem tailTrace_2257125 : CollatzResearch.WordTrace tailWord_2257125 prefixEnd_2257125 1158990022279586721757177 := by
  unfold tailWord_2257125
  simp only [CollatzResearch.WordTrace]
  refine ⟨82324111947829086104980829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54882741298552724069987219 82324111947829086104980829)
  ·
    refine ⟨30871541980435907289367811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82324111947829086104980829 30871541980435907289367811)
    ·
      refine ⟨46307312970653860934051717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30871541980435907289367811 46307312970653860934051717)
      ·
        refine ⟨8682621181997598925134697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46307312970653860934051717 8682621181997598925134697)
        ·
          refine ⟨6511965886498199193851023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8682621181997598925134697 6511965886498199193851023)
          ·
            refine ⟨9767948829747298790776535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6511965886498199193851023 9767948829747298790776535)
            ·
              refine ⟨14651923244620948186164803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9767948829747298790776535 14651923244620948186164803)
              ·
                refine ⟨21977884866931422279247205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14651923244620948186164803 21977884866931422279247205)
                ·
                  refine ⟨4120853412549641677358851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21977884866931422279247205 4120853412549641677358851)
                  ·
                    refine ⟨6181280118824462516038277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4120853412549641677358851 6181280118824462516038277)
                    ·
                      refine ⟨1158990022279586721757177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6181280118824462516038277 1158990022279586721757177)
                      ·
                        rfl

theorem cell23_2257125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2257125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257125 prefixEnd_2257125 := by exact prefixLift 2257125
  have htrace : WordTrace (prefixWord ++ tailWord_2257125) baseStart_2257125 baseEnd_2257125 := by
    simpa [prefixWord, tailWord_2257125, baseEnd_2257125] using wordTrace_append hprefix tailTrace_2257125
  have hstable : (prefixWord ++ tailWord_2257125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257125).length < 2 ^ (prefixWord ++ tailWord_2257125).sum := by decide
  have hdescent : baseEnd_2257125 < baseStart_2257125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257142 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_2257142 : Nat := 118140960795 + 2257142 * 2 ^ 59
def prefixEnd_2257142 : Nat := 4983230072969 + 3 ^ 40 * 2257142 * 2
def baseEnd_2257142 : Nat := 1158998751450713155244599

theorem tailTrace_2257142 : CollatzResearch.WordTrace tailWord_2257142 prefixEnd_2257142 1158998751450713155244599 := by
  unfold tailWord_2257142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5145295749297968625521855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54883154659178332005566453 5145295749297968625521855)
  ·
    refine ⟨7717943623946952938282783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5145295749297968625521855 7717943623946952938282783)
    ·
      refine ⟨11576915435920429407424175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7717943623946952938282783 11576915435920429407424175)
      ·
        refine ⟨17365373153880644111136263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11576915435920429407424175 17365373153880644111136263)
        ·
          refine ⟨26048059730820966166704395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17365373153880644111136263 26048059730820966166704395)
          ·
            refine ⟨39072089596231449250056593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26048059730820966166704395 39072089596231449250056593)
            ·
              refine ⟨29304067197173586937542445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39072089596231449250056593 29304067197173586937542445)
              ·
                refine ⟨10989025198940095101578417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29304067197173586937542445 10989025198940095101578417)
                ·
                  refine ⟨8241768899205071326183813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10989025198940095101578417 8241768899205071326183813)
                  ·
                    refine ⟨1545331668600950873659465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8241768899205071326183813 1545331668600950873659465)
                    ·
                      refine ⟨1158998751450713155244599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545331668600950873659465 1158998751450713155244599)
                      ·
                        rfl

theorem cell23_2257142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_2257142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257142 prefixEnd_2257142 := by exact prefixLift 2257142
  have htrace : WordTrace (prefixWord ++ tailWord_2257142) baseStart_2257142 baseEnd_2257142 := by
    simpa [prefixWord, tailWord_2257142, baseEnd_2257142] using wordTrace_append hprefix tailTrace_2257142
  have hstable : (prefixWord ++ tailWord_2257142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257142).length < 2 ^ (prefixWord ++ tailWord_2257142).sum := by decide
  have hdescent : baseEnd_2257142 < baseStart_2257142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257159 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2257159 : Nat := 118140960795 + 2257159 * 2 ^ 59
def prefixEnd_2257159 : Nat := 4983230072969 + 3 ^ 40 * 2257159 * 2
def baseEnd_2257159 : Nat := 1159007480621839588732021

theorem tailTrace_2257159 : CollatzResearch.WordTrace tailWord_2257159 prefixEnd_2257159 1159007480621839588732021 := by
  unfold tailWord_2257159
  simp only [CollatzResearch.WordTrace]
  refine ⟨82325352029705909911718531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54883568019803939941145687 82325352029705909911718531)
  ·
    refine ⟨123488028044558864867577797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82325352029705909911718531 123488028044558864867577797)
    ·
      refine ⟨23154005258354787162670837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123488028044558864867577797 23154005258354787162670837)
      ·
        refine ⟨2170687992970761296500391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23154005258354787162670837 2170687992970761296500391)
        ·
          refine ⟨3256031989456141944750587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2170687992970761296500391 3256031989456141944750587)
          ·
            refine ⟨4884047984184212917125881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256031989456141944750587 4884047984184212917125881)
            ·
              refine ⟨3663035988138159687844411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4884047984184212917125881 3663035988138159687844411)
              ·
                refine ⟨5494553982207239531766617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3663035988138159687844411 5494553982207239531766617)
                ·
                  refine ⟨4120915486655429648824963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5494553982207239531766617 4120915486655429648824963)
                  ·
                    refine ⟨6181373229983144473237445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4120915486655429648824963 6181373229983144473237445)
                    ·
                      refine ⟨1159007480621839588732021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6181373229983144473237445 1159007480621839588732021)
                      ·
                        rfl

theorem cell23_2257159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2257159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257159 prefixEnd_2257159 := by exact prefixLift 2257159
  have htrace : WordTrace (prefixWord ++ tailWord_2257159) baseStart_2257159 baseEnd_2257159 := by
    simpa [prefixWord, tailWord_2257159, baseEnd_2257159] using wordTrace_append hprefix tailTrace_2257159
  have hstable : (prefixWord ++ tailWord_2257159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257159).length < 2 ^ (prefixWord ++ tailWord_2257159).sum := by decide
  have hdescent : baseEnd_2257159 < baseStart_2257159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257186 : List Nat := [3, 3, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2257186 : Nat := 118140960795 + 2257186 * 2 ^ 59
def prefixEnd_2257186 : Nat := 4983230072969 + 3 ^ 40 * 2257186 * 2
def baseEnd_2257186 : Nat := 386340448199836994364799

theorem tailTrace_2257186 : CollatzResearch.WordTrace tailWord_2257186 prefixEnd_2257186 386340448199836994364799 := by
  unfold tailWord_2257186
  simp only [CollatzResearch.WordTrace]
  refine ⟨20581584200152023380737853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54884224533738729015300941 20581584200152023380737853)
  ·
    refine ⟨7718094075057008767776695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20581584200152023380737853 7718094075057008767776695)
    ·
      refine ⟨11577141112585513151665043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7718094075057008767776695 11577141112585513151665043)
      ·
        refine ⟨17365711668878269727497565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11577141112585513151665043 17365711668878269727497565)
        ·
          refine ⟨6512141875829351147811587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17365711668878269727497565 6512141875829351147811587)
          ·
            refine ⟨9768212813744026721717381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6512141875829351147811587 9768212813744026721717381)
            ·
              refine ⟨1831539902577005010322009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9768212813744026721717381 1831539902577005010322009)
              ·
                refine ⟨1373654926932753757741507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1831539902577005010322009 1373654926932753757741507)
                ·
                  refine ⟨2060482390399130636612261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373654926932753757741507 2060482390399130636612261)
                  ·
                    refine ⟨386340448199836994364799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2060482390399130636612261 386340448199836994364799)
                    ·
                      rfl

theorem cell23_2257186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2257186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257186 prefixEnd_2257186 := by exact prefixLift 2257186
  have htrace : WordTrace (prefixWord ++ tailWord_2257186) baseStart_2257186 baseEnd_2257186 := by
    simpa [prefixWord, tailWord_2257186, baseEnd_2257186] using wordTrace_append hprefix tailTrace_2257186
  have hstable : (prefixWord ++ tailWord_2257186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257186).length < 2 ^ (prefixWord ++ tailWord_2257186).sum := by decide
  have hdescent : baseEnd_2257186 < baseStart_2257186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257209 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2257209 : Nat := 118140960795 + 2257209 * 2 ^ 59
def prefixEnd_2257209 : Nat := 4983230072969 + 3 ^ 40 * 2257209 * 2
def baseEnd_2257209 : Nat := 1159033154654564393106791

theorem tailTrace_2257209 : CollatzResearch.WordTrace tailWord_2257209 prefixEnd_2257209 1159033154654564393106791 := by
  unfold tailWord_2257209
  simp only [CollatzResearch.WordTrace]
  refine ⟨82327175679524768451038681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54884783786349845634025787 82327175679524768451038681)
  ·
    refine ⟨61745381759643576338279011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82327175679524768451038681 61745381759643576338279011)
    ·
      refine ⟨92618072639465364507418517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61745381759643576338279011 92618072639465364507418517)
      ·
        refine ⟨4341472154974938961285243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92618072639465364507418517 4341472154974938961285243)
        ·
          refine ⟨6512208232462408441927865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4341472154974938961285243 6512208232462408441927865)
          ·
            refine ⟨4884156174346806331445899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6512208232462408441927865 4884156174346806331445899)
            ·
              refine ⟨7326234261520209497168849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884156174346806331445899 7326234261520209497168849)
              ·
                refine ⟨5494675696140157122876637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7326234261520209497168849 5494675696140157122876637)
                ·
                  refine ⟨2060503386052558921078739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5494675696140157122876637 2060503386052558921078739)
                  ·
                    refine ⟨3090755079078838381618109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2060503386052558921078739 3090755079078838381618109)
                    ·
                      refine ⟨1159033154654564393106791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3090755079078838381618109 1159033154654564393106791)
                      ·
                        rfl

theorem cell23_2257209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2257209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257209 prefixEnd_2257209 := by exact prefixLift 2257209
  have htrace : WordTrace (prefixWord ++ tailWord_2257209) baseStart_2257209 baseEnd_2257209 := by
    simpa [prefixWord, tailWord_2257209, baseEnd_2257209] using wordTrace_append hprefix tailTrace_2257209
  have hstable : (prefixWord ++ tailWord_2257209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257209).length < 2 ^ (prefixWord ++ tailWord_2257209).sum := by decide
  have hdescent : baseEnd_2257209 < baseStart_2257209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257215 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_2257215 : Nat := 118140960795 + 2257215 * 2 ^ 59
def prefixEnd_2257215 : Nat := 4983230072969 + 3 ^ 40 * 2257215 * 2
def baseEnd_2257215 : Nat := 1159036235538491369631763

theorem tailTrace_2257215 : CollatzResearch.WordTrace tailWord_2257215 prefixEnd_2257215 1159036235538491369631763 := by
  unfold tailWord_2257215
  simp only [CollatzResearch.WordTrace]
  refine ⟨82327394517503031475757099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54884929678335354317171399 82327394517503031475757099)
  ·
    refine ⟨123491091776254547213635649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82327394517503031475757099 123491091776254547213635649)
    ·
      refine ⟨92618318832190910410226737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123491091776254547213635649 92618318832190910410226737)
      ·
        refine ⟨69463739124143182807670053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92618318832190910410226737 69463739124143182807670053)
        ·
          refine ⟨13024451085776846776438135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69463739124143182807670053 13024451085776846776438135)
          ·
            refine ⟨19536676628665270164657203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13024451085776846776438135 19536676628665270164657203)
            ·
              refine ⟨29305014942997905246985805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19536676628665270164657203 29305014942997905246985805)
              ·
                refine ⟨10989380603624214467619677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29305014942997905246985805 10989380603624214467619677)
                ·
                  refine ⟨4121017726359080425357379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10989380603624214467619677 4121017726359080425357379)
                  ·
                    refine ⟨6181526589538620638036069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4121017726359080425357379 6181526589538620638036069)
                    ·
                      refine ⟨1159036235538491369631763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6181526589538620638036069 1159036235538491369631763)
                      ·
                        rfl

theorem cell23_2257215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_2257215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257215 prefixEnd_2257215 := by exact prefixLift 2257215
  have htrace : WordTrace (prefixWord ++ tailWord_2257215) baseStart_2257215 baseEnd_2257215 := by
    simpa [prefixWord, tailWord_2257215, baseEnd_2257215] using wordTrace_append hprefix tailTrace_2257215
  have hstable : (prefixWord ++ tailWord_2257215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257215).length < 2 ^ (prefixWord ++ tailWord_2257215).sum := by decide
  have hdescent : baseEnd_2257215 < baseStart_2257215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257225 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 4, 4]
def baseStart_2257225 : Nat := 118140960795 + 2257225 * 2 ^ 59
def prefixEnd_2257225 : Nat := 4983230072969 + 3 ^ 40 * 2257225 * 2
def baseEnd_2257225 : Nat := 386347123448345443502239

theorem tailTrace_2257225 : CollatzResearch.WordTrace tailWord_2257225 prefixEnd_2257225 386347123448345443502239 := by
  unfold tailWord_2257225
  simp only [CollatzResearch.WordTrace]
  refine ⟨82327759247466803183621129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54885172831644535455747419 82327759247466803183621129)
  ·
    refine ⟨61745819435600102387715847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82327759247466803183621129 61745819435600102387715847)
    ·
      refine ⟨92618729153400153581573771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61745819435600102387715847 92618729153400153581573771)
      ·
        refine ⟨138928093730100230372360657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92618729153400153581573771 138928093730100230372360657)
        ·
          refine ⟨104196070297575172779270493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138928093730100230372360657 104196070297575172779270493)
          ·
            refine ⟨39073526361590689792226435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104196070297575172779270493 39073526361590689792226435)
            ·
              refine ⟨58610289542386034688339653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39073526361590689792226435 58610289542386034688339653)
              ·
                refine ⟨10989429289197381504063685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58610289542386034688339653 10989429289197381504063685)
                ·
                  refine ⟨2060517991724509032011941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10989429289197381504063685 2060517991724509032011941)
                  ·
                    refine ⟨386347123448345443502239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2060517991724509032011941 386347123448345443502239)
                    ·
                      rfl

theorem cell23_2257225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 4].length) (baseStart_2257225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257225 prefixEnd_2257225 := by exact prefixLift 2257225
  have htrace : WordTrace (prefixWord ++ tailWord_2257225) baseStart_2257225 baseEnd_2257225 := by
    simpa [prefixWord, tailWord_2257225, baseEnd_2257225] using wordTrace_append hprefix tailTrace_2257225
  have hstable : (prefixWord ++ tailWord_2257225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257225).length < 2 ^ (prefixWord ++ tailWord_2257225).sum := by decide
  have hdescent : baseEnd_2257225 < baseStart_2257225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257232 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 4]
def baseStart_2257232 : Nat := 118140960795 + 2257232 * 2 ^ 59
def prefixEnd_2257232 : Nat := 4983230072969 + 3 ^ 40 * 2257232 * 2
def baseEnd_2257232 : Nat := 1159044964709617803119185

theorem tailTrace_2257232 : CollatzResearch.WordTrace tailWord_2257232 prefixEnd_2257232 1159044964709617803119185 := by
  unfold tailWord_2257232
  simp only [CollatzResearch.WordTrace]
  refine ⟨41164007279220721689562975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54885343038960962252750633 41164007279220721689562975)
  ·
    refine ⟨61746010918831082534344463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41164007279220721689562975 61746010918831082534344463)
    ·
      refine ⟨92619016378246623801516695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61746010918831082534344463 92619016378246623801516695)
      ·
        refine ⟨138928524567369935702275043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92619016378246623801516695 138928524567369935702275043)
        ·
          refine ⟨208392786851054903553412565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138928524567369935702275043 208392786851054903553412565)
          ·
            refine ⟨4884205941821599302033107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 208392786851054903553412565 4884205941821599302033107)
            ·
              refine ⟨7326308912732398953049661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884205941821599302033107 7326308912732398953049661)
              ·
                refine ⟨2747365842274649607393623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7326308912732398953049661 2747365842274649607393623)
                ·
                  refine ⟨4121048763411974411090435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747365842274649607393623 4121048763411974411090435)
                  ·
                    refine ⟨6181573145117961616635653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4121048763411974411090435 6181573145117961616635653)
                    ·
                      refine ⟨1159044964709617803119185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6181573145117961616635653 1159044964709617803119185)
                      ·
                        rfl

theorem cell23_2257232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 4].length) (baseStart_2257232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257232 prefixEnd_2257232 := by exact prefixLift 2257232
  have htrace : WordTrace (prefixWord ++ tailWord_2257232) baseStart_2257232 baseEnd_2257232 := by
    simpa [prefixWord, tailWord_2257232, baseEnd_2257232] using wordTrace_append hprefix tailTrace_2257232
  have hstable : (prefixWord ++ tailWord_2257232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257232).length < 2 ^ (prefixWord ++ tailWord_2257232).sum := by decide
  have hdescent : baseEnd_2257232 < baseStart_2257232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257235 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 3]
def baseStart_2257235 : Nat := 118140960795 + 2257235 * 2 ^ 59
def prefixEnd_2257235 : Nat := 4983230072969 + 3 ^ 40 * 2257235 * 2
def baseEnd_2257235 : Nat := 1159046505151581291381671

theorem tailTrace_2257235 : CollatzResearch.WordTrace tailWord_2257235 prefixEnd_2257235 1159046505151581291381671 := by
  unfold tailWord_2257235
  simp only [CollatzResearch.WordTrace]
  refine ⟨82328123977430574891485159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54885415984953716594323439 82328123977430574891485159)
  ·
    refine ⟨123492185966145862337227739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82328123977430574891485159 123492185966145862337227739)
    ·
      refine ⟨185238278949218793505841609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123492185966145862337227739 185238278949218793505841609)
      ·
        refine ⟨138928709211914095129381207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185238278949218793505841609 138928709211914095129381207)
        ·
          refine ⟨208393063817871142694071811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138928709211914095129381207 208393063817871142694071811)
          ·
            refine ⟨312589595726806714041107717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208393063817871142694071811 312589595726806714041107717)
            ·
              refine ⟨58610549198776258882707697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312589595726806714041107717 58610549198776258882707697)
              ·
                refine ⟨43957911899082194162030773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58610549198776258882707697 43957911899082194162030773)
                ·
                  refine ⟨4121054240538955702690385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43957911899082194162030773 4121054240538955702690385)
                  ·
                    refine ⟨3090790680404216777017789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4121054240538955702690385 3090790680404216777017789)
                    ·
                      refine ⟨1159046505151581291381671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3090790680404216777017789 1159046505151581291381671)
                      ·
                        rfl

theorem cell23_2257235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_2257235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257235 prefixEnd_2257235 := by exact prefixLift 2257235
  have htrace : WordTrace (prefixWord ++ tailWord_2257235) baseStart_2257235 baseEnd_2257235 := by
    simpa [prefixWord, tailWord_2257235, baseEnd_2257235] using wordTrace_append hprefix tailTrace_2257235
  have hstable : (prefixWord ++ tailWord_2257235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257235).length < 2 ^ (prefixWord ++ tailWord_2257235).sum := by decide
  have hdescent : baseEnd_2257235 < baseStart_2257235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257269 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2257269 : Nat := 118140960795 + 2257269 * 2 ^ 59
def prefixEnd_2257269 : Nat := 4983230072969 + 3 ^ 40 * 2257269 * 2
def baseEnd_2257269 : Nat := 1159063963493834158356515

theorem tailTrace_2257269 : CollatzResearch.WordTrace tailWord_2257269 prefixEnd_2257269 1159063963493834158356515 := by
  unfold tailWord_2257269
  simp only [CollatzResearch.WordTrace]
  refine ⟨82329364059307398698222861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54886242706204932465481907 82329364059307398698222861)
  ·
    refine ⟨30873511522240274511833573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82329364059307398698222861 30873511522240274511833573)
    ·
      refine ⟨5788783410420051470968795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30873511522240274511833573 5788783410420051470968795)
      ·
        refine ⟨8683175115630077206453193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5788783410420051470968795 8683175115630077206453193)
        ·
          refine ⟨6512381336722557904839895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8683175115630077206453193 6512381336722557904839895)
          ·
            refine ⟨9768572005083836857259843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6512381336722557904839895 9768572005083836857259843)
            ·
              refine ⟨14652858007625755285889765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9768572005083836857259843 14652858007625755285889765)
              ·
                refine ⟨2747410876429829116104331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14652858007625755285889765 2747410876429829116104331)
                ·
                  refine ⟨4121116314644743674156497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747410876429829116104331 4121116314644743674156497)
                  ·
                    refine ⟨3090837235983557755617373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4121116314644743674156497 3090837235983557755617373)
                    ·
                      refine ⟨1159063963493834158356515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3090837235983557755617373 1159063963493834158356515)
                      ·
                        rfl

theorem cell23_2257269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2257269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257269 prefixEnd_2257269 := by exact prefixLift 2257269
  have htrace : WordTrace (prefixWord ++ tailWord_2257269) baseStart_2257269 baseEnd_2257269 := by
    simpa [prefixWord, tailWord_2257269, baseEnd_2257269] using wordTrace_append hprefix tailTrace_2257269
  have hstable : (prefixWord ++ tailWord_2257269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257269).length < 2 ^ (prefixWord ++ tailWord_2257269).sum := by decide
  have hdescent : baseEnd_2257269 < baseStart_2257269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257300 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_2257300 : Nat := 118140960795 + 2257300 * 2 ^ 59
def prefixEnd_2257300 : Nat := 4983230072969 + 3 ^ 40 * 2257300 * 2
def baseEnd_2257300 : Nat := 1159079881394123537068873

theorem tailTrace_2257300 : CollatzResearch.WordTrace tailWord_2257300 prefixEnd_2257300 1159079881394123537068873 := by
  unfold tailWord_2257300
  simp only [CollatzResearch.WordTrace]
  refine ⟨41165247361097545496300677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54886996481463393995067569 41165247361097545496300677)
  ·
    refine ⟨7718483880205789780556377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41165247361097545496300677 7718483880205789780556377)
    ·
      refine ⟨5788862910154342335417283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7718483880205789780556377 5788862910154342335417283)
      ·
        refine ⟨8683294365231513503125925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5788862910154342335417283 8683294365231513503125925)
        ·
          refine ⟨1628117693480908781836111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8683294365231513503125925 1628117693480908781836111)
          ·
            refine ⟨2442176540221363172754167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628117693480908781836111 2442176540221363172754167)
            ·
              refine ⟨3663264810332044759131251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442176540221363172754167 3663264810332044759131251)
              ·
                refine ⟨5494897215498067138696877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3663264810332044759131251 5494897215498067138696877)
                ·
                  refine ⟨2060586455811775177011329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5494897215498067138696877 2060586455811775177011329)
                  ·
                    refine ⟨1545439841858831382758497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060586455811775177011329 1545439841858831382758497)
                    ·
                      refine ⟨1159079881394123537068873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545439841858831382758497 1159079881394123537068873)
                      ·
                        rfl

theorem cell23_2257300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_2257300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257300 prefixEnd_2257300 := by exact prefixLift 2257300
  have htrace : WordTrace (prefixWord ++ tailWord_2257300) baseStart_2257300 baseEnd_2257300 := by
    simpa [prefixWord, tailWord_2257300, baseEnd_2257300] using wordTrace_append hprefix tailTrace_2257300
  have hstable : (prefixWord ++ tailWord_2257300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257300).length < 2 ^ (prefixWord ++ tailWord_2257300).sum := by decide
  have hdescent : baseEnd_2257300 < baseStart_2257300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257305 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_2257305 : Nat := 118140960795 + 2257305 * 2 ^ 59
def prefixEnd_2257305 : Nat := 4983230072969 + 3 ^ 40 * 2257305 * 2
def baseEnd_2257305 : Nat := 1159082448797396017506349

theorem tailTrace_2257305 : CollatzResearch.WordTrace tailWord_2257305 prefixEnd_2257305 1159082448797396017506349 := by
  unfold tailWord_2257305
  simp only [CollatzResearch.WordTrace]
  refine ⟨82330677087176976846533369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54887118058117984564355579 82330677087176976846533369)
  ·
    refine ⟨61748007815382732634900027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82330677087176976846533369 61748007815382732634900027)
    ·
      refine ⟨92622011723074098952350041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61748007815382732634900027 92622011723074098952350041)
      ·
        refine ⟨69466508792305574214262531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92622011723074098952350041 69466508792305574214262531)
        ·
          refine ⟨104199763188458361321393797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69466508792305574214262531 104199763188458361321393797)
          ·
            refine ⟨19537455597835942747761337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104199763188458361321393797 19537455597835942747761337)
            ·
              refine ⟨14653091698376957060821003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19537455597835942747761337 14653091698376957060821003)
              ·
                refine ⟨21979637547565435591231505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14653091698376957060821003 21979637547565435591231505)
                ·
                  refine ⟨16484728160674076693423629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21979637547565435591231505 16484728160674076693423629)
                  ·
                    refine ⟨6181773060252778760033861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16484728160674076693423629 6181773060252778760033861)
                    ·
                      refine ⟨1159082448797396017506349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6181773060252778760033861 1159082448797396017506349)
                      ·
                        rfl

theorem cell23_2257305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_2257305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257305 prefixEnd_2257305 := by exact prefixLift 2257305
  have htrace : WordTrace (prefixWord ++ tailWord_2257305) baseStart_2257305 baseEnd_2257305 := by
    simpa [prefixWord, tailWord_2257305, baseEnd_2257305] using wordTrace_append hprefix tailTrace_2257305
  have hstable : (prefixWord ++ tailWord_2257305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257305).length < 2 ^ (prefixWord ++ tailWord_2257305).sum := by decide
  have hdescent : baseEnd_2257305 < baseStart_2257305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257316 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_2257316 : Nat := 118140960795 + 2257316 * 2 ^ 59
def prefixEnd_2257316 : Nat := 4983230072969 + 3 ^ 40 * 2257316 * 2
def baseEnd_2257316 : Nat := 1159088097084595474468799

theorem tailTrace_2257316 : CollatzResearch.WordTrace tailWord_2257316 prefixEnd_2257316 1159088097084595474468799 := by
  unfold tailWord_2257316
  simp only [CollatzResearch.WordTrace]
  refine ⟨41165539145068562862591901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54887385526758083816789201 41165539145068562862591901)
  ·
    refine ⟨15437077179400711073471963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41165539145068562862591901 15437077179400711073471963)
    ·
      refine ⟨23155615769101066610207945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15437077179400711073471963 23155615769101066610207945)
      ·
        refine ⟨17366711826825799957655959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23155615769101066610207945 17366711826825799957655959)
        ·
          refine ⟨26050067740238699936483939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17366711826825799957655959 26050067740238699936483939)
          ·
            refine ⟨39075101610358049904725909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26050067740238699936483939 39075101610358049904725909)
            ·
              refine ⟨1831645387985533589284027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39075101610358049904725909 1831645387985533589284027)
              ·
                refine ⟨2747468081978300383926041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1831645387985533589284027 2747468081978300383926041)
                ·
                  refine ⟨2060601061483725287944531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2747468081978300383926041 2060601061483725287944531)
                  ·
                    refine ⟨3090901592225587931916797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2060601061483725287944531 3090901592225587931916797)
                    ·
                      refine ⟨1159088097084595474468799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3090901592225587931916797 1159088097084595474468799)
                      ·
                        rfl

theorem cell23_2257316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_2257316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257316 prefixEnd_2257316 := by exact prefixLift 2257316
  have htrace : WordTrace (prefixWord ++ tailWord_2257316) baseStart_2257316 baseEnd_2257316 := by
    simpa [prefixWord, tailWord_2257316, baseEnd_2257316] using wordTrace_append hprefix tailTrace_2257316
  have hstable : (prefixWord ++ tailWord_2257316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257316).length < 2 ^ (prefixWord ++ tailWord_2257316).sum := by decide
  have hdescent : baseEnd_2257316 < baseStart_2257316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257342 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2257342 : Nat := 118140960795 + 2257342 * 2 ^ 59
def prefixEnd_2257342 : Nat := 4983230072969 + 3 ^ 40 * 2257342 * 2
def baseEnd_2257342 : Nat := 1159101447581612372743679

theorem tailTrace_2257342 : CollatzResearch.WordTrace tailWord_2257342 prefixEnd_2257342 1159101447581612372743679 := by
  unfold tailWord_2257342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10291503323505366520703785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54888017725361954777086853 10291503323505366520703785)
  ·
    refine ⟨7718627492629024890527839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10291503323505366520703785 7718627492629024890527839)
    ·
      refine ⟨11577941238943537335791759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7718627492629024890527839 11577941238943537335791759)
      ·
        refine ⟨17366911858415306003687639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11577941238943537335791759 17366911858415306003687639)
        ·
          refine ⟨26050367787622959005531459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17366911858415306003687639 26050367787622959005531459)
          ·
            refine ⟨39075551681434438508297189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26050367787622959005531459 39075551681434438508297189)
            ·
              refine ⟨7326665940268957220305723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39075551681434438508297189 7326665940268957220305723)
              ·
                refine ⟨10989998910403435830458585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7326665940268957220305723 10989998910403435830458585)
                ·
                  refine ⟨8242499182802576872843939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10989998910403435830458585 8242499182802576872843939)
                  ·
                    refine ⟨12363748774203865309265909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8242499182802576872843939 12363748774203865309265909)
                    ·
                      refine ⟨1159101447581612372743679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12363748774203865309265909 1159101447581612372743679)
                      ·
                        rfl

theorem cell23_2257342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2257342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257342 prefixEnd_2257342 := by exact prefixLift 2257342
  have htrace : WordTrace (prefixWord ++ tailWord_2257342) baseStart_2257342 baseEnd_2257342 := by
    simpa [prefixWord, tailWord_2257342, baseEnd_2257342] using wordTrace_append hprefix tailTrace_2257342
  have hstable : (prefixWord ++ tailWord_2257342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257342).length < 2 ^ (prefixWord ++ tailWord_2257342).sum := by decide
  have hdescent : baseEnd_2257342 < baseStart_2257342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257385 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_2257385 : Nat := 118140960795 + 2257385 * 2 ^ 59
def prefixEnd_2257385 : Nat := 4983230072969 + 3 ^ 40 * 2257385 * 2
def baseEnd_2257385 : Nat := 1159123527249755704505981

theorem tailTrace_2257385 : CollatzResearch.WordTrace tailWord_2257385 prefixEnd_2257385 1159123527249755704505981 := by
  unfold tailWord_2257385
  simp only [CollatzResearch.WordTrace]
  refine ⟨82333594926887150509445609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54889063284591433672963739 82333594926887150509445609)
  ·
    refine ⟨61750196195165362882084207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82333594926887150509445609 61750196195165362882084207)
    ·
      refine ⟨92625294292748044323126311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61750196195165362882084207 92625294292748044323126311)
      ·
        refine ⟨138937941439122066484689467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92625294292748044323126311 138937941439122066484689467)
        ·
          refine ⟨208406912158683099727034201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138937941439122066484689467 208406912158683099727034201)
          ·
            refine ⟨156305184119012324795275651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208406912158683099727034201 156305184119012324795275651)
            ·
              refine ⟨234457776178518487192913477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156305184119012324795275651 234457776178518487192913477)
              ·
                refine ⟨43960833033472216348671277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234457776178518487192913477 43960833033472216348671277)
                ·
                  refine ⟨16485312387552081130751729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43960833033472216348671277 16485312387552081130751729)
                  ·
                    refine ⟨12363984290664060848063797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16485312387552081130751729 12363984290664060848063797)
                    ·
                      refine ⟨1159123527249755704505981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12363984290664060848063797 1159123527249755704505981)
                      ·
                        rfl

theorem cell23_2257385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_2257385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257385 prefixEnd_2257385 := by exact prefixLift 2257385
  have htrace : WordTrace (prefixWord ++ tailWord_2257385) baseStart_2257385 baseEnd_2257385 := by
    simpa [prefixWord, tailWord_2257385, baseEnd_2257385] using wordTrace_append hprefix tailTrace_2257385
  have hstable : (prefixWord ++ tailWord_2257385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257385).length < 2 ^ (prefixWord ++ tailWord_2257385).sum := by decide
  have hdescent : baseEnd_2257385 < baseStart_2257385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257429 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_2257429 : Nat := 118140960795 + 2257429 * 2 ^ 59
def prefixEnd_2257429 : Nat := 4983230072969 + 3 ^ 40 * 2257429 * 2
def baseEnd_2257429 : Nat := 1159146120398553532355779

theorem tailTrace_2257429 : CollatzResearch.WordTrace tailWord_2257429 prefixEnd_2257429 1159146120398553532355779 := by
  unfold tailWord_2257429
  simp only [CollatzResearch.WordTrace]
  refine ⟨82335199738727746024047341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54890133159151830682698227 82335199738727746024047341)
  ·
    refine ⟨30875699902022904759017753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82335199738727746024047341 30875699902022904759017753)
    ·
      refine ⟨23156774926517178569263315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30875699902022904759017753 23156774926517178569263315)
      ·
        refine ⟨34735162389775767853894973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23156774926517178569263315 34735162389775767853894973)
        ·
          refine ⟨13025685896165912945210615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34735162389775767853894973 13025685896165912945210615)
          ·
            refine ⟨19538528844248869417815923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13025685896165912945210615 19538528844248869417815923)
            ·
              refine ⟨29307793266373304126723885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19538528844248869417815923 29307793266373304126723885)
              ·
                refine ⟨10990422474889989047521457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29307793266373304126723885 10990422474889989047521457)
                ·
                  refine ⟨8242816856167491785641093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10990422474889989047521457 8242816856167491785641093)
                  ·
                    refine ⟨1545528160531404709807705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8242816856167491785641093 1545528160531404709807705)
                    ·
                      refine ⟨1159146120398553532355779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545528160531404709807705 1159146120398553532355779)
                      ·
                        rfl

theorem cell23_2257429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_2257429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257429 prefixEnd_2257429 := by exact prefixLift 2257429
  have htrace : WordTrace (prefixWord ++ tailWord_2257429) baseStart_2257429 baseEnd_2257429 := by
    simpa [prefixWord, tailWord_2257429, baseEnd_2257429] using wordTrace_append hprefix tailTrace_2257429
  have hstable : (prefixWord ++ tailWord_2257429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257429).length < 2 ^ (prefixWord ++ tailWord_2257429).sum := by decide
  have hdescent : baseEnd_2257429 < baseStart_2257429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257442 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2257442 : Nat := 118140960795 + 2257442 * 2 ^ 59
def prefixEnd_2257442 : Nat := 4983230072969 + 3 ^ 40 * 2257442 * 2
def baseEnd_2257442 : Nat := 1159152795647061981493219

theorem tailTrace_2257442 : CollatzResearch.WordTrace tailWord_2257442 prefixEnd_2257442 1159152795647061981493219 := by
  unfold tailWord_2257442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20583918471920162311067645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54890449258453766162847053 20583918471920162311067645)
  ·
    refine ⟨7718969426970060866650367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20583918471920162311067645 7718969426970060866650367)
    ·
      refine ⟨11578454140455091299975551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7718969426970060866650367 11578454140455091299975551)
      ·
        refine ⟨17367681210682636949963327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11578454140455091299975551 17367681210682636949963327)
        ·
          refine ⟨26051521816023955424944991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17367681210682636949963327 26051521816023955424944991)
          ·
            refine ⟨39077282724035933137417487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26051521816023955424944991 39077282724035933137417487)
            ·
              refine ⟨58615924086053899706126231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39077282724035933137417487 58615924086053899706126231)
              ·
                refine ⟨87923886129080849559189347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58615924086053899706126231 87923886129080849559189347)
                ·
                  refine ⟨131885829193621274338784021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87923886129080849559189347 131885829193621274338784021)
                  ·
                    refine ⟨6182148243450997234630501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 131885829193621274338784021 6182148243450997234630501)
                    ·
                      refine ⟨1159152795647061981493219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6182148243450997234630501 1159152795647061981493219)
                      ·
                        rfl

theorem cell23_2257442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2257442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257442 prefixEnd_2257442 := by exact prefixLift 2257442
  have htrace : WordTrace (prefixWord ++ tailWord_2257442) baseStart_2257442 baseEnd_2257442 := by
    simpa [prefixWord, tailWord_2257442, baseEnd_2257442] using wordTrace_append hprefix tailTrace_2257442
  have hstable : (prefixWord ++ tailWord_2257442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257442).length < 2 ^ (prefixWord ++ tailWord_2257442).sum := by decide
  have hdescent : baseEnd_2257442 < baseStart_2257442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257456 : List Nat := [2, 1, 1, 1, 2, 3, 5, 3, 1, 4]
def baseStart_2257456 : Nat := 118140960795 + 2257456 * 2 ^ 59
def prefixEnd_2257456 : Nat := 4983230072969 + 3 ^ 40 * 2257456 * 2
def baseEnd_2257456 : Nat := 386386661458741642239385

theorem tailTrace_2257456 : CollatzResearch.WordTrace tailWord_2257456 prefixEnd_2257456 386386661458741642239385 := by
  unfold tailWord_2257456
  simp only [CollatzResearch.WordTrace]
  refine ⟨41168092254814964817640111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54890789673086619756853481 41168092254814964817640111)
  ·
    refine ⟨61752138382222447226460167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41168092254814964817640111 61752138382222447226460167)
    ·
      refine ⟨92628207573333670839690251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61752138382222447226460167 92628207573333670839690251)
      ·
        refine ⟨138942311360000506259535377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92628207573333670839690251 138942311360000506259535377)
        ·
          refine ⟨104206733520000379694651533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138942311360000506259535377 104206733520000379694651533)
          ·
            refine ⟨39077525070000142385494325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104206733520000379694651533 39077525070000142385494325)
            ·
              refine ⟨3663517975312513348640093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39077525070000142385494325 3663517975312513348640093)
              ·
                refine ⟨1373819240742192505740035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3663517975312513348640093 1373819240742192505740035)
                ·
                  refine ⟨2060728861113288758610053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373819240742192505740035 2060728861113288758610053)
                  ·
                    refine ⟨386386661458741642239385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2060728861113288758610053 386386661458741642239385)
                    ·
                      rfl

theorem cell23_2257456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 4].length) (baseStart_2257456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257456 prefixEnd_2257456 := by exact prefixLift 2257456
  have htrace : WordTrace (prefixWord ++ tailWord_2257456) baseStart_2257456 baseEnd_2257456 := by
    simpa [prefixWord, tailWord_2257456, baseEnd_2257456] using wordTrace_append hprefix tailTrace_2257456
  have hstable : (prefixWord ++ tailWord_2257456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257456).length < 2 ^ (prefixWord ++ tailWord_2257456).sum := by decide
  have hdescent : baseEnd_2257456 < baseStart_2257456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257519 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 4]
def baseStart_2257519 : Nat := 118140960795 + 2257519 * 2 ^ 59
def prefixEnd_2257519 : Nat := 4983230072969 + 3 ^ 40 * 2257519 * 2
def baseEnd_2257519 : Nat := 1159192333657458180230365

theorem tailTrace_2257519 : CollatzResearch.WordTrace tailWord_2257519 prefixEnd_2257519 1159192333657458180230365 := by
  unfold tailWord_2257519
  simp only [CollatzResearch.WordTrace]
  refine ⟨82338482308401691394823611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54892321538934460929882407 82338482308401691394823611)
  ·
    refine ⟨123507723462602537092235417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82338482308401691394823611 123507723462602537092235417)
    ·
      refine ⟨92630792596951902819176563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123507723462602537092235417 92630792596951902819176563)
      ·
        refine ⟨138946188895427854228764845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92630792596951902819176563 138946188895427854228764845)
        ·
          refine ⟨52104820835785445335786817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138946188895427854228764845 52104820835785445335786817)
          ·
            refine ⟨39078615626839084001840113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52104820835785445335786817 39078615626839084001840113)
            ·
              refine ⟨29308961720129313001380085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39078615626839084001840113 29308961720129313001380085)
              ·
                refine ⟨2747715161262123093879383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29308961720129313001380085 2747715161262123093879383)
                ·
                  refine ⟨4121572741893184640819075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747715161262123093879383 4121572741893184640819075)
                  ·
                    refine ⟨6182359112839776961228613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4121572741893184640819075 6182359112839776961228613)
                    ·
                      refine ⟨1159192333657458180230365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6182359112839776961228613 1159192333657458180230365)
                      ·
                        rfl

theorem cell23_2257519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 4].length) (baseStart_2257519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257519 prefixEnd_2257519 := by exact prefixLift 2257519
  have htrace : WordTrace (prefixWord ++ tailWord_2257519) baseStart_2257519 baseEnd_2257519 := by
    simpa [prefixWord, tailWord_2257519, baseEnd_2257519] using wordTrace_append hprefix tailTrace_2257519
  have hstable : (prefixWord ++ tailWord_2257519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257519).length < 2 ^ (prefixWord ++ tailWord_2257519).sum := by decide
  have hdescent : baseEnd_2257519 < baseStart_2257519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257532 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2257532 : Nat := 118140960795 + 2257532 * 2 ^ 59
def prefixEnd_2257532 : Nat := 4983230072969 + 3 ^ 40 * 2257532 * 2
def baseEnd_2257532 : Nat := 1159199008905966629367805

theorem tailTrace_2257532 : CollatzResearch.WordTrace tailWord_2257532 prefixEnd_2257532 1159199008905966629367805 := by
  unfold tailWord_2257532
  simp only [CollatzResearch.WordTrace]
  refine ⟨41169478228677297307523425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54892637638236396410031233 41169478228677297307523425)
  ·
    refine ⟨30877108671507972980642569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41169478228677297307523425 30877108671507972980642569)
    ·
      refine ⟨23157831503630979735481927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30877108671507972980642569 23157831503630979735481927)
      ·
        refine ⟨34736747255446469603222891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23157831503630979735481927 34736747255446469603222891)
        ·
          refine ⟨52105120883169704404834337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34736747255446469603222891 52105120883169704404834337)
          ·
            refine ⟨39078840662377278303625753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52105120883169704404834337 39078840662377278303625753)
            ·
              refine ⟨29309130496782958727719315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39078840662377278303625753 29309130496782958727719315)
              ·
                refine ⟨43963695745174438091578973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29309130496782958727719315 43963695745174438091578973)
                ·
                  refine ⟨16486385904440414284342115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43963695745174438091578973 16486385904440414284342115)
                  ·
                    refine ⟨24729578856660621426513173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16486385904440414284342115 24729578856660621426513173)
                    ·
                      refine ⟨1159199008905966629367805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24729578856660621426513173 1159199008905966629367805)
                      ·
                        rfl

theorem cell23_2257532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2257532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257532 prefixEnd_2257532 := by exact prefixLift 2257532
  have htrace : WordTrace (prefixWord ++ tailWord_2257532) baseStart_2257532 baseEnd_2257532 := by
    simpa [prefixWord, tailWord_2257532, baseEnd_2257532] using wordTrace_append hprefix tailTrace_2257532
  have hstable : (prefixWord ++ tailWord_2257532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257532).length < 2 ^ (prefixWord ++ tailWord_2257532).sum := by decide
  have hdescent : baseEnd_2257532 < baseStart_2257532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257539 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 3]
def baseStart_2257539 : Nat := 118140960795 + 2257539 * 2 ^ 59
def prefixEnd_2257539 : Nat := 4983230072969 + 3 ^ 40 * 2257539 * 2
def baseEnd_2257539 : Nat := 1159202603270548101980273

theorem tailTrace_2257539 : CollatzResearch.WordTrace tailWord_2257539 prefixEnd_2257539 1159202603270548101980273 := by
  unfold tailWord_2257539
  simp only [CollatzResearch.WordTrace]
  refine ⟨82339211768329234810551671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54892807845552823207034447 82339211768329234810551671)
  ·
    refine ⟨123508817652493852215827507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82339211768329234810551671 123508817652493852215827507)
    ·
      refine ⟨185263226478740778323741261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123508817652493852215827507 185263226478740778323741261)
      ·
        refine ⟨69473709929527791871402973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185263226478740778323741261 69473709929527791871402973)
        ·
          refine ⟨26052641223572921951776115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69473709929527791871402973 26052641223572921951776115)
          ·
            refine ⟨39078961835359382927664173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26052641223572921951776115 39078961835359382927664173)
            ·
              refine ⟨14654610688259768597874065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39078961835359382927664173 14654610688259768597874065)
              ·
                refine ⟨10990958016194826448405549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14654610688259768597874065 10990958016194826448405549)
                ·
                  refine ⟨4121609256073059918152081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10990958016194826448405549 4121609256073059918152081)
                  ·
                    refine ⟨3091206942054794938614061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4121609256073059918152081 3091206942054794938614061)
                    ·
                      refine ⟨1159202603270548101980273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3091206942054794938614061 1159202603270548101980273)
                      ·
                        rfl

theorem cell23_2257539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_2257539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257539 prefixEnd_2257539 := by exact prefixLift 2257539
  have htrace : WordTrace (prefixWord ++ tailWord_2257539) baseStart_2257539 baseEnd_2257539 := by
    simpa [prefixWord, tailWord_2257539, baseEnd_2257539] using wordTrace_append hprefix tailTrace_2257539
  have hstable : (prefixWord ++ tailWord_2257539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257539).length < 2 ^ (prefixWord ++ tailWord_2257539).sum := by decide
  have hdescent : baseEnd_2257539 < baseStart_2257539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257546 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_2257546 : Nat := 118140960795 + 2257546 * 2 ^ 59
def prefixEnd_2257546 : Nat := 4983230072969 + 3 ^ 40 * 2257546 * 2
def baseEnd_2257546 : Nat := 386402065878376524864247

theorem tailTrace_2257546 : CollatzResearch.WordTrace tailWord_2257546 prefixEnd_2257546 386402065878376524864247 := by
  unfold tailWord_2257546
  simp only [CollatzResearch.WordTrace]
  refine ⟨20584866769825968751514123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54892978052869250004037661 20584866769825968751514123)
  ·
    refine ⟨30877300154738953127271185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20584866769825968751514123 30877300154738953127271185)
    ·
      refine ⟨23157975116054214845453389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30877300154738953127271185 23157975116054214845453389)
      ·
        refine ⟨8684240668520330567045021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23157975116054214845453389 8684240668520330567045021)
        ·
          refine ⟨3256590250695123962641883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8684240668520330567045021 3256590250695123962641883)
          ·
            refine ⟨4884885376042685943962825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256590250695123962641883 4884885376042685943962825)
            ·
              refine ⟨3663664032032014457972119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4884885376042685943962825 3663664032032014457972119)
              ·
                refine ⟨5495496048048021686958179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3663664032032014457972119 5495496048048021686958179)
                ·
                  refine ⟨8243244072072032530437269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5495496048048021686958179 8243244072072032530437269)
                  ·
                    refine ⟨386402065878376524864247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8243244072072032530437269 386402065878376524864247)
                    ·
                      rfl

theorem cell23_2257546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_2257546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257546 prefixEnd_2257546 := by exact prefixLift 2257546
  have htrace : WordTrace (prefixWord ++ tailWord_2257546) baseStart_2257546 baseEnd_2257546 := by
    simpa [prefixWord, tailWord_2257546, baseEnd_2257546] using wordTrace_append hprefix tailTrace_2257546
  have hstable : (prefixWord ++ tailWord_2257546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257546).length < 2 ^ (prefixWord ++ tailWord_2257546).sum := by decide
  have hdescent : baseEnd_2257546 < baseStart_2257546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257559 : List Nat := [1, 1, 3, 3, 2, 1, 5, 7]
def baseStart_2257559 : Nat := 118140960795 + 2257559 * 2 ^ 59
def prefixEnd_2257559 : Nat := 4983230072969 + 3 ^ 40 * 2257559 * 2
def baseEnd_2257559 : Nat := 42933810106801408286303

theorem tailTrace_2257559 : CollatzResearch.WordTrace tailWord_2257559 prefixEnd_2257559 42933810106801408286303 := by
  unfold tailWord_2257559
  simp only [CollatzResearch.WordTrace]
  refine ⟨82339941228256778226279731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54893294152171185484186487 82339941228256778226279731)
  ·
    refine ⟨123509911842385167339419597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82339941228256778226279731 123509911842385167339419597)
    ·
      refine ⟨46316216940894437752282349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123509911842385167339419597 46316216940894437752282349)
      ·
        refine ⟨17368581352835414157105881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46316216940894437752282349 17368581352835414157105881)
        ·
          refine ⟨13026436014626560617829411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17368581352835414157105881 13026436014626560617829411)
          ·
            refine ⟨19539654021939840926744117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13026436014626560617829411 19539654021939840926744117)
            ·
              refine ⟨1831842564556860086882261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19539654021939840926744117 1831842564556860086882261)
              ·
                refine ⟨42933810106801408286303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1831842564556860086882261 42933810106801408286303)
                ·
                  rfl

theorem cell23_2257559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 7].length) (baseStart_2257559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257559 prefixEnd_2257559 := by exact prefixLift 2257559
  have htrace : WordTrace (prefixWord ++ tailWord_2257559) baseStart_2257559 baseEnd_2257559 := by
    simpa [prefixWord, tailWord_2257559, baseEnd_2257559] using wordTrace_append hprefix tailTrace_2257559
  have hstable : (prefixWord ++ tailWord_2257559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257559).length < 2 ^ (prefixWord ++ tailWord_2257559).sum := by decide
  have hdescent : baseEnd_2257559 < baseStart_2257559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257566 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2257566 : Nat := 118140960795 + 2257566 * 2 ^ 59
def prefixEnd_2257566 : Nat := 4983230072969 + 3 ^ 40 * 2257566 * 2
def baseEnd_2257566 : Nat := 1159216467248219496342649

theorem tailTrace_2257566 : CollatzResearch.WordTrace tailWord_2257566 prefixEnd_2257566 1159216467248219496342649 := by
  unfold tailWord_2257566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10292524567403927302723069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54893464359487612281189701 10292524567403927302723069)
  ·
    refine ⟨3859696712776472738521151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10292524567403927302723069 3859696712776472738521151)
    ·
      refine ⟨5789545069164709107781727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3859696712776472738521151 5789545069164709107781727)
      ·
        refine ⟨8684317603747063661672591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5789545069164709107781727 8684317603747063661672591)
        ·
          refine ⟨13026476405620595492508887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8684317603747063661672591 13026476405620595492508887)
          ·
            refine ⟨19539714608430893238763331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13026476405620595492508887 19539714608430893238763331)
            ·
              refine ⟨29309571912646339858144997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19539714608430893238763331 29309571912646339858144997)
              ·
                refine ⟨5495544733621188723402187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29309571912646339858144997 5495544733621188723402187)
                ·
                  refine ⟨8243317100431783085103281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5495544733621188723402187 8243317100431783085103281)
                  ·
                    refine ⟨6182487825323837313827461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8243317100431783085103281 6182487825323837313827461)
                    ·
                      refine ⟨1159216467248219496342649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6182487825323837313827461 1159216467248219496342649)
                      ·
                        rfl

theorem cell23_2257566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2257566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257566 prefixEnd_2257566 := by exact prefixLift 2257566
  have htrace : WordTrace (prefixWord ++ tailWord_2257566) baseStart_2257566 baseEnd_2257566 := by
    simpa [prefixWord, tailWord_2257566, baseEnd_2257566] using wordTrace_append hprefix tailTrace_2257566
  have hstable : (prefixWord ++ tailWord_2257566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257566).length < 2 ^ (prefixWord ++ tailWord_2257566).sum := by decide
  have hdescent : baseEnd_2257566 < baseStart_2257566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257621 : List Nat := [1, 3, 2, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2257621 : Nat := 118140960795 + 2257621 * 2 ^ 59
def prefixEnd_2257621 : Nat := 4983230072969 + 3 ^ 40 * 2257621 * 2
def baseEnd_2257621 : Nat := 1159244708684216781154897

theorem tailTrace_2257621 : CollatzResearch.WordTrace tailWord_2257621 prefixEnd_2257621 1159244708684216781154897 := by
  unfold tailWord_2257621
  simp only [CollatzResearch.WordTrace]
  refine ⟨82342202554032162815036717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54894801702688108543357811 82342202554032162815036717)
  ·
    refine ⟨30878325957762061055638769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82342202554032162815036717 30878325957762061055638769)
    ·
      refine ⟨23158744468321545791729077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30878325957762061055638769 23158744468321545791729077)
      ·
        refine ⟨2171132293905144917974601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23158744468321545791729077 2171132293905144917974601)
        ·
          refine ⟨1628349220428858688480951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2171132293905144917974601 1628349220428858688480951)
          ·
            refine ⟨2442523830643288032721427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628349220428858688480951 2442523830643288032721427)
            ·
              refine ⟨3663785745964932049082141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442523830643288032721427 3663785745964932049082141)
              ·
                refine ⟨1373919654736849518405803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3663785745964932049082141 1373919654736849518405803)
                ·
                  refine ⟨2060879482105274277608705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373919654736849518405803 2060879482105274277608705)
                  ·
                    refine ⟨1545659611578955708206529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060879482105274277608705 1545659611578955708206529)
                    ·
                      refine ⟨1159244708684216781154897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545659611578955708206529 1159244708684216781154897)
                      ·
                        rfl

theorem cell23_2257621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2257621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257621 prefixEnd_2257621 := by exact prefixLift 2257621
  have htrace : WordTrace (prefixWord ++ tailWord_2257621) baseStart_2257621 baseEnd_2257621 := by
    simpa [prefixWord, tailWord_2257621, baseEnd_2257621] using wordTrace_append hprefix tailTrace_2257621
  have hstable : (prefixWord ++ tailWord_2257621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257621).length < 2 ^ (prefixWord ++ tailWord_2257621).sum := by decide
  have hdescent : baseEnd_2257621 < baseStart_2257621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257626 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2]
def baseStart_2257626 : Nat := 118140960795 + 2257626 * 2 ^ 59
def prefixEnd_2257626 : Nat := 4983230072969 + 3 ^ 40 * 2257626 * 2
def baseEnd_2257626 : Nat := 1159247276087489261592373

theorem tailTrace_2257626 : CollatzResearch.WordTrace tailWord_2257626 prefixEnd_2257626 1159247276087489261592373 := by
  unfold tailWord_2257626
  simp only [CollatzResearch.WordTrace]
  refine ⟨20585596229753512167242183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54894923279342699112645821 20585596229753512167242183)
  ·
    refine ⟨30878394344630268250863275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20585596229753512167242183 30878394344630268250863275)
    ·
      refine ⟨46317591516945402376294913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30878394344630268250863275 46317591516945402376294913)
      ·
        refine ⟨34738193637709051782221185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46317591516945402376294913 34738193637709051782221185)
        ·
          refine ⟨26053645228281788836665889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34738193637709051782221185 26053645228281788836665889)
          ·
            refine ⟨19540233921211341627499417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26053645228281788836665889 19540233921211341627499417)
            ·
              refine ⟨14655175440908506220624563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19540233921211341627499417 14655175440908506220624563)
              ·
                refine ⟨21982763161362759330936845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14655175440908506220624563 21982763161362759330936845)
                ·
                  refine ⟨8243536185511034749101317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21982763161362759330936845 8243536185511034749101317)
                  ·
                    refine ⟨1545663034783319015456497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8243536185511034749101317 1545663034783319015456497)
                    ·
                      refine ⟨1159247276087489261592373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545663034783319015456497 1159247276087489261592373)
                      ·
                        rfl

theorem cell23_2257626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_2257626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257626 prefixEnd_2257626 := by exact prefixLift 2257626
  have htrace : WordTrace (prefixWord ++ tailWord_2257626) baseStart_2257626 baseEnd_2257626 := by
    simpa [prefixWord, tailWord_2257626, baseEnd_2257626] using wordTrace_append hprefix tailTrace_2257626
  have hstable : (prefixWord ++ tailWord_2257626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257626).length < 2 ^ (prefixWord ++ tailWord_2257626).sum := by decide
  have hdescent : baseEnd_2257626 < baseStart_2257626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257643 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 2, 2, 2]
def baseStart_2257643 : Nat := 118140960795 + 2257643 * 2 ^ 59
def prefixEnd_2257643 : Nat := 4983230072969 + 3 ^ 40 * 2257643 * 2
def baseEnd_2257643 : Nat := 1159256005258615695079795

theorem tailTrace_2257643 : CollatzResearch.WordTrace tailWord_2257643 prefixEnd_2257643 1159256005258615695079795 := by
  unfold tailWord_2257643
  simp only [CollatzResearch.WordTrace]
  refine ⟨82343004959952460572337583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54895336639968307048225055 82343004959952460572337583)
  ·
    refine ⟨123514507439928690858506375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82343004959952460572337583 123514507439928690858506375)
    ·
      refine ⟨185271761159893036287759563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123514507439928690858506375 185271761159893036287759563)
      ·
        refine ⟨277907641739839554431639345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185271761159893036287759563 277907641739839554431639345)
        ·
          refine ⟨208430731304879665823729509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277907641739839554431639345 208430731304879665823729509)
          ·
            refine ⟨39080762119664937341949283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208430731304879665823729509 39080762119664937341949283)
            ·
              refine ⟨58621143179497406012923925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39080762119664937341949283 58621143179497406012923925)
              ·
                refine ⟨2747866086538940906855809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58621143179497406012923925 2747866086538940906855809)
                ·
                  refine ⟨2060899564904205680141857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2747866086538940906855809 2060899564904205680141857)
                  ·
                    refine ⟨1545674673678154260106393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060899564904205680141857 1545674673678154260106393)
                    ·
                      refine ⟨1159256005258615695079795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545674673678154260106393 1159256005258615695079795)
                      ·
                        rfl

theorem cell23_2257643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 2, 2].length) (baseStart_2257643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257643 prefixEnd_2257643 := by exact prefixLift 2257643
  have htrace : WordTrace (prefixWord ++ tailWord_2257643) baseStart_2257643 baseEnd_2257643 := by
    simpa [prefixWord, tailWord_2257643, baseEnd_2257643] using wordTrace_append hprefix tailTrace_2257643
  have hstable : (prefixWord ++ tailWord_2257643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257643).length < 2 ^ (prefixWord ++ tailWord_2257643).sum := by decide
  have hdescent : baseEnd_2257643 < baseStart_2257643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257659 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 3]
def baseStart_2257659 : Nat := 118140960795 + 2257659 * 2 ^ 59
def prefixEnd_2257659 : Nat := 4983230072969 + 3 ^ 40 * 2257659 * 2
def baseEnd_2257659 : Nat := 1159264220949087632479721

theorem tailTrace_2257659 : CollatzResearch.WordTrace tailWord_2257659 prefixEnd_2257659 1159264220949087632479721 := by
  unfold tailWord_2257659
  simp only [CollatzResearch.WordTrace]
  refine ⟨82343588527894495304920031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54895725685262996869946687 82343588527894495304920031)
  ·
    refine ⟨123515382791841742957380047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82343588527894495304920031 123515382791841742957380047)
    ·
      refine ⟨185273074187762614436070071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123515382791841742957380047 185273074187762614436070071)
      ·
        refine ⟨277909611281643921654105107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185273074187762614436070071 277909611281643921654105107)
        ·
          refine ⟨416864416922465882481157661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277909611281643921654105107 416864416922465882481157661)
          ·
            refine ⟨156324156345924705930434123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 416864416922465882481157661 156324156345924705930434123)
            ·
              refine ⟨234486234518887058895651185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156324156345924705930434123 234486234518887058895651185)
              ·
                refine ⟨175864675889165294171738389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234486234518887058895651185 175864675889165294171738389)
                ·
                  refine ⟨8243656682304623164300237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 175864675889165294171738389 8243656682304623164300237)
                  ·
                    refine ⟨3091371255864233686612589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8243656682304623164300237 3091371255864233686612589)
                    ·
                      refine ⟨1159264220949087632479721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3091371255864233686612589 1159264220949087632479721)
                      ·
                        rfl

theorem cell23_2257659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 3].length) (baseStart_2257659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257659 prefixEnd_2257659 := by exact prefixLift 2257659
  have htrace : WordTrace (prefixWord ++ tailWord_2257659) baseStart_2257659 baseEnd_2257659 := by
    simpa [prefixWord, tailWord_2257659, baseEnd_2257659] using wordTrace_append hprefix tailTrace_2257659
  have hstable : (prefixWord ++ tailWord_2257659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257659).length < 2 ^ (prefixWord ++ tailWord_2257659).sum := by decide
  have hdescent : baseEnd_2257659 < baseStart_2257659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257660 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_2257660 : Nat := 118140960795 + 2257660 * 2 ^ 59
def prefixEnd_2257660 : Nat := 4983230072969 + 3 ^ 40 * 2257660 * 2
def baseEnd_2257660 : Nat := 1159264734429742128567217

theorem tailTrace_2257660 : CollatzResearch.WordTrace tailWord_2257660 prefixEnd_2257660 1159264734429742128567217 := by
  unfold tailWord_2257660
  simp only [CollatzResearch.WordTrace]
  refine ⟨41171812500445436237853217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54895750000593914983804289 41171812500445436237853217)
  ·
    refine ⟨30878859375334077178389913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41171812500445436237853217 30878859375334077178389913)
    ·
      refine ⟨23159144531500557883792435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30878859375334077178389913 23159144531500557883792435)
      ·
        refine ⟨34738716797250836825688653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23159144531500557883792435 34738716797250836825688653)
        ·
          refine ⟨13027018798969063809633245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34738716797250836825688653 13027018798969063809633245)
          ·
            refine ⟨4885132049613398928612467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13027018798969063809633245 4885132049613398928612467)
            ·
              refine ⟨7327698074420098392918701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4885132049613398928612467 7327698074420098392918701)
              ·
                refine ⟨2747886777907536897344513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7327698074420098392918701 2747886777907536897344513)
                ·
                  refine ⟨2060915083430652673008385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2747886777907536897344513 2060915083430652673008385)
                  ·
                    refine ⟨1545686312572989504756289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060915083430652673008385 1545686312572989504756289)
                    ·
                      refine ⟨1159264734429742128567217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545686312572989504756289 1159264734429742128567217)
                      ·
                        rfl

theorem cell23_2257660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_2257660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257660 prefixEnd_2257660 := by exact prefixLift 2257660
  have htrace : WordTrace (prefixWord ++ tailWord_2257660) baseStart_2257660 baseEnd_2257660 := by
    simpa [prefixWord, tailWord_2257660, baseEnd_2257660] using wordTrace_append hprefix tailTrace_2257660
  have hstable : (prefixWord ++ tailWord_2257660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257660).length < 2 ^ (prefixWord ++ tailWord_2257660).sum := by decide
  have hdescent : baseEnd_2257660 < baseStart_2257660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257696 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 2, 5]
def baseStart_2257696 : Nat := 118140960795 + 2257696 * 2 ^ 59
def prefixEnd_2257696 : Nat := 4983230072969 + 3 ^ 40 * 2257696 * 2
def baseEnd_2257696 : Nat := 386427739911101329239017

theorem tailTrace_2257696 : CollatzResearch.WordTrace tailWord_2257696 prefixEnd_2257696 386427739911101329239017 := by
  unfold tailWord_2257696
  simp only [CollatzResearch.WordTrace]
  refine ⟨41172469014380225312008471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54896625352506967082677961 41172469014380225312008471)
  ·
    refine ⟨61758703521570337968012707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41172469014380225312008471 61758703521570337968012707)
    ·
      refine ⟨92638055282355506952019061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61758703521570337968012707 92638055282355506952019061)
      ·
        refine ⟨8684817682720828776751787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92638055282355506952019061 8684817682720828776751787)
        ·
          refine ⟨13027226524081243165127681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8684817682720828776751787 13027226524081243165127681)
          ·
            refine ⟨9770419893060932373845761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13027226524081243165127681 9770419893060932373845761)
            ·
              refine ⟨7327814919795699280384321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9770419893060932373845761 7327814919795699280384321)
              ·
                refine ⟨5495861189846774460288241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7327814919795699280384321 5495861189846774460288241)
                ·
                  refine ⟨4121895892385080845216181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5495861189846774460288241 4121895892385080845216181)
                  ·
                    refine ⟨386427739911101329239017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4121895892385080845216181 386427739911101329239017)
                    ·
                      rfl

theorem cell23_2257696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_2257696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257696 prefixEnd_2257696 := by exact prefixLift 2257696
  have htrace : WordTrace (prefixWord ++ tailWord_2257696) baseStart_2257696 baseEnd_2257696 := by
    simpa [prefixWord, tailWord_2257696, baseEnd_2257696] using wordTrace_append hprefix tailTrace_2257696
  have hstable : (prefixWord ++ tailWord_2257696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257696).length < 2 ^ (prefixWord ++ tailWord_2257696).sum := by decide
  have hdescent : baseEnd_2257696 < baseStart_2257696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257699 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 4]
def baseStart_2257699 : Nat := 118140960795 + 2257699 * 2 ^ 59
def prefixEnd_2257699 : Nat := 4983230072969 + 3 ^ 40 * 2257699 * 2
def baseEnd_2257699 : Nat := 1159284760175267475979537

theorem tailTrace_2257699 : CollatzResearch.WordTrace tailWord_2257699 prefixEnd_2257699 1159284760175267475979537 := by
  unfold tailWord_2257699
  simp only [CollatzResearch.WordTrace]
  refine ⟨82345047447749582136376151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54896698298499721424250767 82345047447749582136376151)
  ·
    refine ⟨123517571171624373204564227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82345047447749582136376151 123517571171624373204564227)
    ·
      refine ⟨185276356757436559806846341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123517571171624373204564227 185276356757436559806846341)
      ·
        refine ⟨34739316892019354963783689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185276356757436559806846341 34739316892019354963783689)
        ·
          refine ⟨26054487669014516222837767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34739316892019354963783689 26054487669014516222837767)
          ·
            refine ⟨39081731503521774334256651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26054487669014516222837767 39081731503521774334256651)
            ·
              refine ⟨58622597255282661501384977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39081731503521774334256651 58622597255282661501384977)
              ·
                refine ⟨43966947941461996126038733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58622597255282661501384977 43966947941461996126038733)
                ·
                  refine ⟨16487605478048248547264525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43966947941461996126038733 16487605478048248547264525)
                  ·
                    refine ⟨6182852054268093205224197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16487605478048248547264525 6182852054268093205224197)
                    ·
                      refine ⟨1159284760175267475979537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6182852054268093205224197 1159284760175267475979537)
                      ·
                        rfl

theorem cell23_2257699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_2257699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257699 prefixEnd_2257699 := by exact prefixLift 2257699
  have htrace : WordTrace (prefixWord ++ tailWord_2257699) baseStart_2257699 baseEnd_2257699 := by
    simpa [prefixWord, tailWord_2257699, baseEnd_2257699] using wordTrace_append hprefix tailTrace_2257699
  have hstable : (prefixWord ++ tailWord_2257699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257699).length < 2 ^ (prefixWord ++ tailWord_2257699).sum := by decide
  have hdescent : baseEnd_2257699 < baseStart_2257699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257736 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_2257736 : Nat := 118140960795 + 2257736 * 2 ^ 59
def prefixEnd_2257736 : Nat := 4983230072969 + 3 ^ 40 * 2257736 * 2
def baseEnd_2257736 : Nat := 1159303758959483831216867

theorem tailTrace_2257736 : CollatzResearch.WordTrace tailWord_2257736 prefixEnd_2257736 1159303758959483831216867 := by
  unfold tailWord_2257736
  simp only [CollatzResearch.WordTrace]
  refine ⟨41173198474307768727736531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54897597965743691636982041 41173198474307768727736531)
  ·
    refine ⟨61759797711461653091604797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41173198474307768727736531 61759797711461653091604797)
    ·
      refine ⟨23159924141798119909351799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61759797711461653091604797 23159924141798119909351799)
      ·
        refine ⟨34739886212697179864027699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23159924141798119909351799 34739886212697179864027699)
        ·
          refine ⟨52109829319045769796041549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34739886212697179864027699 52109829319045769796041549)
          ·
            refine ⟨19541185994642163673515581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52109829319045769796041549 19541185994642163673515581)
            ·
              refine ⟨7327944747990811377568343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19541185994642163673515581 7327944747990811377568343)
              ·
                refine ⟨10991917121986217066352515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327944747990811377568343 10991917121986217066352515)
                ·
                  refine ⟨16487875682979325599528773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10991917121986217066352515 16487875682979325599528773)
                  ·
                    refine ⟨3091476690558623549911645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16487875682979325599528773 3091476690558623549911645)
                    ·
                      refine ⟨1159303758959483831216867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3091476690558623549911645 1159303758959483831216867)
                      ·
                        rfl

theorem cell23_2257736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_2257736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257736 prefixEnd_2257736 := by exact prefixLift 2257736
  have htrace : WordTrace (prefixWord ++ tailWord_2257736) baseStart_2257736 baseEnd_2257736 := by
    simpa [prefixWord, tailWord_2257736, baseEnd_2257736] using wordTrace_append hprefix tailTrace_2257736
  have hstable : (prefixWord ++ tailWord_2257736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257736).length < 2 ^ (prefixWord ++ tailWord_2257736).sum := by decide
  have hdescent : baseEnd_2257736 < baseStart_2257736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257759 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_2257759 : Nat := 118140960795 + 2257759 * 2 ^ 59
def prefixEnd_2257759 : Nat := 4983230072969 + 3 ^ 40 * 2257759 * 2
def baseEnd_2257759 : Nat := 1159315569014537241229261

theorem tailTrace_2257759 : CollatzResearch.WordTrace tailWord_2257759 prefixEnd_2257759 1159315569014537241229261 := by
  unfold tailWord_2257759
  simp only [CollatzResearch.WordTrace]
  refine ⟨82347235827532212383560331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54898157218354808255706887 82347235827532212383560331)
  ·
    refine ⟨123520853741298318575340497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82347235827532212383560331 123520853741298318575340497)
    ·
      refine ⟨92640640305973738931505373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123520853741298318575340497 92640640305973738931505373)
      ·
        refine ⟨34740240114740152099314515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92640640305973738931505373 34740240114740152099314515)
        ·
          refine ⟨52110360172110228148971773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34740240114740152099314515 52110360172110228148971773)
          ·
            refine ⟨19541385064541335555864415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52110360172110228148971773 19541385064541335555864415)
            ·
              refine ⟨29312077596812003333796623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19541385064541335555864415 29312077596812003333796623)
              ·
                refine ⟨43968116395218005000694935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29312077596812003333796623 43968116395218005000694935)
                ·
                  refine ⟨65952174592827007501042403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43968116395218005000694935 65952174592827007501042403)
                  ·
                    refine ⟨98928261889240511251563605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65952174592827007501042403 98928261889240511251563605)
                    ·
                      refine ⟨1159315569014537241229261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 98928261889240511251563605 1159315569014537241229261)
                      ·
                        rfl

theorem cell23_2257759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_2257759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257759 prefixEnd_2257759 := by exact prefixLift 2257759
  have htrace : WordTrace (prefixWord ++ tailWord_2257759) baseStart_2257759 baseEnd_2257759 := by
    simpa [prefixWord, tailWord_2257759, baseEnd_2257759] using wordTrace_append hprefix tailTrace_2257759
  have hstable : (prefixWord ++ tailWord_2257759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257759).length < 2 ^ (prefixWord ++ tailWord_2257759).sum := by decide
  have hdescent : baseEnd_2257759 < baseStart_2257759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257779 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 7]
def baseStart_2257779 : Nat := 118140960795 + 2257779 * 2 ^ 59
def prefixEnd_2257779 : Nat := 4983230072969 + 3 ^ 40 * 2257779 * 2
def baseEnd_2257779 : Nat := 1159325838627627162979169

theorem tailTrace_2257779 : CollatzResearch.WordTrace tailWord_2257779 prefixEnd_2257779 1159325838627627162979169 := by
  unfold tailWord_2257779
  simp only [CollatzResearch.WordTrace]
  refine ⟨82347965287459755799288391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54898643524973170532858927 82347965287459755799288391)
  ·
    refine ⟨123521947931189633698932587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82347965287459755799288391 123521947931189633698932587)
    ·
      refine ⟨185282921896784450548398881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123521947931189633698932587 185282921896784450548398881)
      ·
        refine ⟨138962191422588337911299161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185282921896784450548398881 138962191422588337911299161)
        ·
          refine ⟨104221643566941253433474371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138962191422588337911299161 104221643566941253433474371)
          ·
            refine ⟨156332465350411880150211557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104221643566941253433474371 156332465350411880150211557)
            ·
              refine ⟨29312337253202227528164667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156332465350411880150211557 29312337253202227528164667)
              ·
                refine ⟨43968505879803341292247001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29312337253202227528164667 43968505879803341292247001)
                ·
                  refine ⟨32976379409852505969185251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43968505879803341292247001 32976379409852505969185251)
                  ·
                    refine ⟨49464569114778758953777877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32976379409852505969185251 49464569114778758953777877)
                    ·
                      refine ⟨1159325838627627162979169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49464569114778758953777877 1159325838627627162979169)
                      ·
                        rfl

theorem cell23_2257779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_2257779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257779 prefixEnd_2257779 := by exact prefixLift 2257779
  have htrace : WordTrace (prefixWord ++ tailWord_2257779) baseStart_2257779 baseEnd_2257779 := by
    simpa [prefixWord, tailWord_2257779, baseEnd_2257779] using wordTrace_append hprefix tailTrace_2257779
  have hstable : (prefixWord ++ tailWord_2257779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257779).length < 2 ^ (prefixWord ++ tailWord_2257779).sum := by decide
  have hdescent : baseEnd_2257779 < baseStart_2257779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257833 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 2, 4]
def baseStart_2257833 : Nat := 118140960795 + 2257833 * 2 ^ 59
def prefixEnd_2257833 : Nat := 4983230072969 + 3 ^ 40 * 2257833 * 2
def baseEnd_2257833 : Nat := 386451188860989983901307

theorem tailTrace_2257833 : CollatzResearch.WordTrace tailWord_2257833 prefixEnd_2257833 386451188860989983901307 := by
  unfold tailWord_2257833
  simp only [CollatzResearch.WordTrace]
  refine ⟨82349934829264123021754153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54899956552842748681169435 82349934829264123021754153)
  ·
    refine ⟨61762451121948092266315615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82349934829264123021754153 61762451121948092266315615)
    ·
      refine ⟨92643676682922138399473423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61762451121948092266315615 92643676682922138399473423)
      ·
        refine ⟨138965515024383207599210135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92643676682922138399473423 138965515024383207599210135)
        ·
          refine ⟨208448272536574811398815203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138965515024383207599210135 208448272536574811398815203)
          ·
            refine ⟨312672408804862217098222805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208448272536574811398815203 312672408804862217098222805)
            ·
              refine ⟨7328259581363958213239597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 312672408804862217098222805 7328259581363958213239597)
              ·
                refine ⟨2748097343011484329964849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7328259581363958213239597 2748097343011484329964849)
                ·
                  refine ⟨2061073007258613247473637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2748097343011484329964849 2061073007258613247473637)
                  ·
                    refine ⟨386451188860989983901307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2061073007258613247473637 386451188860989983901307)
                    ·
                      rfl

theorem cell23_2257833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 4].length) (baseStart_2257833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257833 prefixEnd_2257833 := by exact prefixLift 2257833
  have htrace : WordTrace (prefixWord ++ tailWord_2257833) baseStart_2257833 baseEnd_2257833 := by
    simpa [prefixWord, tailWord_2257833, baseEnd_2257833] using wordTrace_append hprefix tailTrace_2257833
  have hstable : (prefixWord ++ tailWord_2257833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257833).length < 2 ^ (prefixWord ++ tailWord_2257833).sum := by decide
  have hdescent : baseEnd_2257833 < baseStart_2257833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257843 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 3]
def baseStart_2257843 : Nat := 118140960795 + 2257843 * 2 ^ 59
def prefixEnd_2257843 : Nat := 4983230072969 + 3 ^ 40 * 2257843 * 2
def baseEnd_2257843 : Nat := 1159358701389514912578875

theorem tailTrace_2257843 : CollatzResearch.WordTrace tailWord_2257843 prefixEnd_2257843 1159358701389514912578875 := by
  unfold tailWord_2257843
  simp only [CollatzResearch.WordTrace]
  refine ⟨82350299559227894729618183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54900199706151929819745455 82350299559227894729618183)
  ·
    refine ⟨123525449338841842094427275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82350299559227894729618183 123525449338841842094427275)
    ·
      refine ⟨185288174008262763141640913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123525449338841842094427275 185288174008262763141640913)
      ·
        refine ⟨138966130506197072356230685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185288174008262763141640913 138966130506197072356230685)
        ·
          refine ⟨52112298939823902133586507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138966130506197072356230685 52112298939823902133586507)
          ·
            refine ⟨78168448409735853200379761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52112298939823902133586507 78168448409735853200379761)
            ·
              refine ⟨58626336307301889900284821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78168448409735853200379761 58626336307301889900284821)
              ·
                refine ⟨2748109514404776089075851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58626336307301889900284821 2748109514404776089075851)
                ·
                  refine ⟨4122164271607164133613777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748109514404776089075851 4122164271607164133613777)
                  ·
                    refine ⟨3091623203705373100210333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4122164271607164133613777 3091623203705373100210333)
                    ·
                      refine ⟨1159358701389514912578875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3091623203705373100210333 1159358701389514912578875)
                      ·
                        rfl

theorem cell23_2257843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 3].length) (baseStart_2257843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257843 prefixEnd_2257843 := by exact prefixLift 2257843
  have htrace : WordTrace (prefixWord ++ tailWord_2257843) baseStart_2257843 baseEnd_2257843 := by
    simpa [prefixWord, tailWord_2257843, baseEnd_2257843] using wordTrace_append hprefix tailTrace_2257843
  have hstable : (prefixWord ++ tailWord_2257843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257843).length < 2 ^ (prefixWord ++ tailWord_2257843).sum := by decide
  have hdescent : baseEnd_2257843 < baseStart_2257843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257844 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_2257844 : Nat := 118140960795 + 2257844 * 2 ^ 59
def prefixEnd_2257844 : Nat := 4983230072969 + 3 ^ 40 * 2257844 * 2
def baseEnd_2257844 : Nat := 1159359214870169408666371

theorem tailTrace_2257844 : CollatzResearch.WordTrace tailWord_2257844 prefixEnd_2257844 1159359214870169408666371 := by
  unfold tailWord_2257844
  simp only [CollatzResearch.WordTrace]
  refine ⟨41175168016112135950202293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54900224021482847933603057 41175168016112135950202293)
  ·
    refine ⟨3860172001510512745331465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41175168016112135950202293 3860172001510512745331465)
    ·
      refine ⟨2895129001132884558998599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3860172001510512745331465 2895129001132884558998599)
      ·
        refine ⟨4342693501699326838497899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2895129001132884558998599 4342693501699326838497899)
        ·
          refine ⟨6514040252548990257746849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4342693501699326838497899 6514040252548990257746849)
          ·
            refine ⟨4885530189411742693310137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6514040252548990257746849 4885530189411742693310137)
            ·
              refine ⟨3664147642058807019982603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4885530189411742693310137 3664147642058807019982603)
              ·
                refine ⟨5496221463088210529973905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664147642058807019982603 5496221463088210529973905)
                ·
                  refine ⟨4122166097316157897480429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5496221463088210529973905 4122166097316157897480429)
                  ·
                    refine ⟨1545812286493559211555161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4122166097316157897480429 1545812286493559211555161)
                    ·
                      refine ⟨1159359214870169408666371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545812286493559211555161 1159359214870169408666371)
                      ·
                        rfl

theorem cell23_2257844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_2257844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257844 prefixEnd_2257844 := by exact prefixLift 2257844
  have htrace : WordTrace (prefixWord ++ tailWord_2257844) baseStart_2257844 baseEnd_2257844 := by
    simpa [prefixWord, tailWord_2257844, baseEnd_2257844] using wordTrace_append hprefix tailTrace_2257844
  have hstable : (prefixWord ++ tailWord_2257844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257844).length < 2 ^ (prefixWord ++ tailWord_2257844).sum := by decide
  have hdescent : baseEnd_2257844 < baseStart_2257844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257862 : List Nat := [6, 1, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2257862 : Nat := 118140960795 + 2257862 * 2 ^ 59
def prefixEnd_2257862 : Nat := 4983230072969 + 3 ^ 40 * 2257862 * 2
def baseEnd_2257862 : Nat := 386456152507316779413763

theorem tailTrace_2257862 : CollatzResearch.WordTrace tailWord_2257862 prefixEnd_2257862 386456152507316779413763 := by
  unfold tailWord_2257862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2573468517067470655454995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54900661697439373983039893 2573468517067470655454995)
  ·
    refine ⟨3860202775601205983182493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2573468517067470655454995 3860202775601205983182493)
    ·
      refine ⟨1447576040850452243693435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3860202775601205983182493 1447576040850452243693435)
      ·
        refine ⟨2171364061275678365540153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447576040850452243693435 2171364061275678365540153)
        ·
          refine ⟨1628523045956758774155115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2171364061275678365540153 1628523045956758774155115)
          ·
            refine ⟨2442784568935138161232673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628523045956758774155115 2442784568935138161232673)
            ·
              refine ⟨1832088426701353620924505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2442784568935138161232673 1832088426701353620924505)
              ·
                refine ⟨1374066320026015215693379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1832088426701353620924505 1374066320026015215693379)
                ·
                  refine ⟨2061099480039022823540069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374066320026015215693379 2061099480039022823540069)
                  ·
                    refine ⟨386456152507316779413763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2061099480039022823540069 386456152507316779413763)
                    ·
                      rfl

theorem cell23_2257862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2257862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257862 prefixEnd_2257862 := by exact prefixLift 2257862
  have htrace : WordTrace (prefixWord ++ tailWord_2257862) baseStart_2257862 baseEnd_2257862 := by
    simpa [prefixWord, tailWord_2257862, baseEnd_2257862] using wordTrace_append hprefix tailTrace_2257862
  have hstable : (prefixWord ++ tailWord_2257862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257862).length < 2 ^ (prefixWord ++ tailWord_2257862).sum := by decide
  have hdescent : baseEnd_2257862 < baseStart_2257862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257953 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 7]
def baseStart_2257953 : Nat := 118140960795 + 2257953 * 2 ^ 59
def prefixEnd_2257953 : Nat := 4983230072969 + 3 ^ 40 * 2257953 * 2
def baseEnd_2257953 : Nat := 128823909362389942467041

theorem tailTrace_2257953 : CollatzResearch.WordTrace tailWord_2257953 prefixEnd_2257953 128823909362389942467041 := by
  unfold tailWord_2257953
  simp only [CollatzResearch.WordTrace]
  refine ⟨82354311588829383516122513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54902874392552922344081675 82354311588829383516122513)
  ·
    refine ⟨61765733691622037637091885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82354311588829383516122513 61765733691622037637091885)
    ·
      refine ⟨23162150134358264113909457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61765733691622037637091885 23162150134358264113909457)
      ·
        refine ⟨17371612600768698085432093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23162150134358264113909457 17371612600768698085432093)
        ·
          refine ⟨6514354725288261782037035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17371612600768698085432093 6514354725288261782037035)
          ·
            refine ⟨9771532087932392673055553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6514354725288261782037035 9771532087932392673055553)
            ·
              refine ⟨7328649065949294504791665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9771532087932392673055553 7328649065949294504791665)
              ·
                refine ⟨5496486799461970878593749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7328649065949294504791665 5496486799461970878593749)
                ·
                  refine ⟨128823909362389942467041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5496486799461970878593749 128823909362389942467041)
                  ·
                    rfl

theorem cell23_2257953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 7].length) (baseStart_2257953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2257953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2257953 prefixEnd_2257953 := by exact prefixLift 2257953
  have htrace : WordTrace (prefixWord ++ tailWord_2257953) baseStart_2257953 baseEnd_2257953 := by
    simpa [prefixWord, tailWord_2257953, baseEnd_2257953] using wordTrace_append hprefix tailTrace_2257953
  have hstable : (prefixWord ++ tailWord_2257953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257953).length < 2 ^ (prefixWord ++ tailWord_2257953).sum := by decide
  have hdescent : baseEnd_2257953 < baseStart_2257953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258020 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_2258020 : Nat := 118140960795 + 2258020 * 2 ^ 59
def prefixEnd_2258020 : Nat := 4983230072969 + 3 ^ 40 * 2258020 * 2
def baseEnd_2258020 : Nat := 1159449587465360720065561

theorem tailTrace_2258020 : CollatzResearch.WordTrace tailWord_2258020 prefixEnd_2258020 1159449587465360720065561 := by
  unfold tailWord_2258020
  simp only [CollatzResearch.WordTrace]
  refine ⟨41178377639793326979405757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54904503519724435972541009 41178377639793326979405757)
  ·
    refine ⟨15441891614922497617277159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41178377639793326979405757 15441891614922497617277159)
    ·
      refine ⟨23162837422383746425915739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15441891614922497617277159 23162837422383746425915739)
      ·
        refine ⟨34744256133575619638873609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23162837422383746425915739 34744256133575619638873609)
        ·
          refine ⟨26058192100181714729155207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34744256133575619638873609 26058192100181714729155207)
          ·
            refine ⟨39087288150272572093732811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26058192100181714729155207 39087288150272572093732811)
            ·
              refine ⟨58630932225408858140599217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39087288150272572093732811 58630932225408858140599217)
              ·
                refine ⟨43973199169056643605449413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58630932225408858140599217 43973199169056643605449413)
                ·
                  refine ⟨8244974844198120676021765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43973199169056643605449413 8244974844198120676021765)
                  ·
                    refine ⟨1545932783287147626754081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8244974844198120676021765 1545932783287147626754081)
                    ·
                      refine ⟨1159449587465360720065561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1545932783287147626754081 1159449587465360720065561)
                      ·
                        rfl

theorem cell23_2258020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_2258020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258020 prefixEnd_2258020 := by exact prefixLift 2258020
  have htrace : WordTrace (prefixWord ++ tailWord_2258020) baseStart_2258020 baseEnd_2258020 := by
    simpa [prefixWord, tailWord_2258020, baseEnd_2258020] using wordTrace_append hprefix tailTrace_2258020
  have hstable : (prefixWord ++ tailWord_2258020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258020).length < 2 ^ (prefixWord ++ tailWord_2258020).sum := by decide
  have hdescent : baseEnd_2258020 < baseStart_2258020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258040 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_2258040 : Nat := 118140960795 + 2258040 * 2 ^ 59
def prefixEnd_2258040 : Nat := 4983230072969 + 3 ^ 40 * 2258040 * 2
def baseEnd_2258040 : Nat := 1159459857078450641815469

theorem tailTrace_2258040 : CollatzResearch.WordTrace tailWord_2258040 prefixEnd_2258040 1159459857078450641815469 := by
  unfold tailWord_2258040
  simp only [CollatzResearch.WordTrace]
  refine ⟨41178742369757098687269787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54904989826342798249693049 41178742369757098687269787)
  ·
    refine ⟨61768113554635648030904681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41178742369757098687269787 61768113554635648030904681)
    ·
      refine ⟨46326085165976736023178511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61768113554635648030904681 46326085165976736023178511)
      ·
        refine ⟨69489127748965104034767767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46326085165976736023178511 69489127748965104034767767)
        ·
          refine ⟨104233691623447656052151651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69489127748965104034767767 104233691623447656052151651)
          ·
            refine ⟨156350537435171484078227477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104233691623447656052151651 156350537435171484078227477)
            ·
              refine ⟨7328931442273663316166913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 156350537435171484078227477 7328931442273663316166913)
              ·
                refine ⟨5496698581705247487125185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7328931442273663316166913 5496698581705247487125185)
                ·
                  refine ⟨4122523936278935615343889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5496698581705247487125185 4122523936278935615343889)
                  ·
                    refine ⟨3091892952209201711507917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4122523936278935615343889 3091892952209201711507917)
                    ·
                      refine ⟨1159459857078450641815469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3091892952209201711507917 1159459857078450641815469)
                      ·
                        rfl

theorem cell23_2258040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_2258040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258040 prefixEnd_2258040 := by exact prefixLift 2258040
  have htrace : WordTrace (prefixWord ++ tailWord_2258040) baseStart_2258040 baseEnd_2258040 := by
    simpa [prefixWord, tailWord_2258040, baseEnd_2258040] using wordTrace_append hprefix tailTrace_2258040
  have hstable : (prefixWord ++ tailWord_2258040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258040).length < 2 ^ (prefixWord ++ tailWord_2258040).sum := by decide
  have hdescent : baseEnd_2258040 < baseStart_2258040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258074 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2258074 : Nat := 118140960795 + 2258074 * 2 ^ 59
def prefixEnd_2258074 : Nat := 4983230072969 + 3 ^ 40 * 2258074 * 2
def baseEnd_2258074 : Nat := 1159477315420703508790313

theorem tailTrace_2258074 : CollatzResearch.WordTrace tailWord_2258074 prefixEnd_2258074 1159477315420703508790313 := by
  unfold tailWord_2258074
  simp only [CollatzResearch.WordTrace]
  refine ⟨20589681205347755295319319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54905816547594014120851517 20589681205347755295319319)
  ·
    refine ⟨30884521808021632942978979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20589681205347755295319319 30884521808021632942978979)
    ·
      refine ⟨46326782712032449414468469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30884521808021632942978979 46326782712032449414468469)
      ·
        refine ⟨4343135879253042132606419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46326782712032449414468469 4343135879253042132606419)
        ·
          refine ⟨6514703818879563198909629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343135879253042132606419 6514703818879563198909629)
          ·
            refine ⟨2443013932079836199591111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6514703818879563198909629 2443013932079836199591111)
            ·
              refine ⟨3664520898119754299386667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443013932079836199591111 3664520898119754299386667)
              ·
                refine ⟨5496781347179631449080001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664520898119754299386667 5496781347179631449080001)
                ·
                  refine ⟨4122586010384723586810001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5496781347179631449080001 4122586010384723586810001)
                  ·
                    refine ⟨3091939507788542690107501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4122586010384723586810001 3091939507788542690107501)
                    ·
                      refine ⟨1159477315420703508790313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3091939507788542690107501 1159477315420703508790313)
                      ·
                        rfl

theorem cell23_2258074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2258074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258074 prefixEnd_2258074 := by exact prefixLift 2258074
  have htrace : WordTrace (prefixWord ++ tailWord_2258074) baseStart_2258074 baseEnd_2258074 := by
    simpa [prefixWord, tailWord_2258074, baseEnd_2258074] using wordTrace_append hprefix tailTrace_2258074
  have hstable : (prefixWord ++ tailWord_2258074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258074).length < 2 ^ (prefixWord ++ tailWord_2258074).sum := by decide
  have hdescent : baseEnd_2258074 < baseStart_2258074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258120 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 1, 6]
def baseStart_2258120 : Nat := 118140960795 + 2258120 * 2 ^ 59
def prefixEnd_2258120 : Nat := 4983230072969 + 3 ^ 40 * 2258120 * 2
def baseEnd_2258120 : Nat := 386500311843603442938367

theorem tailTrace_2258120 : CollatzResearch.WordTrace tailWord_2258120 prefixEnd_2258120 386500311843603442938367 := by
  unfold tailWord_2258120
  simp only [CollatzResearch.WordTrace]
  refine ⟨41180201289612185518725907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54906935052816247358301209 41180201289612185518725907)
  ·
    refine ⟨61770301934418278278088861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41180201289612185518725907 61770301934418278278088861)
    ·
      refine ⟨23163863225406854354283323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61770301934418278278088861 23163863225406854354283323)
      ·
        refine ⟨34745794838110281531424985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23163863225406854354283323 34745794838110281531424985)
        ·
          refine ⟨26059346128582711148568739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34745794838110281531424985 26059346128582711148568739)
          ·
            refine ⟨39089019192874066722853109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26059346128582711148568739 39089019192874066722853109)
            ·
              refine ⟨3664595549331943755267479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39089019192874066722853109 3664595549331943755267479)
              ·
                refine ⟨5496893323997915632901219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664595549331943755267479 5496893323997915632901219)
                ·
                  refine ⟨8245339985996873449351829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5496893323997915632901219 8245339985996873449351829)
                  ·
                    refine ⟨386500311843603442938367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8245339985996873449351829 386500311843603442938367)
                    ·
                      rfl

theorem cell23_2258120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_2258120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258120 prefixEnd_2258120 := by exact prefixLift 2258120
  have htrace : WordTrace (prefixWord ++ tailWord_2258120) baseStart_2258120 baseEnd_2258120 := by
    simpa [prefixWord, tailWord_2258120, baseEnd_2258120] using wordTrace_append hprefix tailTrace_2258120
  have hstable : (prefixWord ++ tailWord_2258120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258120).length < 2 ^ (prefixWord ++ tailWord_2258120).sum := by decide
  have hdescent : baseEnd_2258120 < baseStart_2258120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258127 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 5, 2, 2]
def baseStart_2258127 : Nat := 118140960795 + 2258127 * 2 ^ 59
def prefixEnd_2258127 : Nat := 4983230072969 + 3 ^ 40 * 2258127 * 2
def baseEnd_2258127 : Nat := 1159504529895391801427569

theorem tailTrace_2258127 : CollatzResearch.WordTrace tailWord_2258127 prefixEnd_2258127 1159504529895391801427569 := by
  unfold tailWord_2258127
  simp only [CollatzResearch.WordTrace]
  refine ⟨82360657890199011232956635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54907105260132674155304423 82360657890199011232956635)
  ·
    refine ⟨123540986835298516849434953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82360657890199011232956635 123540986835298516849434953)
    ·
      refine ⟨92655740126473887637076215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123540986835298516849434953 92655740126473887637076215)
      ·
        refine ⟨138983610189710831455614323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92655740126473887637076215 138983610189710831455614323)
        ·
          refine ⟨208475415284566247183421485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138983610189710831455614323 208475415284566247183421485)
          ·
            refine ⟨78178280731712342693783057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208475415284566247183421485 78178280731712342693783057)
            ·
              refine ⟨58633710548784257020337293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78178280731712342693783057 58633710548784257020337293)
              ·
                refine ⟨21987641455794096382626485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58633710548784257020337293 21987641455794096382626485)
                ·
                  refine ⟨2061341386480696535871233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21987641455794096382626485 2061341386480696535871233)
                  ·
                    refine ⟨1546006039860522401903425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2061341386480696535871233 1546006039860522401903425)
                    ·
                      refine ⟨1159504529895391801427569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546006039860522401903425 1159504529895391801427569)
                      ·
                        rfl

theorem cell23_2258127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 2, 2].length) (baseStart_2258127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258127 prefixEnd_2258127 := by exact prefixLift 2258127
  have htrace : WordTrace (prefixWord ++ tailWord_2258127) baseStart_2258127 baseEnd_2258127 := by
    simpa [prefixWord, tailWord_2258127, baseEnd_2258127] using wordTrace_append hprefix tailTrace_2258127
  have hstable : (prefixWord ++ tailWord_2258127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258127).length < 2 ^ (prefixWord ++ tailWord_2258127).sum := by decide
  have hdescent : baseEnd_2258127 < baseStart_2258127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258130 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2258130 : Nat := 118140960795 + 2258130 * 2 ^ 59
def prefixEnd_2258130 : Nat := 4983230072969 + 3 ^ 40 * 2258130 * 2
def baseEnd_2258130 : Nat := 1159506070337355289690055

theorem tailTrace_2258130 : CollatzResearch.WordTrace tailWord_2258130 prefixEnd_2258130 1159506070337355289690055 := by
  unfold tailWord_2258130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20590191827297035686328961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54907178206125428496877229 20590191827297035686328961)
  ·
    refine ⟨15442643870472776764746721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20590191827297035686328961 15442643870472776764746721)
    ·
      refine ⟨11581982902854582573560041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15442643870472776764746721 11581982902854582573560041)
      ·
        refine ⟨8686487177140936930170031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11581982902854582573560041 8686487177140936930170031)
        ·
          refine ⟨13029730765711405395255047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8686487177140936930170031 13029730765711405395255047)
          ·
            refine ⟨19544596148567108092882571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13029730765711405395255047 19544596148567108092882571)
            ·
              refine ⟨29316894222850662139323857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19544596148567108092882571 29316894222850662139323857)
              ·
                refine ⟨21987670667137996604492893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29316894222850662139323857 21987670667137996604492893)
                ·
                  refine ⟨8245376500176748726684835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21987670667137996604492893 8245376500176748726684835)
                  ·
                    refine ⟨12368064750265123090027253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8245376500176748726684835 12368064750265123090027253)
                    ·
                      refine ⟨1159506070337355289690055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12368064750265123090027253 1159506070337355289690055)
                      ·
                        rfl

theorem cell23_2258130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2258130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258130 prefixEnd_2258130 := by exact prefixLift 2258130
  have htrace : WordTrace (prefixWord ++ tailWord_2258130) baseStart_2258130 baseEnd_2258130 := by
    simpa [prefixWord, tailWord_2258130, baseEnd_2258130] using wordTrace_append hprefix tailTrace_2258130
  have hstable : (prefixWord ++ tailWord_2258130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258130).length < 2 ^ (prefixWord ++ tailWord_2258130).sum := by decide
  have hdescent : baseEnd_2258130 < baseStart_2258130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258153 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_2258153 : Nat := 118140960795 + 2258153 * 2 ^ 59
def prefixEnd_2258153 : Nat := 4983230072969 + 3 ^ 40 * 2258153 * 2
def baseEnd_2258153 : Nat := 1159517880392408699702449

theorem tailTrace_2258153 : CollatzResearch.WordTrace tailWord_2258153 prefixEnd_2258153 1159517880392408699702449 := by
  unfold tailWord_2258153
  simp only [CollatzResearch.WordTrace]
  refine ⟨82361606188104817673403113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54907737458736545115602075 82361606188104817673403113)
  ·
    refine ⟨61771204641078613255052335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82361606188104817673403113 61771204641078613255052335)
    ·
      refine ⟨92656806961617919882578503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61771204641078613255052335 92656806961617919882578503)
      ·
        refine ⟨138985210442426879823867755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92656806961617919882578503 138985210442426879823867755)
        ·
          refine ⟨208477815663640319735801633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138985210442426879823867755 208477815663640319735801633)
          ·
            refine ⟨156358361747730239801851225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208477815663640319735801633 156358361747730239801851225)
            ·
              refine ⟨117268771310797679851388419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156358361747730239801851225 117268771310797679851388419)
              ·
                refine ⟨175903156966196519777082629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117268771310797679851388419 175903156966196519777082629)
                ·
                  refine ⟨32981841931161847458202993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175903156966196519777082629 32981841931161847458202993)
                  ·
                    refine ⟨24736381448371385593652245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32981841931161847458202993 24736381448371385593652245)
                    ·
                      refine ⟨1159517880392408699702449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24736381448371385593652245 1159517880392408699702449)
                      ·
                        rfl

theorem cell23_2258153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_2258153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258153 prefixEnd_2258153 := by exact prefixLift 2258153
  have htrace : WordTrace (prefixWord ++ tailWord_2258153) baseStart_2258153 baseEnd_2258153 := by
    simpa [prefixWord, tailWord_2258153, baseEnd_2258153] using wordTrace_append hprefix tailTrace_2258153
  have hstable : (prefixWord ++ tailWord_2258153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258153).length < 2 ^ (prefixWord ++ tailWord_2258153).sum := by decide
  have hdescent : baseEnd_2258153 < baseStart_2258153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258178 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_2258178 : Nat := 118140960795 + 2258178 * 2 ^ 59
def prefixEnd_2258178 : Nat := 4983230072969 + 3 ^ 40 * 2258178 * 2
def baseEnd_2258178 : Nat := 1159530717408771101889835

theorem tailTrace_2258178 : CollatzResearch.WordTrace tailWord_2258178 prefixEnd_2258178 1159530717408771101889835 := by
  unfold tailWord_2258178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20590629503253561735765797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54908345342009497962042125 20590629503253561735765797)
  ·
    refine ⟨3860743031860042825456087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20590629503253561735765797 3860743031860042825456087)
    ·
      refine ⟨5791114547790064238184131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3860743031860042825456087 5791114547790064238184131)
      ·
        refine ⟨8686671821685096357276197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5791114547790064238184131 8686671821685096357276197)
        ·
          refine ⟨1628750966565955566989287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8686671821685096357276197 1628750966565955566989287)
          ·
            refine ⟨2443126449848933350483931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628750966565955566989287 2443126449848933350483931)
            ·
              refine ⟨3664689674773400025725897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443126449848933350483931 3664689674773400025725897)
              ·
                refine ⟨2748517256080050019294423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3664689674773400025725897 2748517256080050019294423)
                ·
                  refine ⟨4122775884120075028941635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748517256080050019294423 4122775884120075028941635)
                  ·
                    refine ⟨6184163826180112543412453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4122775884120075028941635 6184163826180112543412453)
                    ·
                      refine ⟨1159530717408771101889835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6184163826180112543412453 1159530717408771101889835)
                      ·
                        rfl

theorem cell23_2258178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_2258178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258178 prefixEnd_2258178 := by exact prefixLift 2258178
  have htrace : WordTrace (prefixWord ++ tailWord_2258178) baseStart_2258178 baseEnd_2258178 := by
    simpa [prefixWord, tailWord_2258178, baseEnd_2258178] using wordTrace_append hprefix tailTrace_2258178
  have hstable : (prefixWord ++ tailWord_2258178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258178).length < 2 ^ (prefixWord ++ tailWord_2258178).sum := by decide
  have hdescent : baseEnd_2258178 < baseStart_2258178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258204 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_2258204 : Nat := 118140960795 + 2258204 * 2 ^ 59
def prefixEnd_2258204 : Nat := 4983230072969 + 3 ^ 40 * 2258204 * 2
def baseEnd_2258204 : Nat := 1159544067905788000164715

theorem tailTrace_2258204 : CollatzResearch.WordTrace tailWord_2258204 prefixEnd_2258204 1159544067905788000164715 := by
  unfold tailWord_2258204
  simp only [CollatzResearch.WordTrace]
  refine ⟨41181733155460026691754833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54908977540613368922339777 41181733155460026691754833)
  ·
    refine ⟨30886299866595020018816125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41181733155460026691754833 30886299866595020018816125)
    ·
      refine ⟨11582362449973132507056047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30886299866595020018816125 11582362449973132507056047)
      ·
        refine ⟨17373543674959698760584071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11582362449973132507056047 17373543674959698760584071)
        ·
          refine ⟨26060315512439548140876107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17373543674959698760584071 26060315512439548140876107)
          ·
            refine ⟨39090473268659322211314161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26060315512439548140876107 39090473268659322211314161)
            ·
              refine ⟨29317854951494491658485621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39090473268659322211314161 29317854951494491658485621)
              ·
                refine ⟨2748548901702608592983027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29317854951494491658485621 2748548901702608592983027)
                ·
                  refine ⟨4122823352553912889474541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748548901702608592983027 4122823352553912889474541)
                  ·
                    refine ⟨1546058757207717333552953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4122823352553912889474541 1546058757207717333552953)
                    ·
                      refine ⟨1159544067905788000164715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546058757207717333552953 1159544067905788000164715)
                      ·
                        rfl

theorem cell23_2258204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_2258204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258204 prefixEnd_2258204 := by exact prefixLift 2258204
  have htrace : WordTrace (prefixWord ++ tailWord_2258204) baseStart_2258204 baseEnd_2258204 := by
    simpa [prefixWord, tailWord_2258204, baseEnd_2258204] using wordTrace_append hprefix tailTrace_2258204
  have hstable : (prefixWord ++ tailWord_2258204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258204).length < 2 ^ (prefixWord ++ tailWord_2258204).sum := by decide
  have hdescent : baseEnd_2258204 < baseStart_2258204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258221 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_2258221 : Nat := 118140960795 + 2258221 * 2 ^ 59
def prefixEnd_2258221 : Nat := 4983230072969 + 3 ^ 40 * 2258221 * 2
def baseEnd_2258221 : Nat := 1159552797076914433652137

theorem tailTrace_2258221 : CollatzResearch.WordTrace tailWord_2258221 prefixEnd_2258221 1159552797076914433652137 := by
  unfold tailWord_2258221
  simp only [CollatzResearch.WordTrace]
  refine ⟨82364086351858465286878517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54909390901238976857919011 82364086351858465286878517)
  ·
    refine ⟨7721633095486731120644861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82364086351858465286878517 7721633095486731120644861)
    ·
      refine ⟨2895612410807524170241823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7721633095486731120644861 2895612410807524170241823)
      ·
        refine ⟨4343418616211286255362735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2895612410807524170241823 4343418616211286255362735)
        ·
          refine ⟨6515127924316929383044103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343418616211286255362735 6515127924316929383044103)
          ·
            refine ⟨9772691886475394074566155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515127924316929383044103 9772691886475394074566155)
            ·
              refine ⟨14659037829713091111849233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9772691886475394074566155 14659037829713091111849233)
              ·
                refine ⟨10994278372284818333886925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14659037829713091111849233 10994278372284818333886925)
                ·
                  refine ⟨4122854389606806875207597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10994278372284818333886925 4122854389606806875207597)
                  ·
                    refine ⟨1546070396102552578202849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4122854389606806875207597 1546070396102552578202849)
                    ·
                      refine ⟨1159552797076914433652137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546070396102552578202849 1159552797076914433652137)
                      ·
                        rfl

theorem cell23_2258221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_2258221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258221 prefixEnd_2258221 := by exact prefixLift 2258221
  have htrace : WordTrace (prefixWord ++ tailWord_2258221) baseStart_2258221 baseEnd_2258221 := by
    simpa [prefixWord, tailWord_2258221, baseEnd_2258221] using wordTrace_append hprefix tailTrace_2258221
  have hstable : (prefixWord ++ tailWord_2258221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258221).length < 2 ^ (prefixWord ++ tailWord_2258221).sum := by decide
  have hdescent : baseEnd_2258221 < baseStart_2258221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258234 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2]
def baseStart_2258234 : Nat := 118140960795 + 2258234 * 2 ^ 59
def prefixEnd_2258234 : Nat := 4983230072969 + 3 ^ 40 * 2258234 * 2
def baseEnd_2258234 : Nat := 1159559472325422882789577

theorem tailTrace_2258234 : CollatzResearch.WordTrace tailWord_2258234 prefixEnd_2258234 1159559472325422882789577 := by
  unfold tailWord_2258234
  simp only [CollatzResearch.WordTrace]
  refine ⟨20591140125202842126775439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54909707000540912338067837 20591140125202842126775439)
  ·
    refine ⟨30886710187804263190163159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20591140125202842126775439 30886710187804263190163159)
    ·
      refine ⟨46330065281706394785244739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30886710187804263190163159 46330065281706394785244739)
      ·
        refine ⟨69495097922559592177867109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46330065281706394785244739 69495097922559592177867109)
        ·
          refine ⟨13030330860479923533350083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69495097922559592177867109 13030330860479923533350083)
          ·
            refine ⟨19545496290719885300025125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13030330860479923533350083 19545496290719885300025125)
            ·
              refine ⟨3664780554509978493754711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19545496290719885300025125 3664780554509978493754711)
              ·
                refine ⟨5497170831764967740632067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664780554509978493754711 5497170831764967740632067)
                ·
                  refine ⟨8245756247647451610948101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5497170831764967740632067 8245756247647451610948101)
                  ·
                    refine ⟨1546079296433897177052769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8245756247647451610948101 1546079296433897177052769)
                    ·
                      refine ⟨1159559472325422882789577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546079296433897177052769 1159559472325422882789577)
                      ·
                        rfl

theorem cell23_2258234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_2258234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258234 prefixEnd_2258234 := by exact prefixLift 2258234
  have htrace : WordTrace (prefixWord ++ tailWord_2258234) baseStart_2258234 baseEnd_2258234 := by
    simpa [prefixWord, tailWord_2258234, baseEnd_2258234] using wordTrace_append hprefix tailTrace_2258234
  have hstable : (prefixWord ++ tailWord_2258234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258234).length < 2 ^ (prefixWord ++ tailWord_2258234).sum := by decide
  have hdescent : baseEnd_2258234 < baseStart_2258234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258240 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 7]
def baseStart_2258240 : Nat := 118140960795 + 2258240 * 2 ^ 59
def prefixEnd_2258240 : Nat := 4983230072969 + 3 ^ 40 * 2258240 * 2
def baseEnd_2258240 : Nat := 128840283689927762146061

theorem tailTrace_2258240 : CollatzResearch.WordTrace tailWord_2258240 prefixEnd_2258240 128840283689927762146061 := by
  unfold tailWord_2258240
  simp only [CollatzResearch.WordTrace]
  refine ⟨41182389669394815765910087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54909852892526421021213449 41182389669394815765910087)
  ·
    refine ⟨61773584504092223648865131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41182389669394815765910087 61773584504092223648865131)
    ·
      refine ⟨92660376756138335473297697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61773584504092223648865131 92660376756138335473297697)
      ·
        refine ⟨69495282567103751604973273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92660376756138335473297697 69495282567103751604973273)
        ·
          refine ⟨52121461925327813703729955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69495282567103751604973273 52121461925327813703729955)
          ·
            refine ⟨78182192887991720555594933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52121461925327813703729955 78182192887991720555594933)
            ·
              refine ⟨7329580583249223802087025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78182192887991720555594933 7329580583249223802087025)
              ·
                refine ⟨5497185437436917851565269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7329580583249223802087025 5497185437436917851565269)
                ·
                  refine ⟨128840283689927762146061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5497185437436917851565269 128840283689927762146061)
                  ·
                    rfl

theorem cell23_2258240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 7].length) (baseStart_2258240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258240 prefixEnd_2258240 := by exact prefixLift 2258240
  have htrace : WordTrace (prefixWord ++ tailWord_2258240) baseStart_2258240 baseEnd_2258240 := by
    simpa [prefixWord, tailWord_2258240, baseEnd_2258240] using wordTrace_append hprefix tailTrace_2258240
  have hstable : (prefixWord ++ tailWord_2258240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258240).length < 2 ^ (prefixWord ++ tailWord_2258240).sum := by decide
  have hdescent : baseEnd_2258240 < baseStart_2258240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258274 : List Nat := [3, 3, 2, 1, 1, 1, 1, 6, 5]
def baseStart_2258274 : Nat := 118140960795 + 2258274 * 2 ^ 59
def prefixEnd_2258274 : Nat := 4983230072969 + 3 ^ 40 * 2258274 * 2
def baseEnd_2258274 : Nat := 128842223505733636254377

theorem tailTrace_2258274 : CollatzResearch.WordTrace tailWord_2258274 prefixEnd_2258274 128842223505733636254377 := by
  unfold tailWord_2258274
  simp only [CollatzResearch.WordTrace]
  refine ⟨20591504855166613834639469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54910679613777636892371917 20591504855166613834639469)
  ·
    refine ⟨7721814320687480187989801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20591504855166613834639469 7721814320687480187989801)
    ·
      refine ⟨5791360740515610140992351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7721814320687480187989801 5791360740515610140992351)
      ·
        refine ⟨8687041110773415211488527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5791360740515610140992351 8687041110773415211488527)
        ·
          refine ⟨13030561666160122817232791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8687041110773415211488527 13030561666160122817232791)
          ·
            refine ⟨19545842499240184225849187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13030561666160122817232791 19545842499240184225849187)
            ·
              refine ⟨29318763748860276338773781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19545842499240184225849187 29318763748860276338773781)
              ·
                refine ⟨1374317050727825453380021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29318763748860276338773781 1374317050727825453380021)
                ·
                  refine ⟨128842223505733636254377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1374317050727825453380021 128842223505733636254377)
                  ·
                    rfl

theorem cell23_2258274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_2258274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258274 prefixEnd_2258274 := by exact prefixLift 2258274
  have htrace : WordTrace (prefixWord ++ tailWord_2258274) baseStart_2258274 baseEnd_2258274 := by
    simpa [prefixWord, tailWord_2258274, baseEnd_2258274] using wordTrace_append hprefix tailTrace_2258274
  have hstable : (prefixWord ++ tailWord_2258274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258274).length < 2 ^ (prefixWord ++ tailWord_2258274).sum := by decide
  have hdescent : baseEnd_2258274 < baseStart_2258274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258300 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_2258300 : Nat := 118140960795 + 2258300 * 2 ^ 59
def prefixEnd_2258300 : Nat := 4983230072969 + 3 ^ 40 * 2258300 * 2
def baseEnd_2258300 : Nat := 386531120682873208188091

theorem tailTrace_2258300 : CollatzResearch.WordTrace tailWord_2258300 prefixEnd_2258300 386531120682873208188091 := by
  unfold tailWord_2258300
  simp only [CollatzResearch.WordTrace]
  refine ⟨41183483859286130889502177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54911311812381507852669569 41183483859286130889502177)
  ·
    refine ⟨30887612894464598167126633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41183483859286130889502177 30887612894464598167126633)
    ·
      refine ⟨23165709670848448625344975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30887612894464598167126633 23165709670848448625344975)
      ·
        refine ⟨34748564506272672938017463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23165709670848448625344975 34748564506272672938017463)
        ·
          refine ⟨52122846759409009407026195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34748564506272672938017463 52122846759409009407026195)
          ·
            refine ⟨78184270139113514110539293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52122846759409009407026195 78184270139113514110539293)
            ·
              refine ⟨29319101302167567791452235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78184270139113514110539293 29319101302167567791452235)
              ·
                refine ⟨43978651953251351687178353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29319101302167567791452235 43978651953251351687178353)
                ·
                  refine ⟨32983988964938513765383765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43978651953251351687178353 32983988964938513765383765)
                  ·
                    refine ⟨386531120682873208188091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32983988964938513765383765 386531120682873208188091)
                    ·
                      rfl

theorem cell23_2258300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_2258300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258300 prefixEnd_2258300 := by exact prefixLift 2258300
  have htrace : WordTrace (prefixWord ++ tailWord_2258300) baseStart_2258300 baseEnd_2258300 := by
    simpa [prefixWord, tailWord_2258300, baseEnd_2258300] using wordTrace_append hprefix tailTrace_2258300
  have hstable : (prefixWord ++ tailWord_2258300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258300).length < 2 ^ (prefixWord ++ tailWord_2258300).sum := by decide
  have hdescent : baseEnd_2258300 < baseStart_2258300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258307 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 4]
def baseStart_2258307 : Nat := 118140960795 + 2258307 * 2 ^ 59
def prefixEnd_2258307 : Nat := 4983230072969 + 3 ^ 40 * 2258307 * 2
def baseEnd_2258307 : Nat := 1159596956413201097176741

theorem tailTrace_2258307 : CollatzResearch.WordTrace tailWord_2258307 prefixEnd_2258307 1159596956413201097176741 := by
  unfold tailWord_2258307
  simp only [CollatzResearch.WordTrace]
  refine ⟨82367223029546901974509175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54911482019697934649672783 82367223029546901974509175)
  ·
    refine ⟨123550834544320352961763763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82367223029546901974509175 123550834544320352961763763)
    ·
      refine ⟨185326251816480529442645645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123550834544320352961763763 185326251816480529442645645)
      ·
        refine ⟨69497344431180198540992117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185326251816480529442645645 69497344431180198540992117)
        ·
          refine ⟨6515376040423143613218011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69497344431180198540992117 6515376040423143613218011)
          ·
            refine ⟨9773064060634715419827017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515376040423143613218011 9773064060634715419827017)
            ·
              refine ⟨7329798045476036564870263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9773064060634715419827017 7329798045476036564870263)
              ·
                refine ⟨10994697068214054847305395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7329798045476036564870263 10994697068214054847305395)
                ·
                  refine ⟨16492045602321082270958093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10994697068214054847305395 16492045602321082270958093)
                  ·
                    refine ⟨6184517100870405851609285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16492045602321082270958093 6184517100870405851609285)
                    ·
                      refine ⟨1159596956413201097176741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6184517100870405851609285 1159596956413201097176741)
                      ·
                        rfl

theorem cell23_2258307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_2258307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258307 prefixEnd_2258307 := by exact prefixLift 2258307
  have htrace : WordTrace (prefixWord ++ tailWord_2258307) baseStart_2258307 baseEnd_2258307 := by
    simpa [prefixWord, tailWord_2258307, baseEnd_2258307] using wordTrace_append hprefix tailTrace_2258307
  have hstable : (prefixWord ++ tailWord_2258307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258307).length < 2 ^ (prefixWord ++ tailWord_2258307).sum := by decide
  have hdescent : baseEnd_2258307 < baseStart_2258307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258324 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2258324 : Nat := 118140960795 + 2258324 * 2 ^ 59
def prefixEnd_2258324 : Nat := 4983230072969 + 3 ^ 40 * 2258324 * 2
def baseEnd_2258324 : Nat := 1159605685584327530664163

theorem tailTrace_2258324 : CollatzResearch.WordTrace tailWord_2258324 prefixEnd_2258324 1159605685584327530664163 := by
  unfold tailWord_2258324
  simp only [CollatzResearch.WordTrace]
  refine ⟨41183921535242656938939013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54911895380323542585252017 41183921535242656938939013)
  ·
    refine ⟨7721985287857998176051065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41183921535242656938939013 7721985287857998176051065)
    ·
      refine ⟨5791488965893498632038299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7721985287857998176051065 5791488965893498632038299)
      ·
        refine ⟨8687233448840247948057449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5791488965893498632038299 8687233448840247948057449)
        ·
          refine ⟨6515425086630185961043087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8687233448840247948057449 6515425086630185961043087)
          ·
            refine ⟨9773137629945278941564631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515425086630185961043087 9773137629945278941564631)
            ·
              refine ⟨14659706444917918412346947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9773137629945278941564631 14659706444917918412346947)
              ·
                refine ⟨21989559667376877618520421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14659706444917918412346947 21989559667376877618520421)
                ·
                  refine ⟨4123042437633164553472579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21989559667376877618520421 4123042437633164553472579)
                  ·
                    refine ⟨6184563656449746830208869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123042437633164553472579 6184563656449746830208869)
                    ·
                      refine ⟨1159605685584327530664163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6184563656449746830208869 1159605685584327530664163)
                      ·
                        rfl

theorem cell23_2258324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2258324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258324 prefixEnd_2258324 := by exact prefixLift 2258324
  have htrace : WordTrace (prefixWord ++ tailWord_2258324) baseStart_2258324 baseEnd_2258324 := by
    simpa [prefixWord, tailWord_2258324, baseEnd_2258324] using wordTrace_append hprefix tailTrace_2258324
  have hstable : (prefixWord ++ tailWord_2258324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258324).length < 2 ^ (prefixWord ++ tailWord_2258324).sum := by decide
  have hdescent : baseEnd_2258324 < baseStart_2258324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258361 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2258361 : Nat := 118140960795 + 2258361 * 2 ^ 59
def prefixEnd_2258361 : Nat := 4983230072969 + 3 ^ 40 * 2258361 * 2
def baseEnd_2258361 : Nat := 1159624684368543885901493

theorem tailTrace_2258361 : CollatzResearch.WordTrace tailWord_2258361 prefixEnd_2258361 1159624684368543885901493 := by
  unfold tailWord_2258361
  simp only [CollatzResearch.WordTrace]
  refine ⟨82369192571351269196974937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54912795047567512797983291 82369192571351269196974937)
  ·
    refine ⟨61776894428513451897731203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82369192571351269196974937 61776894428513451897731203)
    ·
      refine ⟨92665341642770177846596805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61776894428513451897731203 92665341642770177846596805)
      ·
        refine ⟨17374751558019408346236901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92665341642770177846596805 17374751558019408346236901)
        ·
          refine ⟨3257765917128639064919419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17374751558019408346236901 3257765917128639064919419)
          ·
            refine ⟨4886648875692958597379129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3257765917128639064919419 4886648875692958597379129)
            ·
              refine ⟨3664986656769718948034347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4886648875692958597379129 3664986656769718948034347)
              ·
                refine ⟨5497479985154578422051521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664986656769718948034347 5497479985154578422051521)
                ·
                  refine ⟨4123109988865933816538641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5497479985154578422051521 4123109988865933816538641)
                  ·
                    refine ⟨3092332491649450362403981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4123109988865933816538641 3092332491649450362403981)
                    ·
                      refine ⟨1159624684368543885901493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3092332491649450362403981 1159624684368543885901493)
                      ·
                        rfl

theorem cell23_2258361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2258361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258361 prefixEnd_2258361 := by exact prefixLift 2258361
  have htrace : WordTrace (prefixWord ++ tailWord_2258361) baseStart_2258361 baseEnd_2258361 := by
    simpa [prefixWord, tailWord_2258361, baseEnd_2258361] using wordTrace_append hprefix tailTrace_2258361
  have hstable : (prefixWord ++ tailWord_2258361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258361).length < 2 ^ (prefixWord ++ tailWord_2258361).sum := by decide
  have hdescent : baseEnd_2258361 < baseStart_2258361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258414 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2258414 : Nat := 118140960795 + 2258414 * 2 ^ 59
def prefixEnd_2258414 : Nat := 4983230072969 + 3 ^ 40 * 2258414 * 2
def baseEnd_2258414 : Nat := 1159651898843232178538749

theorem tailTrace_2258414 : CollatzResearch.WordTrace tailWord_2258414 prefixEnd_2258414 1159651898843232178538749 := by
  unfold tailWord_2258414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10296390705019907406081787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54914083760106172832436197 10296390705019907406081787)
  ·
    refine ⟨15444586057529861109122681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10296390705019907406081787 15444586057529861109122681)
    ·
      refine ⟨11583439543147395831842011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15444586057529861109122681 11583439543147395831842011)
      ·
        refine ⟨17375159314721093747763017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11583439543147395831842011 17375159314721093747763017)
        ·
          refine ⟨13031369486040820310822263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17375159314721093747763017 13031369486040820310822263)
          ·
            refine ⟨19547054229061230466233395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13031369486040820310822263 19547054229061230466233395)
            ·
              refine ⟨29320581343591845699350093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19547054229061230466233395 29320581343591845699350093)
              ·
                refine ⟨10995218003846942137256285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29320581343591845699350093 10995218003846942137256285)
                ·
                  refine ⟨4123206751442603301471107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10995218003846942137256285 4123206751442603301471107)
                  ·
                    refine ⟨6184810127163904952206661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123206751442603301471107 6184810127163904952206661)
                    ·
                      refine ⟨1159651898843232178538749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6184810127163904952206661 1159651898843232178538749)
                      ·
                        rfl

theorem cell23_2258414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2258414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258414 prefixEnd_2258414 := by exact prefixLift 2258414
  have htrace : WordTrace (prefixWord ++ tailWord_2258414) baseStart_2258414 baseEnd_2258414 := by
    simpa [prefixWord, tailWord_2258414, baseEnd_2258414] using wordTrace_append hprefix tailTrace_2258414
  have hstable : (prefixWord ++ tailWord_2258414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258414).length < 2 ^ (prefixWord ++ tailWord_2258414).sum := by decide
  have hdescent : baseEnd_2258414 < baseStart_2258414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258418 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2258418 : Nat := 118140960795 + 2258418 * 2 ^ 59
def prefixEnd_2258418 : Nat := 4983230072969 + 3 ^ 40 * 2258418 * 2
def baseEnd_2258418 : Nat := 1159653952765850162888731

theorem tailTrace_2258418 : CollatzResearch.WordTrace tailWord_2258418 prefixEnd_2258418 1159653952765850162888731 := by
  unfold tailWord_2258418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20592817883036191982949977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54914181021429845287866605 20592817883036191982949977)
  ·
    refine ⟨15444613412277143987212483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20592817883036191982949977 15444613412277143987212483)
    ·
      refine ⟨23166920118415715980818725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15444613412277143987212483 23166920118415715980818725)
      ·
        refine ⟨4343797522202946746403511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23166920118415715980818725 4343797522202946746403511)
        ·
          refine ⟨6515696283304420119605267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343797522202946746403511 6515696283304420119605267)
          ·
            refine ⟨9773544424956630179407901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515696283304420119605267 9773544424956630179407901)
            ·
              refine ⟨3665079159358736317277963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9773544424956630179407901 3665079159358736317277963)
              ·
                refine ⟨5497618739038104475916945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3665079159358736317277963 5497618739038104475916945)
                ·
                  refine ⟨4123214054278578356937709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5497618739038104475916945 4123214054278578356937709)
                  ·
                    refine ⟨1546205270354466883851641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4123214054278578356937709 1546205270354466883851641)
                    ·
                      refine ⟨1159653952765850162888731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546205270354466883851641 1159653952765850162888731)
                      ·
                        rfl

theorem cell23_2258418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2258418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258418 prefixEnd_2258418 := by exact prefixLift 2258418
  have htrace : WordTrace (prefixWord ++ tailWord_2258418) baseStart_2258418 baseEnd_2258418 := by
    simpa [prefixWord, tailWord_2258418, baseEnd_2258418] using wordTrace_append hprefix tailTrace_2258418
  have hstable : (prefixWord ++ tailWord_2258418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258418).length < 2 ^ (prefixWord ++ tailWord_2258418).sum := by decide
  have hdescent : baseEnd_2258418 < baseStart_2258418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258462 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2258462 : Nat := 118140960795 + 2258462 * 2 ^ 59
def prefixEnd_2258462 : Nat := 4983230072969 + 3 ^ 40 * 2258462 * 2
def baseEnd_2258462 : Nat := 386558848638215996912843

theorem tailTrace_2258462 : CollatzResearch.WordTrace tailWord_2258462 prefixEnd_2258462 386558848638215996912843 := by
  unfold tailWord_2258462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10296609542998170430800205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54915250895990242297601093 10296609542998170430800205)
  ·
    refine ⟨3861228578624313911550077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10296609542998170430800205 3861228578624313911550077)
    ·
      refine ⟨1447960716984117716831279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3861228578624313911550077 1447960716984117716831279)
      ·
        refine ⟨2171941075476176575246919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447960716984117716831279 2171941075476176575246919)
        ·
          refine ⟨3257911613214264862870379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171941075476176575246919 3257911613214264862870379)
          ·
            refine ⟨4886867419821397294305569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3257911613214264862870379 4886867419821397294305569)
            ·
              refine ⟨3665150564866047970729177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4886867419821397294305569 3665150564866047970729177)
              ·
                refine ⟨2748862923649535978046883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3665150564866047970729177 2748862923649535978046883)
                ·
                  refine ⟨4123294385474303967070325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748862923649535978046883 4123294385474303967070325)
                  ·
                    refine ⟨386558848638215996912843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4123294385474303967070325 386558848638215996912843)
                    ·
                      rfl

theorem cell23_2258462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2258462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258462 prefixEnd_2258462 := by exact prefixLift 2258462
  have htrace : WordTrace (prefixWord ++ tailWord_2258462) baseStart_2258462 baseEnd_2258462 := by
    simpa [prefixWord, tailWord_2258462, baseEnd_2258462] using wordTrace_append hprefix tailTrace_2258462
  have hstable : (prefixWord ++ tailWord_2258462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258462).length < 2 ^ (prefixWord ++ tailWord_2258462).sum := by decide
  have hdescent : baseEnd_2258462 < baseStart_2258462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258507 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 5]
def baseStart_2258507 : Nat := 118140960795 + 2258507 * 2 ^ 59
def prefixEnd_2258507 : Nat := 4983230072969 + 3 ^ 40 * 2258507 * 2
def baseEnd_2258507 : Nat := 1159699652544100314675821

theorem tailTrace_2258507 : CollatzResearch.WordTrace tailWord_2258507 prefixEnd_2258507 1159699652544100314675821 := by
  unfold tailWord_2258507
  simp only [CollatzResearch.WordTrace]
  refine ⟨82374517628822336131789775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54916345085881557421193183 82374517628822336131789775)
  ·
    refine ⟨123561776443233504197684663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82374517628822336131789775 123561776443233504197684663)
    ·
      refine ⟨185342664664850256296526995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123561776443233504197684663 185342664664850256296526995)
      ·
        refine ⟨278013996997275384444790493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185342664664850256296526995 278013996997275384444790493)
        ·
          refine ⟨104255248873978269166796435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278013996997275384444790493 104255248873978269166796435)
          ·
            refine ⟨156382873310967403750194653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104255248873978269166796435 156382873310967403750194653)
            ·
              refine ⟨58643577491612776406322995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156382873310967403750194653 58643577491612776406322995)
              ·
                refine ⟨87965366237419164609484493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58643577491612776406322995 87965366237419164609484493)
                ·
                  refine ⟨32987012339032186728556685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87965366237419164609484493 32987012339032186728556685)
                  ·
                    refine ⟨12370129627137070023208757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32987012339032186728556685 12370129627137070023208757)
                    ·
                      refine ⟨1159699652544100314675821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12370129627137070023208757 1159699652544100314675821)
                      ·
                        rfl

theorem cell23_2258507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_2258507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258507 prefixEnd_2258507 := by exact prefixLift 2258507
  have htrace : WordTrace (prefixWord ++ tailWord_2258507) baseStart_2258507 baseEnd_2258507 := by
    simpa [prefixWord, tailWord_2258507, baseEnd_2258507] using wordTrace_append hprefix tailTrace_2258507
  have hstable : (prefixWord ++ tailWord_2258507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258507).length < 2 ^ (prefixWord ++ tailWord_2258507).sum := by decide
  have hdescent : baseEnd_2258507 < baseStart_2258507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258538 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_2258538 : Nat := 118140960795 + 2258538 * 2 ^ 59
def prefixEnd_2258538 : Nat := 4983230072969 + 3 ^ 40 * 2258538 * 2
def baseEnd_2258538 : Nat := 1159715570444389693388179

theorem tailTrace_2258538 : CollatzResearch.WordTrace tailWord_2258538 prefixEnd_2258538 1159715570444389693388179 := by
  unfold tailWord_2258538
  simp only [CollatzResearch.WordTrace]
  refine ⟨20593912072927507106542067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54917098861140018950778845 20593912072927507106542067)
  ·
    refine ⟨30890868109391260659813101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20593912072927507106542067 30890868109391260659813101)
    ·
      refine ⟨11584075541021722747429913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30890868109391260659813101 11584075541021722747429913)
      ·
        refine ⟨8688056655766292060572435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11584075541021722747429913 8688056655766292060572435)
        ·
          refine ⟨13032084983649438090858653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8688056655766292060572435 13032084983649438090858653)
          ·
            refine ⟨4887031868868539284071995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13032084983649438090858653 4887031868868539284071995)
            ·
              refine ⟨7330547803302808926107993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887031868868539284071995 7330547803302808926107993)
              ·
                refine ⟨5497910852477106694580995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7330547803302808926107993 5497910852477106694580995)
                ·
                  refine ⟨8246866278715660041871493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5497910852477106694580995 8246866278715660041871493)
                  ·
                    refine ⟨1546287427259186257850905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8246866278715660041871493 1546287427259186257850905)
                    ·
                      refine ⟨1159715570444389693388179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1546287427259186257850905 1159715570444389693388179)
                      ·
                        rfl

theorem cell23_2258538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_2258538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2258538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2258538 prefixEnd_2258538 := by exact prefixLift 2258538
  have htrace : WordTrace (prefixWord ++ tailWord_2258538) baseStart_2258538 baseEnd_2258538 := by
    simpa [prefixWord, tailWord_2258538, baseEnd_2258538] using wordTrace_append hprefix tailTrace_2258538
  have hstable : (prefixWord ++ tailWord_2258538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258538).length < 2 ^ (prefixWord ++ tailWord_2258538).sum := by decide
  have hdescent : baseEnd_2258538 < baseStart_2258538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
