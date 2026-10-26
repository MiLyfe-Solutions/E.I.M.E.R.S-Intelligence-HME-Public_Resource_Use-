import V185TrunkScan19Chunk043

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_441314 : List Nat := [3, 3, 3, 1, 1, 1, 7]
def baseStart_441314 : Nat := 118140960795 + 441314 * 2 ^ 59
def prefixEnd_441314 : Nat := 4983230072969 + 3 ^ 40 * 441314 * 2
def baseEnd_441314 : Nat := 44761718826348956176877

theorem tailTrace_441314 : CollatzResearch.WordTrace tailWord_441314 prefixEnd_441314 44761718826348956176877 := by
  unfold tailWord_441314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4024010980800555818940749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10730695948801482183841997 4024010980800555818940749)
  ·
    refine ⟨1509004117800208432102781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4024010980800555818940749 1509004117800208432102781)
    ·
      refine ⟨565876544175078162038543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1509004117800208432102781 565876544175078162038543)
      ·
        refine ⟨848814816262617243057815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565876544175078162038543 848814816262617243057815)
        ·
          refine ⟨1273222224393925864586723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848814816262617243057815 1273222224393925864586723)
          ·
            refine ⟨1909833336590888796880085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273222224393925864586723 1909833336590888796880085)
            ·
              refine ⟨44761718826348956176877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1909833336590888796880085 44761718826348956176877)
              ·
                rfl

theorem cell19_441314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_441314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441314 prefixEnd_441314 := by exact prefixLift 441314
  have htrace : WordTrace (prefixWord ++ tailWord_441314) baseStart_441314 baseEnd_441314 := by
    simpa [prefixWord, tailWord_441314, baseEnd_441314] using wordTrace_append hprefix tailTrace_441314
  have hstable : (prefixWord ++ tailWord_441314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441314).length < 2 ^ (prefixWord ++ tailWord_441314).sum := by decide
  have hdescent : baseEnd_441314 < baseStart_441314 := by decide
  rcases family_descends (prefixWord ++ tailWord_441314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441354 : List Nat := [3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_441354 : Nat := 118140960795 + 441354 * 2 ^ 59
def prefixEnd_441354 : Nat := 4983230072969 + 3 ^ 40 * 441354 * 2
def baseEnd_441354 : Nat := 134297327872338627641633

theorem tailTrace_441354 : CollatzResearch.WordTrace tailWord_441354 prefixEnd_441354 134297327872338627641633 := by
  unfold tailWord_441354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4024375710764327526804779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10731668562038206738146077 4024375710764327526804779)
  ·
    refine ⟨6036563566146491290207169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4024375710764327526804779 6036563566146491290207169)
    ·
      refine ⟨4527422674609868467655377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6036563566146491290207169 4527422674609868467655377)
      ·
        refine ⟨3395567005957401350741533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4527422674609868467655377 3395567005957401350741533)
        ·
          refine ⟨1273337627234025506528075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3395567005957401350741533 1273337627234025506528075)
          ·
            refine ⟨1910006440851038259792113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273337627234025506528075 1910006440851038259792113)
            ·
              refine ⟨1432504830638278694844085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910006440851038259792113 1432504830638278694844085)
              ·
                refine ⟨134297327872338627641633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1432504830638278694844085 134297327872338627641633)
                ·
                  rfl

theorem cell19_441354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_441354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441354 prefixEnd_441354 := by exact prefixLift 441354
  have htrace : WordTrace (prefixWord ++ tailWord_441354) baseStart_441354 baseEnd_441354 := by
    simpa [prefixWord, tailWord_441354, baseEnd_441354] using wordTrace_append hprefix tailTrace_441354
  have hstable : (prefixWord ++ tailWord_441354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441354).length < 2 ^ (prefixWord ++ tailWord_441354).sum := by decide
  have hdescent : baseEnd_441354 < baseStart_441354 := by decide
  rcases family_descends (prefixWord ++ tailWord_441354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441373 : List Nat := [1, 4, 2, 2, 3, 7]
def baseStart_441373 : Nat := 118140960795 + 441373 * 2 ^ 59
def prefixEnd_441373 : Nat := 4983230072969 + 3 ^ 40 * 441373 * 2
def baseEnd_441373 : Nat := 14922567698239134802151

theorem tailTrace_441373 : CollatzResearch.WordTrace tailWord_441373 prefixEnd_441373 14922567698239134802151 := by
  unfold tailWord_441373
  simp only [CollatzResearch.WordTrace]
  refine ⟨16098195829988476352160773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10732130553325650901440515 16098195829988476352160773)
  ·
    refine ⟨3018411718122839316030145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16098195829988476352160773 3018411718122839316030145)
    ·
      refine ⟨2263808788592129487022609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3018411718122839316030145 2263808788592129487022609)
      ·
        refine ⟨1697856591444097115266957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2263808788592129487022609 1697856591444097115266957)
        ·
          refine ⟨636696221791536418225109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1697856591444097115266957 636696221791536418225109)
          ·
            refine ⟨14922567698239134802151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 636696221791536418225109 14922567698239134802151)
            ·
              rfl

theorem cell19_441373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 7].length) (baseStart_441373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441373 prefixEnd_441373 := by exact prefixLift 441373
  have htrace : WordTrace (prefixWord ++ tailWord_441373) baseStart_441373 baseEnd_441373 := by
    simpa [prefixWord, tailWord_441373, baseEnd_441373] using wordTrace_append hprefix tailTrace_441373
  have hstable : (prefixWord ++ tailWord_441373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441373).length < 2 ^ (prefixWord ++ tailWord_441373).sum := by decide
  have hdescent : baseEnd_441373 < baseStart_441373 := by decide
  rcases family_descends (prefixWord ++ tailWord_441373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441375 : List Nat := [1, 1, 2, 4, 1, 10]
def baseStart_441375 : Nat := 118140960795 + 441375 * 2 ^ 59
def prefixEnd_441375 : Nat := 4983230072969 + 3 ^ 40 * 441375 * 2
def baseEnd_441375 : Nat := 14922635317090755686101

theorem tailTrace_441375 : CollatzResearch.WordTrace tailWord_441375 prefixEnd_441375 14922635317090755686101 := by
  unfold tailWord_441375
  simp only [CollatzResearch.WordTrace]
  refine ⟨16098268775981230693733579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10732179183987487129155719 16098268775981230693733579)
  ·
    refine ⟨24147403163971846040600369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16098268775981230693733579 24147403163971846040600369)
    ·
      refine ⟨18110552372978884530450277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24147403163971846040600369 18110552372978884530450277)
      ·
        refine ⟨3395728569933540849459427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18110552372978884530450277 3395728569933540849459427)
        ·
          refine ⟨5093592854900311274189141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395728569933540849459427 5093592854900311274189141)
          ·
            refine ⟨14922635317090755686101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5093592854900311274189141 14922635317090755686101)
            ·
              rfl

theorem cell19_441375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 10].length) (baseStart_441375 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441375 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441375 prefixEnd_441375 := by exact prefixLift 441375
  have htrace : WordTrace (prefixWord ++ tailWord_441375) baseStart_441375 baseEnd_441375 := by
    simpa [prefixWord, tailWord_441375, baseEnd_441375] using wordTrace_append hprefix tailTrace_441375
  have hstable : (prefixWord ++ tailWord_441375).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441375).length < 2 ^ (prefixWord ++ tailWord_441375).sum := by decide
  have hdescent : baseEnd_441375 < baseStart_441375 := by decide
  rcases family_descends (prefixWord ++ tailWord_441375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441411 : List Nat := [1, 1, 1, 3, 1, 2, 7, 3]
def baseStart_441411 : Nat := 118140960795 + 441411 * 2 ^ 59
def prefixEnd_441411 : Nat := 4983230072969 + 3 ^ 40 * 441411 * 2
def baseEnd_441411 : Nat := 134314672107779384374811

theorem tailTrace_441411 : CollatzResearch.WordTrace tailWord_441411 prefixEnd_441411 134314672107779384374811 := by
  unfold tailWord_441411
  simp only [CollatzResearch.WordTrace]
  refine ⟨16099581803850808842044087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10733054535900539228029391 16099581803850808842044087)
  ·
    refine ⟨24149372705776213263066131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16099581803850808842044087 24149372705776213263066131)
    ·
      refine ⟨36224059058664319894599197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24149372705776213263066131 36224059058664319894599197)
      ·
        refine ⟨13584022146999119960474699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36224059058664319894599197 13584022146999119960474699)
        ·
          refine ⟨20376033220498679940712049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584022146999119960474699 20376033220498679940712049)
          ·
            refine ⟨15282024915374009955534037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20376033220498679940712049 15282024915374009955534037)
            ·
              refine ⟨358172458954078358332829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15282024915374009955534037 358172458954078358332829)
              ·
                refine ⟨134314672107779384374811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358172458954078358332829 134314672107779384374811)
                ·
                  rfl

theorem cell19_441411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_441411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441411 prefixEnd_441411 := by exact prefixLift 441411
  have htrace : WordTrace (prefixWord ++ tailWord_441411) baseStart_441411 baseEnd_441411 := by
    simpa [prefixWord, tailWord_441411, baseEnd_441411] using wordTrace_append hprefix tailTrace_441411
  have hstable : (prefixWord ++ tailWord_441411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441411).length < 2 ^ (prefixWord ++ tailWord_441411).sum := by decide
  have hdescent : baseEnd_441411 < baseStart_441411 := by decide
  rcases family_descends (prefixWord ++ tailWord_441411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441413 : List Nat := [1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_441413 : Nat := 118140960795 + 441413 * 2 ^ 59
def prefixEnd_441413 : Nat := 4983230072969 + 3 ^ 40 * 441413 * 2
def baseEnd_441413 : Nat := 134315280677443972330361

theorem tailTrace_441413 : CollatzResearch.WordTrace tailWord_441413 prefixEnd_441413 134315280677443972330361 := by
  unfold tailWord_441413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16099654749843563183616893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10733103166562375455744595 16099654749843563183616893)
  ·
    refine ⟨6037370531191336193856335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16099654749843563183616893 6037370531191336193856335)
    ·
      refine ⟨9056055796787004290784503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6037370531191336193856335 9056055796787004290784503)
      ·
        refine ⟨13584083695180506436176755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056055796787004290784503 13584083695180506436176755)
        ·
          refine ⟨20376125542770759654265133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584083695180506436176755 20376125542770759654265133)
          ·
            refine ⟨7641047078539034870349425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20376125542770759654265133 7641047078539034870349425)
            ·
              refine ⟨5730785308904276152762069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7641047078539034870349425 5730785308904276152762069)
              ·
                refine ⟨134315280677443972330361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5730785308904276152762069 134315280677443972330361)
                ·
                  rfl

theorem cell19_441413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_441413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441413 prefixEnd_441413 := by exact prefixLift 441413
  have htrace : WordTrace (prefixWord ++ tailWord_441413) baseStart_441413 baseEnd_441413 := by
    simpa [prefixWord, tailWord_441413, baseEnd_441413] using wordTrace_append hprefix tailTrace_441413
  have hstable : (prefixWord ++ tailWord_441413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441413).length < 2 ^ (prefixWord ++ tailWord_441413).sum := by decide
  have hdescent : baseEnd_441413 < baseStart_441413 := by decide
  rcases family_descends (prefixWord ++ tailWord_441413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441432 : List Nat := [2, 1, 2, 2, 1, 3, 8]
def baseStart_441432 : Nat := 118140960795 + 441432 * 2 ^ 59
def prefixEnd_441432 : Nat := 4983230072969 + 3 ^ 40 * 441432 * 2
def baseEnd_441432 : Nat := 44773687363085852636029

theorem tailTrace_441432 : CollatzResearch.WordTrace tailWord_441432 prefixEnd_441432 44773687363085852636029 := by
  unfold tailWord_441432
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050173868387364714279275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10733565157849819619039033 8050173868387364714279275)
  ·
    refine ⟨12075260802581047071418913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8050173868387364714279275 12075260802581047071418913)
    ·
      refine ⟨9056445601935785303564185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12075260802581047071418913 9056445601935785303564185)
      ·
        refine ⟨6792334201451838977673139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9056445601935785303564185 6792334201451838977673139)
        ·
          refine ⟨10188501302177758466509709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6792334201451838977673139 10188501302177758466509709)
          ·
            refine ⟨3820687988316659424941141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10188501302177758466509709 3820687988316659424941141)
            ·
              refine ⟨44773687363085852636029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3820687988316659424941141 44773687363085852636029)
              ·
                rfl

theorem cell19_441432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_441432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441432 prefixEnd_441432 := by exact prefixLift 441432
  have htrace : WordTrace (prefixWord ++ tailWord_441432) baseStart_441432 baseEnd_441432 := by
    simpa [prefixWord, tailWord_441432, baseEnd_441432] using wordTrace_append hprefix tailTrace_441432
  have hstable : (prefixWord ++ tailWord_441432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441432).length < 2 ^ (prefixWord ++ tailWord_441432).sum := by decide
  have hdescent : baseEnd_441432 < baseStart_441432 := by decide
  rcases family_descends (prefixWord ++ tailWord_441432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441527 : List Nat := [1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_441527 : Nat := 118140960795 + 441527 * 2 ^ 59
def prefixEnd_441527 : Nat := 4983230072969 + 3 ^ 40 * 441527 * 2
def baseEnd_441527 : Nat := 134349969148325485796717

theorem tailTrace_441527 : CollatzResearch.WordTrace tailWord_441527 prefixEnd_441527 134349969148325485796717 := by
  unfold tailWord_441527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16103812671430560653266835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10735875114287040435511223 16103812671430560653266835)
  ·
    refine ⟨24155719007145840979900253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16103812671430560653266835 24155719007145840979900253)
    ·
      refine ⟨9058394627679690367462595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24155719007145840979900253 9058394627679690367462595)
      ·
        refine ⟨13587591941519535551193893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9058394627679690367462595 13587591941519535551193893)
        ·
          refine ⟨2547673489034912915848855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13587591941519535551193893 2547673489034912915848855)
          ·
            refine ⟨3821510233552369373773283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547673489034912915848855 3821510233552369373773283)
            ·
              refine ⟨5732265350328554060659925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821510233552369373773283 5732265350328554060659925)
              ·
                refine ⟨134349969148325485796717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5732265350328554060659925 134349969148325485796717)
                ·
                  rfl

theorem cell19_441527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_441527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441527 prefixEnd_441527 := by exact prefixLift 441527
  have htrace : WordTrace (prefixWord ++ tailWord_441527) baseStart_441527 baseEnd_441527 := by
    simpa [prefixWord, tailWord_441527, baseEnd_441527] using wordTrace_append hprefix tailTrace_441527
  have hstable : (prefixWord ++ tailWord_441527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441527).length < 2 ^ (prefixWord ++ tailWord_441527).sum := by decide
  have hdescent : baseEnd_441527 < baseStart_441527 := by decide
  rcases family_descends (prefixWord ++ tailWord_441527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441546 : List Nat := [3, 1, 2, 1, 3, 9]
def baseStart_441546 : Nat := 118140960795 + 441546 * 2 ^ 59
def prefixEnd_441546 : Nat := 4983230072969 + 3 ^ 40 * 441546 * 2
def baseEnd_441546 : Nat := 14928416728904341263827

theorem tailTrace_441546 : CollatzResearch.WordTrace tailWord_441546 prefixEnd_441546 14928416728904341263827 := by
  unfold tailWord_441546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026126414590431724552123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10736337105574484598805661 4026126414590431724552123)
  ·
    refine ⟨6039189621885647586828185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4026126414590431724552123 6039189621885647586828185)
    ·
      refine ⟨4529392216414235690121139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6039189621885647586828185 4529392216414235690121139)
      ·
        refine ⟨6794088324621353535181709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529392216414235690121139 6794088324621353535181709)
        ·
          refine ⟨2547783121733007575693141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6794088324621353535181709 2547783121733007575693141)
          ·
            refine ⟨14928416728904341263827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2547783121733007575693141 14928416728904341263827)
            ·
              rfl

theorem cell19_441546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 9].length) (baseStart_441546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441546 prefixEnd_441546 := by exact prefixLift 441546
  have htrace : WordTrace (prefixWord ++ tailWord_441546) baseStart_441546 baseEnd_441546 := by
    simpa [prefixWord, tailWord_441546, baseEnd_441546] using wordTrace_append hprefix tailTrace_441546
  have hstable : (prefixWord ++ tailWord_441546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441546).length < 2 ^ (prefixWord ++ tailWord_441546).sum := by decide
  have hdescent : baseEnd_441546 < baseStart_441546 := by decide
  rcases family_descends (prefixWord ++ tailWord_441546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441603 : List Nat := [1, 1, 1, 3, 2, 5, 6]
def baseStart_441603 : Nat := 118140960795 + 441603 * 2 ^ 59
def prefixEnd_441603 : Nat := 4983230072969 + 3 ^ 40 * 441603 * 2
def baseEnd_441603 : Nat := 44791031598526609369207

theorem tailTrace_441603 : CollatzResearch.WordTrace tailWord_441603 prefixEnd_441603 44791031598526609369207 := by
  unfold tailWord_441603
  simp only [CollatzResearch.WordTrace]
  refine ⟨16106584619155225633033463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10737723079436817088688975 16106584619155225633033463)
  ·
    refine ⟨24159876928732838449550195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16106584619155225633033463 24159876928732838449550195)
    ·
      refine ⟨36239815393099257674325293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24159876928732838449550195 36239815393099257674325293)
      ·
        refine ⟨13589930772412221627871985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36239815393099257674325293 13589930772412221627871985)
        ·
          refine ⟨10192448079309166220903989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13589930772412221627871985 10192448079309166220903989)
          ·
            refine ⟨955542007435234333209749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10192448079309166220903989 955542007435234333209749)
            ·
              refine ⟨44791031598526609369207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 955542007435234333209749 44791031598526609369207)
              ·
                rfl

theorem cell19_441603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_441603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441603 prefixEnd_441603 := by exact prefixLift 441603
  have htrace : WordTrace (prefixWord ++ tailWord_441603) baseStart_441603 baseEnd_441603 := by
    simpa [prefixWord, tailWord_441603, baseEnd_441603] using wordTrace_append hprefix tailTrace_441603
  have hstable : (prefixWord ++ tailWord_441603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441603).length < 2 ^ (prefixWord ++ tailWord_441603).sum := by decide
  have hdescent : baseEnd_441603 < baseStart_441603 := by decide
  rcases family_descends (prefixWord ++ tailWord_441603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441637 : List Nat := [1, 3, 1, 2, 4, 3, 2, 3]
def baseStart_441637 : Nat := 118140960795 + 441637 * 2 ^ 59
def prefixEnd_441637 : Nat := 4983230072969 + 3 ^ 40 * 441637 * 2
def baseEnd_441637 : Nat := 134383440479877823351973

theorem tailTrace_441637 : CollatzResearch.WordTrace tailWord_441637 prefixEnd_441637 134383440479877823351973 := by
  unfold tailWord_441637
  simp only [CollatzResearch.WordTrace]
  refine ⟨16107824701032049439771165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10738549800688032959847443 16107824701032049439771165)
  ·
    refine ⟨6040434262887018539914187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16107824701032049439771165 6040434262887018539914187)
    ·
      refine ⟨9060651394330527809871281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6040434262887018539914187 9060651394330527809871281)
      ·
        refine ⟨6795488545747895857403461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9060651394330527809871281 6795488545747895857403461)
        ·
          refine ⟨1274154102327730473263149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6795488545747895857403461 1274154102327730473263149)
          ·
            refine ⟨477807788372898927473681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1274154102327730473263149 477807788372898927473681)
            ·
              refine ⟨358355841279674195605261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477807788372898927473681 358355841279674195605261)
              ·
                refine ⟨134383440479877823351973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358355841279674195605261 134383440479877823351973)
                ·
                  rfl

theorem cell19_441637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_441637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441637 prefixEnd_441637 := by exact prefixLift 441637
  have htrace : WordTrace (prefixWord ++ tailWord_441637) baseStart_441637 baseEnd_441637 := by
    simpa [prefixWord, tailWord_441637, baseEnd_441637] using wordTrace_append hprefix tailTrace_441637
  have hstable : (prefixWord ++ tailWord_441637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441637).length < 2 ^ (prefixWord ++ tailWord_441637).sum := by decide
  have hdescent : baseEnd_441637 < baseStart_441637 := by decide
  rcases family_descends (prefixWord ++ tailWord_441637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441654 : List Nat := [5, 1, 2, 3, 1, 2, 5]
def baseStart_441654 : Nat := 118140960795 + 441654 * 2 ^ 59
def prefixEnd_441654 : Nat := 4983230072969 + 3 ^ 40 * 441654 * 2
def baseEnd_441654 : Nat := 44796204440675606991383

theorem tailTrace_441654 : CollatzResearch.WordTrace tailWord_441654 prefixEnd_441654 44796204440675606991383 := by
  unfold tailWord_441654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1006777796373153833946251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10738963161313640895426677 1006777796373153833946251)
  ·
    refine ⟨1510166694559730750919377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1006777796373153833946251 1510166694559730750919377)
    ·
      refine ⟨1132625020919798063189533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1510166694559730750919377 1132625020919798063189533)
      ·
        refine ⟨424734382844924273696075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1132625020919798063189533 424734382844924273696075)
        ·
          refine ⟨637101574267386410544113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424734382844924273696075 637101574267386410544113)
          ·
            refine ⟨477826180700539807908085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637101574267386410544113 477826180700539807908085)
            ·
              refine ⟨44796204440675606991383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 477826180700539807908085 44796204440675606991383)
              ·
                rfl

theorem cell19_441654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_441654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441654 prefixEnd_441654 := by exact prefixLift 441654
  have htrace : WordTrace (prefixWord ++ tailWord_441654) baseStart_441654 baseEnd_441654 := by
    simpa [prefixWord, tailWord_441654, baseEnd_441654] using wordTrace_append hprefix tailTrace_441654
  have hstable : (prefixWord ++ tailWord_441654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441654).length < 2 ^ (prefixWord ++ tailWord_441654).sum := by decide
  have hdescent : baseEnd_441654 < baseStart_441654 := by decide
  rcases family_descends (prefixWord ++ tailWord_441654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441660 : List Nat := [2, 2, 2, 2, 1, 3, 7]
def baseStart_441660 : Nat := 118140960795 + 441660 * 2 ^ 59
def prefixEnd_441660 : Nat := 4983230072969 + 3 ^ 40 * 441660 * 2
def baseEnd_441660 : Nat := 44796813010340194946933

theorem tailTrace_441660 : CollatzResearch.WordTrace tailWord_441660 prefixEnd_441660 44796813010340194946933 := by
  unfold tailWord_441660
  simp only [CollatzResearch.WordTrace]
  refine ⟨8054331789974362183929217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10739109053299149578572289 8054331789974362183929217)
  ·
    refine ⟨6040748842480771637946913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8054331789974362183929217 6040748842480771637946913)
    ·
      refine ⟨4530561631860578728460185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6040748842480771637946913 4530561631860578728460185)
      ·
        refine ⟨3397921223895434046345139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4530561631860578728460185 3397921223895434046345139)
        ·
          refine ⟨5096881835843151069517709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397921223895434046345139 5096881835843151069517709)
          ·
            refine ⟨1911330688441181651069141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5096881835843151069517709 1911330688441181651069141)
            ·
              refine ⟨44796813010340194946933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1911330688441181651069141 44796813010340194946933)
              ·
                rfl

theorem cell19_441660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_441660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441660 prefixEnd_441660 := by exact prefixLift 441660
  have htrace : WordTrace (prefixWord ++ tailWord_441660) baseStart_441660 baseEnd_441660 := by
    simpa [prefixWord, tailWord_441660, baseEnd_441660] using wordTrace_append hprefix tailTrace_441660
  have hstable : (prefixWord ++ tailWord_441660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441660).length < 2 ^ (prefixWord ++ tailWord_441660).sum := by decide
  have hdescent : baseEnd_441660 < baseStart_441660 := by decide
  rcases family_descends (prefixWord ++ tailWord_441660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441717 : List Nat := [1, 3, 4, 1, 10]
def baseStart_441717 : Nat := 118140960795 + 441717 * 2 ^ 59
def prefixEnd_441717 : Nat := 4983230072969 + 3 ^ 40 * 441717 * 2
def baseEnd_441717 : Nat := 4978066046905975613851

theorem tailTrace_441717 : CollatzResearch.WordTrace tailWord_441717 prefixEnd_441717 4978066046905975613851 := by
  unfold tailWord_441717
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110742540742223102683405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10740495027161482068455603 16110742540742223102683405)
  ·
    refine ⟨6041528452778333663506277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16110742540742223102683405 6041528452778333663506277)
    ·
      refine ⟨1132786584895937561907427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6041528452778333663506277 1132786584895937561907427)
      ·
        refine ⟨1699179877343906342861141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132786584895937561907427 1699179877343906342861141)
        ·
          refine ⟨4978066046905975613851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1699179877343906342861141 4978066046905975613851)
          ·
            rfl

theorem cell19_441717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 10].length) (baseStart_441717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441717 prefixEnd_441717 := by exact prefixLift 441717
  have htrace : WordTrace (prefixWord ++ tailWord_441717) baseStart_441717 baseEnd_441717 := by
    simpa [prefixWord, tailWord_441717, baseEnd_441717] using wordTrace_append hprefix tailTrace_441717
  have hstable : (prefixWord ++ tailWord_441717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441717).length < 2 ^ (prefixWord ++ tailWord_441717).sum := by decide
  have hdescent : baseEnd_441717 < baseStart_441717 := by decide
  rcases family_descends (prefixWord ++ tailWord_441717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441730 : List Nat := [3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_441730 : Nat := 118140960795 + 441730 * 2 ^ 59
def prefixEnd_441730 : Nat := 4983230072969 + 3 ^ 40 * 441730 * 2
def baseEnd_441730 : Nat := 134411738969281163285053

theorem tailTrace_441730 : CollatzResearch.WordTrace tailWord_441730 prefixEnd_441730 134411738969281163285053 := by
  unfold tailWord_441730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027804172423781580726661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10740811126463417548604429 4027804172423781580726661)
  ·
    refine ⟨755213282329459046386249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4027804172423781580726661 755213282329459046386249)
    ·
      refine ⟨566409961747094284789687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 755213282329459046386249 566409961747094284789687)
      ·
        refine ⟨849614942620641427184531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566409961747094284789687 849614942620641427184531)
        ·
          refine ⟨1274422413930962140776797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849614942620641427184531 1274422413930962140776797)
          ·
            refine ⟨477908405224110802791299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1274422413930962140776797 477908405224110802791299)
            ·
              refine ⟨716862607836166204186949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477908405224110802791299 716862607836166204186949)
              ·
                refine ⟨134411738969281163285053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 716862607836166204186949 134411738969281163285053)
                ·
                  rfl

theorem cell19_441730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_441730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441730 prefixEnd_441730 := by exact prefixLift 441730
  have htrace : WordTrace (prefixWord ++ tailWord_441730) baseStart_441730 baseEnd_441730 := by
    simpa [prefixWord, tailWord_441730, baseEnd_441730] using wordTrace_append hprefix tailTrace_441730
  have hstable : (prefixWord ++ tailWord_441730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441730).length < 2 ^ (prefixWord ++ tailWord_441730).sum := by decide
  have hdescent : baseEnd_441730 < baseStart_441730 := by decide
  rcases family_descends (prefixWord ++ tailWord_441730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441753 : List Nat := [1, 2, 1, 2, 1, 6, 3, 3]
def baseStart_441753 : Nat := 118140960795 + 441753 * 2 ^ 59
def prefixEnd_441753 : Nat := 4983230072969 + 3 ^ 40 * 441753 * 2
def baseEnd_441753 : Nat := 134418737520423924773879

theorem tailTrace_441753 : CollatzResearch.WordTrace tailWord_441753 prefixEnd_441753 134418737520423924773879 := by
  unfold tailWord_441753
  simp only [CollatzResearch.WordTrace]
  refine ⟨16112055568611801250993913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10741370379074534167329275 16112055568611801250993913)
  ·
    refine ⟨12084041676458850938245435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16112055568611801250993913 12084041676458850938245435)
    ·
      refine ⟨18126062514688276407368153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12084041676458850938245435 18126062514688276407368153)
      ·
        refine ⟨13594546886016207305526115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18126062514688276407368153 13594546886016207305526115)
        ·
          refine ⟨20391820329024310958289173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13594546886016207305526115 20391820329024310958289173)
          ·
            refine ⟨955866577923014576169805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20391820329024310958289173 955866577923014576169805)
            ·
              refine ⟨358449966721130466063677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 955866577923014576169805 358449966721130466063677)
              ·
                refine ⟨134418737520423924773879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358449966721130466063677 134418737520423924773879)
                ·
                  rfl

theorem cell19_441753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_441753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441753 prefixEnd_441753 := by exact prefixLift 441753
  have htrace : WordTrace (prefixWord ++ tailWord_441753) baseStart_441753 baseEnd_441753 := by
    simpa [prefixWord, tailWord_441753, baseEnd_441753] using wordTrace_append hprefix tailTrace_441753
  have hstable : (prefixWord ++ tailWord_441753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441753).length < 2 ^ (prefixWord ++ tailWord_441753).sum := by decide
  have hdescent : baseEnd_441753 < baseStart_441753 := by decide
  rcases family_descends (prefixWord ++ tailWord_441753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441829 : List Nat := [1, 3, 1, 5, 1, 3, 5]
def baseStart_441829 : Nat := 118140960795 + 441829 * 2 ^ 59
def prefixEnd_441829 : Nat := 4983230072969 + 3 ^ 40 * 441829 * 2
def baseEnd_441829 : Nat := 44813954389226089028261

theorem tailTrace_441829 : CollatzResearch.WordTrace tailWord_441829 prefixEnd_441829 44813954389226089028261 := by
  unfold tailWord_441829
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114827516336466230760541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10743218344224310820507027 16114827516336466230760541)
  ·
    refine ⟨6043060318626174836535203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16114827516336466230760541 6043060318626174836535203)
    ·
      refine ⟨9064590477939262254802805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043060318626174836535203 9064590477939262254802805)
      ·
        refine ⟨849805357306805836387763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9064590477939262254802805 849805357306805836387763)
        ·
          refine ⟨1274708035960208754581645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849805357306805836387763 1274708035960208754581645)
          ·
            refine ⟨478015513485078282968117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1274708035960208754581645 478015513485078282968117)
            ·
              refine ⟨44813954389226089028261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 478015513485078282968117 44813954389226089028261)
              ·
                rfl

theorem cell19_441829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_441829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441829 prefixEnd_441829 := by exact prefixLift 441829
  have htrace : WordTrace (prefixWord ++ tailWord_441829) baseStart_441829 baseEnd_441829 := by
    simpa [prefixWord, tailWord_441829, baseEnd_441829] using wordTrace_append hprefix tailTrace_441829
  have hstable : (prefixWord ++ tailWord_441829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441829).length < 2 ^ (prefixWord ++ tailWord_441829).sum := by decide
  have hdescent : baseEnd_441829 < baseStart_441829 := by decide
  rcases family_descends (prefixWord ++ tailWord_441829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441831 : List Nat := [1, 1, 5, 2, 1, 2, 7]
def baseStart_441831 : Nat := 118140960795 + 441831 * 2 ^ 59
def prefixEnd_441831 : Nat := 4983230072969 + 3 ^ 40 * 441831 * 2
def baseEnd_441831 : Nat := 44814157245780951680111

theorem tailTrace_441831 : CollatzResearch.WordTrace tailWord_441831 prefixEnd_441831 44814157245780951680111 := by
  unfold tailWord_441831
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114900462329220572333347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10743266974886147048222231 16114900462329220572333347)
  ·
    refine ⟨24172350693493830858500021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16114900462329220572333347 24172350693493830858500021)
    ·
      refine ⟨2266157877515046642984377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24172350693493830858500021 2266157877515046642984377)
      ·
        refine ⟨1699618408136284982238283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2266157877515046642984377 1699618408136284982238283)
        ·
          refine ⟨2549427612204427473357425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699618408136284982238283 2549427612204427473357425)
          ·
            refine ⟨1912070709153320605018069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2549427612204427473357425 1912070709153320605018069)
            ·
              refine ⟨44814157245780951680111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1912070709153320605018069 44814157245780951680111)
              ·
                rfl

theorem cell19_441831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_441831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441831 prefixEnd_441831 := by exact prefixLift 441831
  have htrace : WordTrace (prefixWord ++ tailWord_441831) baseStart_441831 baseEnd_441831 := by
    simpa [prefixWord, tailWord_441831, baseEnd_441831] using wordTrace_append hprefix tailTrace_441831
  have hstable : (prefixWord ++ tailWord_441831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441831).length < 2 ^ (prefixWord ++ tailWord_441831).sum := by decide
  have hdescent : baseEnd_441831 < baseStart_441831 := by decide
  rcases family_descends (prefixWord ++ tailWord_441831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441850 : List Nat := [3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_441850 : Nat := 118140960795 + 441850 * 2 ^ 59
def prefixEnd_441850 : Nat := 4983230072969 + 3 ^ 40 * 441850 * 2
def baseEnd_441850 : Nat := 134448253149156440618059

theorem tailTrace_441850 : CollatzResearch.WordTrace tailWord_441850 prefixEnd_441850 134448253149156440618059 := by
  unfold tailWord_441850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4028898362315096704318751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10743728966173591211516669 4028898362315096704318751)
  ·
    refine ⟨6043347543472645056478127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4028898362315096704318751 6043347543472645056478127)
    ·
      refine ⟨9065021315208967584717191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043347543472645056478127 9065021315208967584717191)
      ·
        refine ⟨13597531972813451377075787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065021315208967584717191 13597531972813451377075787)
        ·
          refine ⟨20396297959220177065613681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13597531972813451377075787 20396297959220177065613681)
          ·
            refine ⟨15297223469415132799210261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20396297959220177065613681 15297223469415132799210261)
            ·
              refine ⟨717057350128834349962981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15297223469415132799210261 717057350128834349962981)
              ·
                refine ⟨134448253149156440618059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717057350128834349962981 134448253149156440618059)
                ·
                  rfl

theorem cell19_441850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_441850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441850 prefixEnd_441850 := by exact prefixLift 441850
  have htrace : WordTrace (prefixWord ++ tailWord_441850) baseStart_441850 baseEnd_441850 := by
    simpa [prefixWord, tailWord_441850, baseEnd_441850] using wordTrace_append hprefix tailTrace_441850
  have hstable : (prefixWord ++ tailWord_441850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441850).length < 2 ^ (prefixWord ++ tailWord_441850).sum := by decide
  have hdescent : baseEnd_441850 < baseStart_441850 := by decide
  rcases family_descends (prefixWord ++ tailWord_441850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441888 : List Nat := [2, 1, 1, 6, 1, 8]
def baseStart_441888 : Nat := 118140960795 + 441888 * 2 ^ 59
def prefixEnd_441888 : Nat := 4983230072969 + 3 ^ 40 * 441888 * 2
def baseEnd_441888 : Nat := 14939979552531512419279

theorem tailTrace_441888 : CollatzResearch.WordTrace tailWord_441888 prefixEnd_441888 14939979552531512419279 := by
  unfold tailWord_441888
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058489711561359653579159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10744652948748479538105545 8058489711561359653579159)
  ·
    refine ⟨12087734567342039480368739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8058489711561359653579159 12087734567342039480368739)
    ·
      refine ⟨18131601851013059220553109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12087734567342039480368739 18131601851013059220553109)
      ·
        refine ⟨849918836766237150963427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18131601851013059220553109 849918836766237150963427)
        ·
          refine ⟨1274878255149355726445141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849918836766237150963427 1274878255149355726445141)
          ·
            refine ⟨14939979552531512419279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1274878255149355726445141 14939979552531512419279)
            ·
              rfl

theorem cell19_441888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 8].length) (baseStart_441888 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441888 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441888 prefixEnd_441888 := by exact prefixLift 441888
  have htrace : WordTrace (prefixWord ++ tailWord_441888) baseStart_441888 baseEnd_441888 := by
    simpa [prefixWord, tailWord_441888, baseEnd_441888] using wordTrace_append hprefix tailTrace_441888
  have hstable : (prefixWord ++ tailWord_441888).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441888).length < 2 ^ (prefixWord ++ tailWord_441888).sum := by decide
  have hdescent : baseEnd_441888 < baseStart_441888 := by decide
  rcases family_descends (prefixWord ++ tailWord_441888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441907 : List Nat := [1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_441907 : Nat := 118140960795 + 441907 * 2 ^ 59
def prefixEnd_441907 : Nat := 4983230072969 + 3 ^ 40 * 441907 * 2
def baseEnd_441907 : Nat := 134465597384597197351237

theorem tailTrace_441907 : CollatzResearch.WordTrace tailWord_441907 prefixEnd_441907 134465597384597197351237 := by
  unfold tailWord_441907
  simp only [CollatzResearch.WordTrace]
  refine ⟨16117672410053885552099975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10745114940035923701399983 16117672410053885552099975)
  ·
    refine ⟨24176508615080828328149963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16117672410053885552099975 24176508615080828328149963)
    ·
      refine ⟨36264762922621242492224945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24176508615080828328149963 36264762922621242492224945)
      ·
        refine ⟨27198572191965931869168709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36264762922621242492224945 27198572191965931869168709)
        ·
          refine ⟨5099732285993612225469133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27198572191965931869168709 5099732285993612225469133)
          ·
            refine ⟨1912399607247604584550925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5099732285993612225469133 1912399607247604584550925)
            ·
              refine ⟨717149852717851719206597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1912399607247604584550925 717149852717851719206597)
              ·
                refine ⟨134465597384597197351237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717149852717851719206597 134465597384597197351237)
                ·
                  rfl

theorem cell19_441907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_441907 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441907 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441907 prefixEnd_441907 := by exact prefixLift 441907
  have htrace : WordTrace (prefixWord ++ tailWord_441907) baseStart_441907 baseEnd_441907 := by
    simpa [prefixWord, tailWord_441907, baseEnd_441907] using wordTrace_append hprefix tailTrace_441907
  have hstable : (prefixWord ++ tailWord_441907).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441907).length < 2 ^ (prefixWord ++ tailWord_441907).sum := by decide
  have hdescent : baseEnd_441907 < baseStart_441907 := by decide
  rcases family_descends (prefixWord ++ tailWord_441907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441981 : List Nat := [1, 4, 1, 1, 4, 1, 4, 3]
def baseStart_441981 : Nat := 118140960795 + 441981 * 2 ^ 59
def prefixEnd_441981 : Nat := 4983230072969 + 3 ^ 40 * 441981 * 2
def baseEnd_441981 : Nat := 134488114462186951706591

theorem tailTrace_441981 : CollatzResearch.WordTrace tailWord_441981 prefixEnd_441981 134488114462186951706591 := by
  unfold tailWord_441981
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120371411785796190293797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10746914274523864126862531 16120371411785796190293797)
  ·
    refine ⟨3022569639709836785680087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16120371411785796190293797 3022569639709836785680087)
    ·
      refine ⟨4533854459564755178520131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022569639709836785680087 4533854459564755178520131)
      ·
        refine ⟨6800781689347132767780197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533854459564755178520131 6800781689347132767780197)
        ·
          refine ⟨1275146566752587393958787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6800781689347132767780197 1275146566752587393958787)
          ·
            refine ⟨1912719850128881090938181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275146566752587393958787 1912719850128881090938181)
            ·
              refine ⟨358634971899165204550909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1912719850128881090938181 358634971899165204550909)
              ·
                refine ⟨134488114462186951706591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358634971899165204550909 134488114462186951706591)
                ·
                  rfl

theorem cell19_441981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_441981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441981 prefixEnd_441981 := by exact prefixLift 441981
  have htrace : WordTrace (prefixWord ++ tailWord_441981) baseStart_441981 baseEnd_441981 := by
    simpa [prefixWord, tailWord_441981, baseEnd_441981] using wordTrace_append hprefix tailTrace_441981
  have hstable : (prefixWord ++ tailWord_441981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441981).length < 2 ^ (prefixWord ++ tailWord_441981).sum := by decide
  have hdescent : baseEnd_441981 < baseStart_441981 := by decide
  rcases family_descends (prefixWord ++ tailWord_441981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442070 : List Nat := [5, 2, 1, 3, 2, 1, 1, 4]
def baseStart_442070 : Nat := 118140960795 + 442070 * 2 ^ 59
def prefixEnd_442070 : Nat := 4983230072969 + 3 ^ 40 * 442070 * 2
def baseEnd_442070 : Nat := 134515195812261115728571

theorem tailTrace_442070 : CollatzResearch.WordTrace tailWord_442070 prefixEnd_442070 134515195812261115728571 := by
  unfold tailWord_442070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007726094278960274392729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10749078338975576260189109 1007726094278960274392729)
  ·
    refine ⟨755794570709220205794547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1007726094278960274392729 755794570709220205794547)
    ·
      refine ⟨1133691856063830308691821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755794570709220205794547 1133691856063830308691821)
      ·
        refine ⟨425134446023936365759433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1133691856063830308691821 425134446023936365759433)
        ·
          refine ⟨318850834517952274319575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425134446023936365759433 318850834517952274319575)
          ·
            refine ⟨478276251776928411479363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318850834517952274319575 478276251776928411479363)
            ·
              refine ⟨717414377665392617219045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478276251776928411479363 717414377665392617219045)
              ·
                refine ⟨134515195812261115728571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717414377665392617219045 134515195812261115728571)
                ·
                  rfl

theorem cell19_442070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_442070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442070 prefixEnd_442070 := by exact prefixLift 442070
  have htrace : WordTrace (prefixWord ++ tailWord_442070) baseStart_442070 baseEnd_442070 := by
    simpa [prefixWord, tailWord_442070, baseEnd_442070] using wordTrace_append hprefix tailTrace_442070
  have hstable : (prefixWord ++ tailWord_442070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442070).length < 2 ^ (prefixWord ++ tailWord_442070).sum := by decide
  have hdescent : baseEnd_442070 < baseStart_442070 := by decide
  rcases family_descends (prefixWord ++ tailWord_442070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442099 : List Nat := [1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_442099 : Nat := 118140960795 + 442099 * 2 ^ 59
def prefixEnd_442099 : Nat := 4983230072969 + 3 ^ 40 * 442099 * 2
def baseEnd_442099 : Nat := 134524020072397641084047

theorem tailTrace_442099 : CollatzResearch.WordTrace tailWord_442099 prefixEnd_442099 134524020072397641084047 := by
  unfold tailWord_442099
  simp only [CollatzResearch.WordTrace]
  refine ⟨16124675225358302343089351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10749783483572201562059567 16124675225358302343089351)
  ·
    refine ⟨24187012838037453514634027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16124675225358302343089351 24187012838037453514634027)
    ·
      refine ⟨36280519257056180271951041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24187012838037453514634027 36280519257056180271951041)
      ·
        refine ⟨27210389442792135203963281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36280519257056180271951041 27210389442792135203963281)
        ·
          refine ⟨20407792082094101402972461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27210389442792135203963281 20407792082094101402972461)
          ·
            refine ⟨7652922030785288026114673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20407792082094101402972461 7652922030785288026114673)
            ·
              refine ⟨5739691523088966019586005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7652922030785288026114673 5739691523088966019586005)
              ·
                refine ⟨134524020072397641084047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5739691523088966019586005 134524020072397641084047)
                ·
                  rfl

theorem cell19_442099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_442099 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442099 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442099 prefixEnd_442099 := by exact prefixLift 442099
  have htrace : WordTrace (prefixWord ++ tailWord_442099) baseStart_442099 baseEnd_442099 := by
    simpa [prefixWord, tailWord_442099, baseEnd_442099] using wordTrace_append hprefix tailTrace_442099
  have hstable : (prefixWord ++ tailWord_442099).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442099).length < 2 ^ (prefixWord ++ tailWord_442099).sum := by decide
  have hdescent : baseEnd_442099 < baseStart_442099 := by decide
  rcases family_descends (prefixWord ++ tailWord_442099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442116 : List Nat := [2, 3, 2, 2, 1, 3, 6]
def baseStart_442116 : Nat := 118140960795 + 442116 * 2 ^ 59
def prefixEnd_442116 : Nat := 4983230072969 + 3 ^ 40 * 442116 * 2
def baseEnd_442116 : Nat := 44843064304848879568741

theorem tailTrace_442116 : CollatzResearch.WordTrace tailWord_442116 prefixEnd_442116 44843064304848879568741 := by
  unfold tailWord_442116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062647633148357123229101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10750196844197809497638801 8062647633148357123229101)
  ·
    refine ⟨3023492862430633921210913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8062647633148357123229101 3023492862430633921210913)
    ·
      refine ⟨2267619646822975440908185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3023492862430633921210913 2267619646822975440908185)
      ·
        refine ⟨1700714735117231580681139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2267619646822975440908185 1700714735117231580681139)
        ·
          refine ⟨2551072102675847371021709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700714735117231580681139 2551072102675847371021709)
          ·
            refine ⟨956652038503442764133141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2551072102675847371021709 956652038503442764133141)
            ·
              refine ⟨44843064304848879568741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 956652038503442764133141 44843064304848879568741)
              ·
                rfl

theorem cell19_442116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_442116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442116 prefixEnd_442116 := by exact prefixLift 442116
  have htrace : WordTrace (prefixWord ++ tailWord_442116) baseStart_442116 baseEnd_442116 := by
    simpa [prefixWord, tailWord_442116, baseEnd_442116] using wordTrace_append hprefix tailTrace_442116
  have hstable : (prefixWord ++ tailWord_442116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442116).length < 2 ^ (prefixWord ++ tailWord_442116).sum := by decide
  have hdescent : baseEnd_442116 < baseStart_442116 := by decide
  rcases family_descends (prefixWord ++ tailWord_442116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442152 : List Nat := [2, 1, 5, 1, 1, 2, 4, 3]
def baseStart_442152 : Nat := 118140960795 + 442152 * 2 ^ 59
def prefixEnd_442152 : Nat := 4983230072969 + 3 ^ 40 * 442152 * 2
def baseEnd_442152 : Nat := 134540147168509221906125

theorem tailTrace_442152 : CollatzResearch.WordTrace tailWord_442152 prefixEnd_442152 134540147168509221906125 := by
  unfold tailWord_442152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8063304147083146197384355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10751072196110861596512473 8063304147083146197384355)
  ·
    refine ⟨12094956220624719296076533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8063304147083146197384355 12094956220624719296076533)
    ·
      refine ⟨1133902145683567434007175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12094956220624719296076533 1133902145683567434007175)
      ·
        refine ⟨1700853218525351151010763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133902145683567434007175 1700853218525351151010763)
        ·
          refine ⟨2551279827788026726516145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700853218525351151010763 2551279827788026726516145)
          ·
            refine ⟨1913459870841020044887109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551279827788026726516145 1913459870841020044887109)
            ·
              refine ⟨358773725782691258416333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1913459870841020044887109 358773725782691258416333)
              ·
                refine ⟨134540147168509221906125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358773725782691258416333 134540147168509221906125)
                ·
                  rfl

theorem cell19_442152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_442152 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442152 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442152 prefixEnd_442152 := by exact prefixLift 442152
  have htrace : WordTrace (prefixWord ++ tailWord_442152) baseStart_442152 baseEnd_442152 := by
    simpa [prefixWord, tailWord_442152, baseEnd_442152] using wordTrace_append hprefix tailTrace_442152
  have hstable : (prefixWord ++ tailWord_442152).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442152).length < 2 ^ (prefixWord ++ tailWord_442152).sum := by decide
  have hdescent : baseEnd_442152 < baseStart_442152 := by decide
  rcases family_descends (prefixWord ++ tailWord_442152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442169 : List Nat := [1, 2, 1, 7, 2, 1, 5]
def baseStart_442169 : Nat := 118140960795 + 442169 * 2 ^ 59
def prefixEnd_442169 : Nat := 4983230072969 + 3 ^ 40 * 442169 * 2
def baseEnd_442169 : Nat := 44848440003552739842767

theorem tailTrace_442169 : CollatzResearch.WordTrace tailWord_442169 prefixEnd_442169 44848440003552739842767 := by
  unfold tailWord_442169
  simp only [CollatzResearch.WordTrace]
  refine ⟨16127228335104704298137561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10751485556736469532091707 16127228335104704298137561)
  ·
    refine ⟨12095421251328528223603171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16127228335104704298137561 12095421251328528223603171)
    ·
      refine ⟨18143131876992792335404757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12095421251328528223603171 18143131876992792335404757)
      ·
        refine ⟨425229653367018570361049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18143131876992792335404757 425229653367018570361049)
        ·
          refine ⟨318922240025263927770787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425229653367018570361049 318922240025263927770787)
          ·
            refine ⟨478383360037895891656181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318922240025263927770787 478383360037895891656181)
            ·
              refine ⟨44848440003552739842767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 478383360037895891656181 44848440003552739842767)
              ·
                rfl

theorem cell19_442169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_442169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442169 prefixEnd_442169 := by exact prefixLift 442169
  have htrace : WordTrace (prefixWord ++ tailWord_442169) baseStart_442169 baseEnd_442169 := by
    simpa [prefixWord, tailWord_442169, baseEnd_442169] using wordTrace_append hprefix tailTrace_442169
  have hstable : (prefixWord ++ tailWord_442169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442169).length < 2 ^ (prefixWord ++ tailWord_442169).sum := by decide
  have hdescent : baseEnd_442169 < baseStart_442169 := by decide
  rcases family_descends (prefixWord ++ tailWord_442169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442173 : List Nat := [1, 4, 1, 4, 1, 1, 7]
def baseStart_442173 : Nat := 118140960795 + 442173 * 2 ^ 59
def prefixEnd_442173 : Nat := 4983230072969 + 3 ^ 40 * 442173 * 2
def baseEnd_442173 : Nat := 44848845716662465146467

theorem tailTrace_442173 : CollatzResearch.WordTrace tailWord_442173 prefixEnd_442173 44848845716662465146467 := by
  unfold tailWord_442173
  simp only [CollatzResearch.WordTrace]
  refine ⟨16127374227090212981283173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10751582818060141987522115 16127374227090212981283173)
  ·
    refine ⟨3023882667579414933990595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16127374227090212981283173 3023882667579414933990595)
    ·
      refine ⟨4535824001369122400985893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023882667579414933990595 4535824001369122400985893)
      ·
        refine ⟨850467000256710450184855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4535824001369122400985893 850467000256710450184855)
        ·
          refine ⟨1275700500385065675277283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850467000256710450184855 1275700500385065675277283)
          ·
            refine ⟨1913550750577598512915925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275700500385065675277283 1913550750577598512915925)
            ·
              refine ⟨44848845716662465146467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1913550750577598512915925 44848845716662465146467)
              ·
                rfl

theorem cell19_442173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_442173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442173 prefixEnd_442173 := by exact prefixLift 442173
  have htrace : WordTrace (prefixWord ++ tailWord_442173) baseStart_442173 baseEnd_442173 := by
    simpa [prefixWord, tailWord_442173, baseEnd_442173] using wordTrace_append hprefix tailTrace_442173
  have hstable : (prefixWord ++ tailWord_442173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442173).length < 2 ^ (prefixWord ++ tailWord_442173).sum := by decide
  have hdescent : baseEnd_442173 < baseStart_442173 := by decide
  rcases family_descends (prefixWord ++ tailWord_442173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442230 : List Nat := [5, 1, 1, 3, 9]
def baseStart_442230 : Nat := 118140960795 + 442230 * 2 ^ 59
def prefixEnd_442230 : Nat := 4983230072969 + 3 ^ 40 * 442230 * 2
def baseEnd_442230 : Nat := 4983847458719561191577

theorem tailTrace_442230 : CollatzResearch.WordTrace tailWord_442230 prefixEnd_442230 4983847458719561191577 := by
  unfold tailWord_442230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008090824242731982256759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10752968791922474477405429 1008090824242731982256759)
  ·
    refine ⟨1512136236364097973385139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1008090824242731982256759 1512136236364097973385139)
    ·
      refine ⟨2268204354546146960077709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512136236364097973385139 2268204354546146960077709)
      ·
        refine ⟨850576632954805110029141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2268204354546146960077709 850576632954805110029141)
        ·
          refine ⟨4983847458719561191577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 850576632954805110029141 4983847458719561191577)
          ·
            rfl

theorem cell19_442230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 9].length) (baseStart_442230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442230 prefixEnd_442230 := by exact prefixLift 442230
  have htrace : WordTrace (prefixWord ++ tailWord_442230) baseStart_442230 baseEnd_442230 := by
    simpa [prefixWord, tailWord_442230, baseEnd_442230] using wordTrace_append hprefix tailTrace_442230
  have hstable : (prefixWord ++ tailWord_442230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442230).length < 2 ^ (prefixWord ++ tailWord_442230).sum := by decide
  have hdescent : baseEnd_442230 < baseStart_442230 := by decide
  rcases family_descends (prefixWord ++ tailWord_442230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442247 : List Nat := [1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_442247 : Nat := 118140960795 + 442247 * 2 ^ 59
def prefixEnd_442247 : Nat := 4983230072969 + 3 ^ 40 * 442247 * 2
def baseEnd_442247 : Nat := 134569054227577149794755

theorem tailTrace_442247 : CollatzResearch.WordTrace tailWord_442247 prefixEnd_442247 134569054227577149794755 := by
  unfold tailWord_442247
  simp only [CollatzResearch.WordTrace]
  refine ⟨16130073228822123619476995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10753382152548082412984663 16130073228822123619476995)
  ·
    refine ⟨24195109843233185429215493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16130073228822123619476995 24195109843233185429215493)
    ·
      refine ⟨4536583095606222267977905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24195109843233185429215493 4536583095606222267977905)
      ·
        refine ⟨3402437321704666700983429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4536583095606222267977905 3402437321704666700983429)
        ·
          refine ⟨637956997819625006434393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3402437321704666700983429 637956997819625006434393)
          ·
            refine ⟨478467748364718754825795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637956997819625006434393 478467748364718754825795)
            ·
              refine ⟨717701622547078132238693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478467748364718754825795 717701622547078132238693)
              ·
                refine ⟨134569054227577149794755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717701622547078132238693 134569054227577149794755)
                ·
                  rfl

theorem cell19_442247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_442247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442247 prefixEnd_442247 := by exact prefixLift 442247
  have htrace : WordTrace (prefixWord ++ tailWord_442247) baseStart_442247 baseEnd_442247 := by
    simpa [prefixWord, tailWord_442247, baseEnd_442247] using wordTrace_append hprefix tailTrace_442247
  have hstable : (prefixWord ++ tailWord_442247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442247).length < 2 ^ (prefixWord ++ tailWord_442247).sum := by decide
  have hdescent : baseEnd_442247 < baseStart_442247 := by decide
  rcases family_descends (prefixWord ++ tailWord_442247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442264 : List Nat := [2, 1, 2, 6, 1, 1, 3, 3]
def baseStart_442264 : Nat := 118140960795 + 442264 * 2 ^ 59
def prefixEnd_442264 : Nat := 4983230072969 + 3 ^ 40 * 442264 * 2
def baseEnd_442264 : Nat := 134574227069726147416931

theorem tailTrace_442264 : CollatzResearch.WordTrace tailWord_442264 prefixEnd_442264 134574227069726147416931 := by
  unfold tailWord_442264
  simp only [CollatzResearch.WordTrace]
  refine ⟨8065346634880267761422923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10753795513173690348563897 8065346634880267761422923)
  ·
    refine ⟨12098019952320401642134385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8065346634880267761422923 12098019952320401642134385)
    ·
      refine ⟨9073514964240301231600789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12098019952320401642134385 9073514964240301231600789)
      ·
        refine ⟨425321013948764120231287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9073514964240301231600789 425321013948764120231287)
        ·
          refine ⟨637981520923146180346931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425321013948764120231287 637981520923146180346931)
          ·
            refine ⟨956972281384719270520397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637981520923146180346931 956972281384719270520397)
            ·
              refine ⟨358864605519269726445149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 956972281384719270520397 358864605519269726445149)
              ·
                refine ⟨134574227069726147416931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358864605519269726445149 134574227069726147416931)
                ·
                  rfl

theorem cell19_442264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_442264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442264 prefixEnd_442264 := by exact prefixLift 442264
  have htrace : WordTrace (prefixWord ++ tailWord_442264) baseStart_442264 baseEnd_442264 := by
    simpa [prefixWord, tailWord_442264, baseEnd_442264] using wordTrace_append hprefix tailTrace_442264
  have hstable : (prefixWord ++ tailWord_442264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442264).length < 2 ^ (prefixWord ++ tailWord_442264).sum := by decide
  have hdescent : baseEnd_442264 < baseStart_442264 := by decide
  rcases family_descends (prefixWord ++ tailWord_442264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442266 : List Nat := [3, 1, 1, 4, 2, 2, 3, 3]
def baseStart_442266 : Nat := 118140960795 + 442266 * 2 ^ 59
def prefixEnd_442266 : Nat := 4983230072969 + 3 ^ 40 * 442266 * 2
def baseEnd_442266 : Nat := 134574835639390735372481

theorem tailTrace_442266 : CollatzResearch.WordTrace tailWord_442266 prefixEnd_442266 134574835639390735372481 := by
  unfold tailWord_442266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032691553938322466104663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10753844143835526576279101 4032691553938322466104663)
  ·
    refine ⟨6049037330907483699156995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4032691553938322466104663 6049037330907483699156995)
    ·
      refine ⟨9073555996361225548735493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6049037330907483699156995 9073555996361225548735493)
      ·
        refine ⟨1701291749317729790387905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9073555996361225548735493 1701291749317729790387905)
        ·
          refine ⟨1275968811988297342790929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701291749317729790387905 1275968811988297342790929)
          ·
            refine ⟨956976608991223007093197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275968811988297342790929 956976608991223007093197)
            ·
              refine ⟨358866228371708627659949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 956976608991223007093197 358866228371708627659949)
              ·
                refine ⟨134574835639390735372481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358866228371708627659949 134574835639390735372481)
                ·
                  rfl

theorem cell19_442266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_442266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442266 prefixEnd_442266 := by exact prefixLift 442266
  have htrace : WordTrace (prefixWord ++ tailWord_442266) baseStart_442266 baseEnd_442266 := by
    simpa [prefixWord, tailWord_442266, baseEnd_442266] using wordTrace_append hprefix tailTrace_442266
  have hstable : (prefixWord ++ tailWord_442266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442266).length < 2 ^ (prefixWord ++ tailWord_442266).sum := by decide
  have hdescent : baseEnd_442266 < baseStart_442266 := by decide
  rcases family_descends (prefixWord ++ tailWord_442266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442325 : List Nat := [1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_442325 : Nat := 118140960795 + 442325 * 2 ^ 59
def prefixEnd_442325 : Nat := 4983230072969 + 3 ^ 40 * 442325 * 2
def baseEnd_442325 : Nat := 134592788444496080061209

theorem tailTrace_442325 : CollatzResearch.WordTrace tailWord_442325 prefixEnd_442325 134592788444496080061209 := by
  unfold tailWord_442325
  simp only [CollatzResearch.WordTrace]
  refine ⟨16132918122539542940816429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10755278748359695293877619 16132918122539542940816429)
  ·
    refine ⟨6049844295952328602806161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16132918122539542940816429 6049844295952328602806161)
    ·
      refine ⟨4537383221964246452104621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6049844295952328602806161 4537383221964246452104621)
      ·
        refine ⟨1701518708236592419539233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4537383221964246452104621 1701518708236592419539233)
        ·
          refine ⟨1276139031177444314654425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701518708236592419539233 1276139031177444314654425)
          ·
            refine ⟨957104273383083235990819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276139031177444314654425 957104273383083235990819)
            ·
              refine ⟨1435656410074624853986229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957104273383083235990819 1435656410074624853986229)
              ·
                refine ⟨134592788444496080061209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1435656410074624853986229 134592788444496080061209)
                ·
                  rfl

theorem cell19_442325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_442325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442325 prefixEnd_442325 := by exact prefixLift 442325
  have htrace : WordTrace (prefixWord ++ tailWord_442325) baseStart_442325 baseEnd_442325 := by
    simpa [prefixWord, tailWord_442325, baseEnd_442325] using wordTrace_append hprefix tailTrace_442325
  have hstable : (prefixWord ++ tailWord_442325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442325).length < 2 ^ (prefixWord ++ tailWord_442325).sum := by decide
  have hdescent : baseEnd_442325 < baseStart_442325 := by decide
  rcases family_descends (prefixWord ++ tailWord_442325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442327 : List Nat := [1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_442327 : Nat := 118140960795 + 442327 * 2 ^ 59
def prefixEnd_442327 : Nat := 4983230072969 + 3 ^ 40 * 442327 * 2
def baseEnd_442327 : Nat := 134593397014160668016759

theorem tailTrace_442327 : CollatzResearch.WordTrace tailWord_442327 prefixEnd_442327 134593397014160668016759 := by
  unfold tailWord_442327
  simp only [CollatzResearch.WordTrace]
  refine ⟨16132991068532297282389235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10755327379021531521592823 16132991068532297282389235)
  ·
    refine ⟨24199486602798445923583853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16132991068532297282389235 24199486602798445923583853)
    ·
      refine ⟨9074807476049417221343945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24199486602798445923583853 9074807476049417221343945)
      ·
        refine ⟨6806105607037062916007959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9074807476049417221343945 6806105607037062916007959)
        ·
          refine ⟨10209158410555594374011939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806105607037062916007959 10209158410555594374011939)
          ·
            refine ⟨15313737615833391561017909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10209158410555594374011939 15313737615833391561017909)
            ·
              refine ⟨1435662901484380458845429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15313737615833391561017909 1435662901484380458845429)
              ·
                refine ⟨134593397014160668016759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1435662901484380458845429 134593397014160668016759)
                ·
                  rfl

theorem cell19_442327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_442327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442327 prefixEnd_442327 := by exact prefixLift 442327
  have htrace : WordTrace (prefixWord ++ tailWord_442327) baseStart_442327 baseEnd_442327 := by
    simpa [prefixWord, tailWord_442327, baseEnd_442327] using wordTrace_append hprefix tailTrace_442327
  have hstable : (prefixWord ++ tailWord_442327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442327).length < 2 ^ (prefixWord ++ tailWord_442327).sum := by decide
  have hdescent : baseEnd_442327 < baseStart_442327 := by decide
  rcases family_descends (prefixWord ++ tailWord_442327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442365 : List Nat := [1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_442365 : Nat := 118140960795 + 442365 * 2 ^ 59
def prefixEnd_442365 : Nat := 4983230072969 + 3 ^ 40 * 442365 * 2
def baseEnd_442365 : Nat := 134604959837787839172211

theorem tailTrace_442365 : CollatzResearch.WordTrace tailWord_442365 prefixEnd_442365 134604959837787839172211 := by
  unfold tailWord_442365
  simp only [CollatzResearch.WordTrace]
  refine ⟨16134377042394629772272549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10756251361596419848181699 16134377042394629772272549)
  ·
    refine ⟨3025195695448993082301103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16134377042394629772272549 3025195695448993082301103)
    ·
      refine ⟨4537793543173489623451655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3025195695448993082301103 4537793543173489623451655)
      ·
        refine ⟨6806690314760234435177483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537793543173489623451655 6806690314760234435177483)
        ·
          refine ⟨10210035472140351652766225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806690314760234435177483 10210035472140351652766225)
          ·
            refine ⟨7657526604105263739574669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10210035472140351652766225 7657526604105263739574669)
            ·
              refine ⟨2871572476539473902340501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7657526604105263739574669 2871572476539473902340501)
              ·
                refine ⟨134604959837787839172211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2871572476539473902340501 134604959837787839172211)
                ·
                  rfl

theorem cell19_442365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_442365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442365 prefixEnd_442365 := by exact prefixLift 442365
  have htrace : WordTrace (prefixWord ++ tailWord_442365) baseStart_442365 baseEnd_442365 := by
    simpa [prefixWord, tailWord_442365, baseEnd_442365] using wordTrace_append hprefix tailTrace_442365
  have hstable : (prefixWord ++ tailWord_442365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442365).length < 2 ^ (prefixWord ++ tailWord_442365).sum := by decide
  have hdescent : baseEnd_442365 < baseStart_442365 := by decide
  rcases family_descends (prefixWord ++ tailWord_442365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442401 : List Nat := [1, 2, 3, 2, 5, 6]
def baseStart_442401 : Nat := 118140960795 + 442401 * 2 ^ 59
def prefixEnd_442401 : Nat := 4983230072969 + 3 ^ 40 * 442401 * 2
def baseEnd_442401 : Nat := 14957323787972269152457

theorem tailTrace_442401 : CollatzResearch.WordTrace tailWord_442401 prefixEnd_442401 14957323787972269152457 := by
  unfold tailWord_442401
  simp only [CollatzResearch.WordTrace]
  refine ⟨16135690070264207920583057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10757126713509471947055371 16135690070264207920583057)
  ·
    refine ⟨12101767552698155940437293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16135690070264207920583057 12101767552698155940437293)
    ·
      refine ⟨4538162832261808477663985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12101767552698155940437293 4538162832261808477663985)
      ·
        refine ⟨3403622124196356358247989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4538162832261808477663985 3403622124196356358247989)
        ·
          refine ⟨319089574143408408585749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3403622124196356358247989 319089574143408408585749)
          ·
            refine ⟨14957323787972269152457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 319089574143408408585749 14957323787972269152457)
            ·
              rfl

theorem cell19_442401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 6].length) (baseStart_442401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442401 prefixEnd_442401 := by exact prefixLift 442401
  have htrace : WordTrace (prefixWord ++ tailWord_442401) baseStart_442401 baseEnd_442401 := by
    simpa [prefixWord, tailWord_442401, baseEnd_442401] using wordTrace_append hprefix tailTrace_442401
  have hstable : (prefixWord ++ tailWord_442401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442401).length < 2 ^ (prefixWord ++ tailWord_442401).sum := by decide
  have hdescent : baseEnd_442401 < baseStart_442401 := by decide
  rcases family_descends (prefixWord ++ tailWord_442401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442439 : List Nat := [1, 1, 4, 1, 3, 1, 5, 3]
def baseStart_442439 : Nat := 118140960795 + 442439 * 2 ^ 59
def prefixEnd_442439 : Nat := 4983230072969 + 3 ^ 40 * 442439 * 2
def baseEnd_442439 : Nat := 134627476915377593527565

theorem tailTrace_442439 : CollatzResearch.WordTrace tailWord_442439 prefixEnd_442439 134627476915377593527565 := by
  unfold tailWord_442439
  simp only [CollatzResearch.WordTrace]
  refine ⟨16137076044126540410466371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10758050696084360273644247 16137076044126540410466371)
  ·
    refine ⟨24205614066189810615699557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16137076044126540410466371 24205614066189810615699557)
    ·
      refine ⟨4538552637410589490443667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24205614066189810615699557 4538552637410589490443667)
      ·
        refine ⟨6807828956115884235665501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4538552637410589490443667 6807828956115884235665501)
        ·
          refine ⟨2552935858543456588374563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6807828956115884235665501 2552935858543456588374563)
          ·
            refine ⟨3829403787815184882561845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552935858543456588374563 3829403787815184882561845)
            ·
              refine ⟨359006605107673582740173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3829403787815184882561845 359006605107673582740173)
              ·
                refine ⟨134627476915377593527565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359006605107673582740173 134627476915377593527565)
                ·
                  rfl

theorem cell19_442439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_442439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442439 prefixEnd_442439 := by exact prefixLift 442439
  have htrace : WordTrace (prefixWord ++ tailWord_442439) baseStart_442439 baseEnd_442439 := by
    simpa [prefixWord, tailWord_442439, baseEnd_442439] using wordTrace_append hprefix tailTrace_442439
  have hstable : (prefixWord ++ tailWord_442439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442439).length < 2 ^ (prefixWord ++ tailWord_442439).sum := by decide
  have hdescent : baseEnd_442439 < baseStart_442439 := by decide
  rcases family_descends (prefixWord ++ tailWord_442439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442572 : List Nat := [2, 2, 1, 6, 1, 7]
def baseStart_442572 : Nat := 118140960795 + 442572 * 2 ^ 59
def prefixEnd_442572 : Nat := 4983230072969 + 3 ^ 40 * 442572 * 2
def baseEnd_442572 : Nat := 14963105199785854730183

theorem tailTrace_442572 : CollatzResearch.WordTrace tailWord_442572 prefixEnd_442572 14963105199785854730183 := by
  unfold tailWord_442572
  simp only [CollatzResearch.WordTrace]
  refine ⟨8070963476322352062528985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10761284635096469416705313 8070963476322352062528985)
  ·
    refine ⟨6053222607241764046896739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8070963476322352062528985 6053222607241764046896739)
    ·
      refine ⟨9079833910862646070345109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053222607241764046896739 9079833910862646070345109)
      ·
        refine ⟨425617214571686534547427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9079833910862646070345109 425617214571686534547427)
        ·
          refine ⟨638425821857529801821141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425617214571686534547427 638425821857529801821141)
          ·
            refine ⟨14963105199785854730183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 638425821857529801821141 14963105199785854730183)
            ·
              rfl

theorem cell19_442572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 7].length) (baseStart_442572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442572 prefixEnd_442572 := by exact prefixLift 442572
  have htrace : WordTrace (prefixWord ++ tailWord_442572) baseStart_442572 baseEnd_442572 := by
    simpa [prefixWord, tailWord_442572, baseEnd_442572] using wordTrace_append hprefix tailTrace_442572
  have hstable : (prefixWord ++ tailWord_442572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442572).length < 2 ^ (prefixWord ++ tailWord_442572).sum := by decide
  have hdescent : baseEnd_442572 < baseStart_442572 := by decide
  rcases family_descends (prefixWord ++ tailWord_442572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442574 : List Nat := [4, 1, 1, 1, 4, 8]
def baseStart_442574 : Nat := 118140960795 + 442574 * 2 ^ 59
def prefixEnd_442574 : Nat := 4983230072969 + 3 ^ 40 * 442574 * 2
def baseEnd_442574 : Nat := 14963172818637475614133

theorem tailTrace_442574 : CollatzResearch.WordTrace tailWord_442574 prefixEnd_442574 14963172818637475614133 := by
  unfold tailWord_442574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017749987329682308328847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10761333265758305644420517 2017749987329682308328847)
  ·
    refine ⟨3026624980994523462493271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2017749987329682308328847 3026624980994523462493271)
    ·
      refine ⟨4539937471491785193739907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026624980994523462493271 4539937471491785193739907)
      ·
        refine ⟨6809906207237677790609861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4539937471491785193739907 6809906207237677790609861)
        ·
          refine ⟨1276857413857064585739349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6809906207237677790609861 1276857413857064585739349)
          ·
            refine ⟨14963172818637475614133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1276857413857064585739349 14963172818637475614133)
            ·
              rfl

theorem cell19_442574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 8].length) (baseStart_442574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442574 prefixEnd_442574 := by exact prefixLift 442574
  have htrace : WordTrace (prefixWord ++ tailWord_442574) baseStart_442574 baseEnd_442574 := by
    simpa [prefixWord, tailWord_442574, baseEnd_442574] using wordTrace_append hprefix tailTrace_442574
  have hstable : (prefixWord ++ tailWord_442574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442574).length < 2 ^ (prefixWord ++ tailWord_442574).sum := by decide
  have hdescent : baseEnd_442574 < baseStart_442574 := by decide
  rcases family_descends (prefixWord ++ tailWord_442574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442589 : List Nat := [1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_442589 : Nat := 118140960795 + 442589 * 2 ^ 59
def prefixEnd_442589 : Nat := 4983230072969 + 3 ^ 40 * 442589 * 2
def baseEnd_442589 : Nat := 134673119640221690193823

theorem tailTrace_442589 : CollatzResearch.WordTrace tailWord_442589 prefixEnd_442589 134673119640221690193823 := by
  unfold tailWord_442589
  simp only [CollatzResearch.WordTrace]
  refine ⟨16142546993583116028426821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10761697995722077352284547 16142546993583116028426821)
  ·
    refine ⟨3026727561296834255330029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16142546993583116028426821 3026727561296834255330029)
    ·
      refine ⟨1135022835486312845748761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3026727561296834255330029 1135022835486312845748761)
      ·
        refine ⟨851267126614734634311571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1135022835486312845748761 851267126614734634311571)
        ·
          refine ⟨1276900689922101951467357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851267126614734634311571 1276900689922101951467357)
          ·
            refine ⟨478837758720788231800259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1276900689922101951467357 478837758720788231800259)
            ·
              refine ⟨718256638081182347700389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478837758720788231800259 718256638081182347700389)
              ·
                refine ⟨134673119640221690193823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 718256638081182347700389 134673119640221690193823)
                ·
                  rfl

theorem cell19_442589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_442589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442589 prefixEnd_442589 := by exact prefixLift 442589
  have htrace : WordTrace (prefixWord ++ tailWord_442589) baseStart_442589 baseEnd_442589 := by
    simpa [prefixWord, tailWord_442589, baseEnd_442589] using wordTrace_append hprefix tailTrace_442589
  have hstable : (prefixWord ++ tailWord_442589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442589).length < 2 ^ (prefixWord ++ tailWord_442589).sum := by decide
  have hdescent : baseEnd_442589 < baseStart_442589 := by decide
  rcases family_descends (prefixWord ++ tailWord_442589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442663 : List Nat := [1, 1, 8, 1, 1, 1, 1, 5]
def baseStart_442663 : Nat := 118140960795 + 442663 * 2 ^ 59
def prefixEnd_442663 : Nat := 4983230072969 + 3 ^ 40 * 442663 * 2
def baseEnd_442663 : Nat := 134695636717811444549177

theorem tailTrace_442663 : CollatzResearch.WordTrace tailWord_442663 prefixEnd_442663 134695636717811444549177 := by
  unfold tailWord_442663
  simp only [CollatzResearch.WordTrace]
  refine ⟨16145245995315026666620643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10763497330210017777747095 16145245995315026666620643)
  ·
    refine ⟨24217868992972539999930965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16145245995315026666620643 24217868992972539999930965)
    ·
      refine ⟨283803152261396953124191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 24217868992972539999930965 283803152261396953124191)
      ·
        refine ⟨425704728392095429686287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283803152261396953124191 425704728392095429686287)
        ·
          refine ⟨638557092588143144529431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425704728392095429686287 638557092588143144529431)
          ·
            refine ⟨957835638882214716794147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638557092588143144529431 957835638882214716794147)
            ·
              refine ⟨1436753458323322075191221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957835638882214716794147 1436753458323322075191221)
              ·
                refine ⟨134695636717811444549177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1436753458323322075191221 134695636717811444549177)
                ·
                  rfl

theorem cell19_442663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 5].length) (baseStart_442663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442663 prefixEnd_442663 := by exact prefixLift 442663
  have htrace : WordTrace (prefixWord ++ tailWord_442663) baseStart_442663 baseEnd_442663 := by
    simpa [prefixWord, tailWord_442663, baseEnd_442663] using wordTrace_append hprefix tailTrace_442663
  have hstable : (prefixWord ++ tailWord_442663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442663).length < 2 ^ (prefixWord ++ tailWord_442663).sum := by decide
  have hdescent : baseEnd_442663 < baseStart_442663 := by decide
  rcases family_descends (prefixWord ++ tailWord_442663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442686 : List Nat := [4, 2, 1, 2, 1, 4, 5]
def baseStart_442686 : Nat := 118140960795 + 442686 * 2 ^ 59
def prefixEnd_442686 : Nat := 4983230072969 + 3 ^ 40 * 442686 * 2
def baseEnd_442686 : Nat := 44900878422984735346001

theorem tailTrace_442686 : CollatzResearch.WordTrace tailWord_442686 prefixEnd_442686 44900878422984735346001 := by
  unfold tailWord_442686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018260609278962699338489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10764056582821134396471941 2018260609278962699338489)
  ·
    refine ⟨1513695456959222024503867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2018260609278962699338489 1513695456959222024503867)
    ·
      refine ⟨2270543185438833036755801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1513695456959222024503867 2270543185438833036755801)
      ·
        refine ⟨1702907389079124777566851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2270543185438833036755801 1702907389079124777566851)
        ·
          refine ⟨2554361083618687166350277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702907389079124777566851 2554361083618687166350277)
          ·
            refine ⟨478942703178503843690677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2554361083618687166350277 478942703178503843690677)
            ·
              refine ⟨44900878422984735346001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 478942703178503843690677 44900878422984735346001)
              ·
                rfl

theorem cell19_442686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_442686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442686 prefixEnd_442686 := by exact prefixLift 442686
  have htrace : WordTrace (prefixWord ++ tailWord_442686) baseStart_442686 baseEnd_442686 := by
    simpa [prefixWord, tailWord_442686, baseEnd_442686] using wordTrace_append hprefix tailTrace_442686
  have hstable : (prefixWord ++ tailWord_442686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442686).length < 2 ^ (prefixWord ++ tailWord_442686).sum := by decide
  have hdescent : baseEnd_442686 < baseStart_442686 := by decide
  rcases family_descends (prefixWord ++ tailWord_442686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442747 : List Nat := [1, 1, 1, 1, 1, 14]
def baseStart_442747 : Nat := 118140960795 + 442747 * 2 ^ 59
def prefixEnd_442747 : Nat := 4983230072969 + 3 ^ 40 * 442747 * 2
def baseEnd_442747 : Nat := 14969021849302682075809

theorem tailTrace_442747 : CollatzResearch.WordTrace tailWord_442747 prefixEnd_442747 14969021849302682075809 := by
  unfold tailWord_442747
  simp only [CollatzResearch.WordTrace]
  refine ⟨16148309727010709012678495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10765539818007139341785663 16148309727010709012678495)
  ·
    refine ⟨24222464590516063519017743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16148309727010709012678495 24222464590516063519017743)
    ·
      refine ⟨36333696885774095278526615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24222464590516063519017743 36333696885774095278526615)
      ·
        refine ⟨54500545328661142917789923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36333696885774095278526615 54500545328661142917789923)
        ·
          refine ⟨81750817992991714376684885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54500545328661142917789923 81750817992991714376684885)
          ·
            refine ⟨14969021849302682075809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 81750817992991714376684885 14969021849302682075809)
            ·
              rfl

theorem cell19_442747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 14].length) (baseStart_442747 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442747 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442747 prefixEnd_442747 := by exact prefixLift 442747
  have htrace : WordTrace (prefixWord ++ tailWord_442747) baseStart_442747 baseEnd_442747 := by
    simpa [prefixWord, tailWord_442747, baseEnd_442747] using wordTrace_append hprefix tailTrace_442747
  have hstable : (prefixWord ++ tailWord_442747).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442747).length < 2 ^ (prefixWord ++ tailWord_442747).sum := by decide
  have hdescent : baseEnd_442747 < baseStart_442747 := by decide
  rcases family_descends (prefixWord ++ tailWord_442747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442764 : List Nat := [2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_442764 : Nat := 118140960795 + 442764 * 2 ^ 59
def prefixEnd_442764 : Nat := 4983230072969 + 3 ^ 40 * 442764 * 2
def baseEnd_442764 : Nat := 134726369485873136304457

theorem tailTrace_442764 : CollatzResearch.WordTrace tailWord_442764 prefixEnd_442764 134726369485873136304457 := by
  unfold tailWord_442764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074464883974560458023673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10765953178632747277364897 8074464883974560458023673)
  ·
    refine ⟨6055848662980920343517755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8074464883974560458023673 6055848662980920343517755)
    ·
      refine ⟨9083772994471380515276633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6055848662980920343517755 9083772994471380515276633)
      ·
        refine ⟨6812829745853535386457475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9083772994471380515276633 6812829745853535386457475)
        ·
          refine ⟨10219244618780303079686213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6812829745853535386457475 10219244618780303079686213)
          ·
            refine ⟨1916108366021306827441165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10219244618780303079686213 1916108366021306827441165)
            ·
              refine ⟨718540637257990060290437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1916108366021306827441165 718540637257990060290437)
              ·
                refine ⟨134726369485873136304457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 718540637257990060290437 134726369485873136304457)
                ·
                  rfl

theorem cell19_442764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_442764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442764 prefixEnd_442764 := by exact prefixLift 442764
  have htrace : WordTrace (prefixWord ++ tailWord_442764) baseStart_442764 baseEnd_442764 := by
    simpa [prefixWord, tailWord_442764, baseEnd_442764] using wordTrace_append hprefix tailTrace_442764
  have hstable : (prefixWord ++ tailWord_442764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442764).length < 2 ^ (prefixWord ++ tailWord_442764).sum := by decide
  have hdescent : baseEnd_442764 < baseStart_442764 := by decide
  rcases family_descends (prefixWord ++ tailWord_442764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442834 : List Nat := [3, 2, 2, 4, 1, 2, 2, 3]
def baseStart_442834 : Nat := 118140960795 + 442834 * 2 ^ 59
def prefixEnd_442834 : Nat := 4983230072969 + 3 ^ 40 * 442834 * 2
def baseEnd_442834 : Nat := 134747669424133714748711

theorem tailTrace_442834 : CollatzResearch.WordTrace tailWord_442834 prefixEnd_442834 134747669424133714748711 := by
  unfold tailWord_442834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037870719423880717773889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10767655251797015247397037 4037870719423880717773889)
  ·
    refine ⟨3028403039567910538330417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4037870719423880717773889 3028403039567910538330417)
    ·
      refine ⟨2271302279675932903747813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3028403039567910538330417 2271302279675932903747813)
      ·
        refine ⟨425869177439237419452715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2271302279675932903747813 425869177439237419452715)
        ·
          refine ⟨638803766158856129179073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425869177439237419452715 638803766158856129179073)
          ·
            refine ⟨479102824619142096884305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638803766158856129179073 479102824619142096884305)
            ·
              refine ⟨359327118464356572663229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479102824619142096884305 359327118464356572663229)
              ·
                refine ⟨134747669424133714748711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359327118464356572663229 134747669424133714748711)
                ·
                  rfl

theorem cell19_442834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_442834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442834 prefixEnd_442834 := by exact prefixLift 442834
  have htrace : WordTrace (prefixWord ++ tailWord_442834) baseStart_442834 baseEnd_442834 := by
    simpa [prefixWord, tailWord_442834, baseEnd_442834] using wordTrace_append hprefix tailTrace_442834
  have hstable : (prefixWord ++ tailWord_442834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442834).length < 2 ^ (prefixWord ++ tailWord_442834).sum := by decide
  have hdescent : baseEnd_442834 < baseStart_442834 := by decide
  rcases family_descends (prefixWord ++ tailWord_442834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442836 : List Nat := [2, 4, 1, 2, 2, 3, 2, 3]
def baseStart_442836 : Nat := 118140960795 + 442836 * 2 ^ 59
def prefixEnd_442836 : Nat := 4983230072969 + 3 ^ 40 * 442836 * 2
def baseEnd_442836 : Nat := 134748277993798302704261

theorem tailTrace_442836 : CollatzResearch.WordTrace tailWord_442836 prefixEnd_442836 134748277993798302704261 := by
  unfold tailWord_442836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075777911844138606334181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10767703882458851475112241 8075777911844138606334181)
  ·
    refine ⟨1514208358470775988687659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8075777911844138606334181 1514208358470775988687659)
    ·
      refine ⟨2271312537706163983031489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1514208358470775988687659 2271312537706163983031489)
      ·
        refine ⟨1703484403279622987273617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2271312537706163983031489 1703484403279622987273617)
        ·
          refine ⟨1277613302459717240455213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1703484403279622987273617 1277613302459717240455213)
          ·
            refine ⟨479104988422393965170705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1277613302459717240455213 479104988422393965170705)
            ·
              refine ⟨359328741316795473878029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479104988422393965170705 359328741316795473878029)
              ·
                refine ⟨134748277993798302704261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359328741316795473878029 134748277993798302704261)
                ·
                  rfl

theorem cell19_442836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_442836 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442836 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442836 prefixEnd_442836 := by exact prefixLift 442836
  have htrace : WordTrace (prefixWord ++ tailWord_442836) baseStart_442836 baseEnd_442836 := by
    simpa [prefixWord, tailWord_442836, baseEnd_442836] using wordTrace_append hprefix tailTrace_442836
  have hstable : (prefixWord ++ tailWord_442836).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442836).length < 2 ^ (prefixWord ++ tailWord_442836).sum := by decide
  have hdescent : baseEnd_442836 < baseStart_442836 := by decide
  rcases family_descends (prefixWord ++ tailWord_442836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442838 : List Nat := [5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_442838 : Nat := 118140960795 + 442838 * 2 ^ 59
def prefixEnd_442838 : Nat := 4983230072969 + 3 ^ 40 * 442838 * 2
def baseEnd_442838 : Nat := 134748886563462890659811

theorem tailTrace_442838 : CollatzResearch.WordTrace tailWord_442838 prefixEnd_442838 134748886563462890659811 := by
  unfold tailWord_442838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1009476798105064472140073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10767752513120687702827445 1009476798105064472140073)
  ·
    refine ⟨757107598578798354105055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1009476798105064472140073 757107598578798354105055)
    ·
      refine ⟨1135661397868197531157583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757107598578798354105055 1135661397868197531157583)
      ·
        refine ⟨1703492096802296296736375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135661397868197531157583 1703492096802296296736375)
        ·
          refine ⟨2555238145203444445104563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703492096802296296736375 2555238145203444445104563)
          ·
            refine ⟨3832857217805166667656845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555238145203444445104563 3832857217805166667656845)
            ·
              refine ⟨1437321456676937500371317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3832857217805166667656845 1437321456676937500371317)
              ·
                refine ⟨134748886563462890659811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1437321456676937500371317 134748886563462890659811)
                ·
                  rfl

theorem cell19_442838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_442838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442838 prefixEnd_442838 := by exact prefixLift 442838
  have htrace : WordTrace (prefixWord ++ tailWord_442838) baseStart_442838 baseEnd_442838 := by
    simpa [prefixWord, tailWord_442838, baseEnd_442838] using wordTrace_append hprefix tailTrace_442838
  have hstable : (prefixWord ++ tailWord_442838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442838).length < 2 ^ (prefixWord ++ tailWord_442838).sum := by decide
  have hdescent : baseEnd_442838 < baseStart_442838 := by decide
  rcases family_descends (prefixWord ++ tailWord_442838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442893 : List Nat := [1, 7, 1, 1, 1, 1, 2, 5]
def baseStart_442893 : Nat := 118140960795 + 442893 * 2 ^ 59
def prefixEnd_442893 : Nat := 4983230072969 + 3 ^ 40 * 442893 * 2
def baseEnd_442893 : Nat := 134765622229239059437439

theorem tailTrace_442893 : CollatzResearch.WordTrace tailWord_442893 prefixEnd_442893 134765622229239059437439 := by
  unfold tailWord_442893
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153634784481775947493333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10769089856321183964995555 16153634784481775947493333)
  ·
    refine ⟨378600815261291623769375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16153634784481775947493333 378600815261291623769375)
    ·
      refine ⟨567901222891937435654063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378600815261291623769375 567901222891937435654063)
      ·
        refine ⟨851851834337906153481095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567901222891937435654063 851851834337906153481095)
        ·
          refine ⟨1277777751506859230221643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851851834337906153481095 1277777751506859230221643)
          ·
            refine ⟨1916666627260288845332465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277777751506859230221643 1916666627260288845332465)
            ·
              refine ⟨1437499970445216633999349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916666627260288845332465 1437499970445216633999349)
              ·
                refine ⟨134765622229239059437439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1437499970445216633999349 134765622229239059437439)
                ·
                  rfl

theorem cell19_442893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_442893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442893 prefixEnd_442893 := by exact prefixLift 442893
  have htrace : WordTrace (prefixWord ++ tailWord_442893) baseStart_442893 baseEnd_442893 := by
    simpa [prefixWord, tailWord_442893, baseEnd_442893] using wordTrace_append hprefix tailTrace_442893
  have hstable : (prefixWord ++ tailWord_442893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442893).length < 2 ^ (prefixWord ++ tailWord_442893).sum := by decide
  have hdescent : baseEnd_442893 < baseStart_442893 := by decide
  rcases family_descends (prefixWord ++ tailWord_442893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442899 : List Nat := [1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_442899 : Nat := 118140960795 + 442899 * 2 ^ 59
def prefixEnd_442899 : Nat := 4983230072969 + 3 ^ 40 * 442899 * 2
def baseEnd_442899 : Nat := 134767447938232823304089

theorem tailTrace_442899 : CollatzResearch.WordTrace tailWord_442899 prefixEnd_442899 134767447938232823304089 := by
  unfold tailWord_442899
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153853622460038972211751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10769235748306692648141167 16153853622460038972211751)
  ·
    refine ⟨24230780433690058458317627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16153853622460038972211751 24230780433690058458317627)
    ·
      refine ⟨36346170650535087687476441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24230780433690058458317627 36346170650535087687476441)
      ·
        refine ⟨27259627987901315765607331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36346170650535087687476441 27259627987901315765607331)
        ·
          refine ⟨40889441981851973648410997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27259627987901315765607331 40889441981851973648410997)
          ·
            refine ⟨3833385185798622529538531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40889441981851973648410997 3833385185798622529538531)
            ·
              refine ⟨5750077778697933794307797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3833385185798622529538531 5750077778697933794307797)
              ·
                refine ⟨134767447938232823304089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5750077778697933794307797 134767447938232823304089)
                ·
                  rfl

theorem cell19_442899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_442899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442899 prefixEnd_442899 := by exact prefixLift 442899
  have htrace : WordTrace (prefixWord ++ tailWord_442899) baseStart_442899 baseEnd_442899 := by
    simpa [prefixWord, tailWord_442899, baseEnd_442899] using wordTrace_append hprefix tailTrace_442899
  have hstable : (prefixWord ++ tailWord_442899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442899).length < 2 ^ (prefixWord ++ tailWord_442899).sum := by decide
  have hdescent : baseEnd_442899 < baseStart_442899 := by decide
  rcases family_descends (prefixWord ++ tailWord_442899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442916 : List Nat := [2, 3, 1, 5, 8]
def baseStart_442916 : Nat := 118140960795 + 442916 * 2 ^ 59
def prefixEnd_442916 : Nat := 4983230072969 + 3 ^ 40 * 442916 * 2
def baseEnd_442916 : Nat := 4991578547421548923195

theorem tailTrace_442916 : CollatzResearch.WordTrace tailWord_442916 prefixEnd_442916 4991578547421548923195 := by
  unfold tailWord_442916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8077236831699225437790301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10769649108932300583720401 8077236831699225437790301)
  ·
    refine ⟨3028963811887209539171363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8077236831699225437790301 3028963811887209539171363)
    ·
      refine ⟨4543445717830814308757045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3028963811887209539171363 4543445717830814308757045)
      ·
        refine ⟨425948036046638841445973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4543445717830814308757045 425948036046638841445973)
        ·
          refine ⟨4991578547421548923195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 425948036046638841445973 4991578547421548923195)
          ·
            rfl

theorem cell19_442916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 8].length) (baseStart_442916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_442916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_442916 prefixEnd_442916 := by exact prefixLift 442916
  have htrace : WordTrace (prefixWord ++ tailWord_442916) baseStart_442916 baseEnd_442916 := by
    simpa [prefixWord, tailWord_442916, baseEnd_442916] using wordTrace_append hprefix tailTrace_442916
  have hstable : (prefixWord ++ tailWord_442916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442916).length < 2 ^ (prefixWord ++ tailWord_442916).sum := by decide
  have hdescent : baseEnd_442916 < baseStart_442916 := by decide
  rcases family_descends (prefixWord ++ tailWord_442916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443011 : List Nat := [1, 1, 1, 3, 3, 1, 6, 3]
def baseStart_443011 : Nat := 118140960795 + 443011 * 2 ^ 59
def prefixEnd_443011 : Nat := 4983230072969 + 3 ^ 40 * 443011 * 2
def baseEnd_443011 : Nat := 134801527839449748814895

theorem tailTrace_443011 : CollatzResearch.WordTrace tailWord_443011 prefixEnd_443011 134801527839449748814895 := by
  unfold tailWord_443011
  simp only [CollatzResearch.WordTrace]
  refine ⟨16157938598054282100288887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10771959065369521400192591 16157938598054282100288887)
  ·
    refine ⟨24236907897081423150433331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16157938598054282100288887 24236907897081423150433331)
    ·
      refine ⟨36355361845622134725649997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24236907897081423150433331 36355361845622134725649997)
      ·
        refine ⟨13633260692108300522118749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36355361845622134725649997 13633260692108300522118749)
        ·
          refine ⟨5112472759540612695794531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13633260692108300522118749 5112472759540612695794531)
          ·
            refine ⟨7668709139310919043691797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5112472759540612695794531 7668709139310919043691797)
            ·
              refine ⟨359470740905199330173053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7668709139310919043691797 359470740905199330173053)
              ·
                refine ⟨134801527839449748814895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359470740905199330173053 134801527839449748814895)
                ·
                  rfl

theorem cell19_443011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_443011 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443011 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443011 prefixEnd_443011 := by exact prefixLift 443011
  have htrace : WordTrace (prefixWord ++ tailWord_443011) baseStart_443011 baseEnd_443011 := by
    simpa [prefixWord, tailWord_443011, baseEnd_443011] using wordTrace_append hprefix tailTrace_443011
  have hstable : (prefixWord ++ tailWord_443011).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443011).length < 2 ^ (prefixWord ++ tailWord_443011).sum := by decide
  have hdescent : baseEnd_443011 < baseStart_443011 := by decide
  rcases family_descends (prefixWord ++ tailWord_443011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443028 : List Nat := [2, 4, 2, 2, 1, 3, 5]
def baseStart_443028 : Nat := 118140960795 + 443028 * 2 ^ 59
def prefixEnd_443028 : Nat := 4983230072969 + 3 ^ 40 * 443028 * 2
def baseEnd_443028 : Nat := 44935566893866248812357

theorem tailTrace_443028 : CollatzResearch.WordTrace tailWord_443028 prefixEnd_443028 44935566893866248812357 := by
  unfold tailWord_443028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8079279319496347001828869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10772372425995129335771825 8079279319496347001828869)
  ·
    refine ⟨1514864872405565062842913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8079279319496347001828869 1514864872405565062842913)
    ·
      refine ⟨1136148654304173797132185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1514864872405565062842913 1136148654304173797132185)
      ·
        refine ⟨852111490728130347849139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1136148654304173797132185 852111490728130347849139)
        ·
          refine ⟨1278167236092195521773709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852111490728130347849139 1278167236092195521773709)
          ·
            refine ⟨479312713534573320665141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1278167236092195521773709 479312713534573320665141)
            ·
              refine ⟨44935566893866248812357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 479312713534573320665141 44935566893866248812357)
              ·
                rfl

theorem cell19_443028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_443028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443028 prefixEnd_443028 := by exact prefixLift 443028
  have htrace : WordTrace (prefixWord ++ tailWord_443028) baseStart_443028 baseEnd_443028 := by
    simpa [prefixWord, tailWord_443028, baseEnd_443028] using wordTrace_append hprefix tailTrace_443028
  have hstable : (prefixWord ++ tailWord_443028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443028).length < 2 ^ (prefixWord ++ tailWord_443028).sum := by decide
  have hdescent : baseEnd_443028 < baseStart_443028 := by decide
  rcases family_descends (prefixWord ++ tailWord_443028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443085 : List Nat := [1, 6, 2, 1, 2, 7]
def baseStart_443085 : Nat := 118140960795 + 443085 * 2 ^ 59
def prefixEnd_443085 : Nat := 4983230072969 + 3 ^ 40 * 443085 * 2
def baseEnd_443085 : Nat := 14980449435226611463361

theorem tailTrace_443085 : CollatzResearch.WordTrace tailWord_443085 prefixEnd_443085 14980449435226611463361 := by
  unfold tailWord_443085
  simp only [CollatzResearch.WordTrace]
  refine ⟨16160637599786192738482709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10773758399857461825655139 16160637599786192738482709)
  ·
    refine ⟨757529887489977784616377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16160637599786192738482709 757529887489977784616377)
    ·
      refine ⟨568147415617483338462283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 757529887489977784616377 568147415617483338462283)
      ·
        refine ⟨852221123426225007693425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568147415617483338462283 852221123426225007693425)
        ·
          refine ⟨639165842569668755770069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852221123426225007693425 639165842569668755770069)
          ·
            refine ⟨14980449435226611463361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 639165842569668755770069 14980449435226611463361)
            ·
              rfl

theorem cell19_443085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 7].length) (baseStart_443085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443085 prefixEnd_443085 := by exact prefixLift 443085
  have htrace : WordTrace (prefixWord ++ tailWord_443085) baseStart_443085 baseEnd_443085 := by
    simpa [prefixWord, tailWord_443085, baseEnd_443085] using wordTrace_append hprefix tailTrace_443085
  have hstable : (prefixWord ++ tailWord_443085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443085).length < 2 ^ (prefixWord ++ tailWord_443085).sum := by decide
  have hdescent : baseEnd_443085 < baseStart_443085 := by decide
  rcases family_descends (prefixWord ++ tailWord_443085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443146 : List Nat := [3, 1, 2, 2, 1, 2, 8]
def baseStart_443146 : Nat := 118140960795 + 443146 * 2 ^ 59
def prefixEnd_443146 : Nat := 4983230072969 + 3 ^ 40 * 443146 * 2
def baseEnd_443146 : Nat := 44947535430603145271509

theorem tailTrace_443146 : CollatzResearch.WordTrace tailWord_443146 prefixEnd_443146 44947535430603145271509 := by
  unfold tailWord_443146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040715613141300039113323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10775241635043466770968861 4040715613141300039113323)
  ·
    refine ⟨6061073419711950058669985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4040715613141300039113323 6061073419711950058669985)
    ·
      refine ⟨4545805064783962544002489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6061073419711950058669985 4545805064783962544002489)
      ·
        refine ⟨3409353798587971908001867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4545805064783962544002489 3409353798587971908001867)
        ·
          refine ⟨5114030697881957862002801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409353798587971908001867 5114030697881957862002801)
          ·
            refine ⟨3835523023411468396502101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114030697881957862002801 3835523023411468396502101)
            ·
              refine ⟨44947535430603145271509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3835523023411468396502101 44947535430603145271509)
              ·
                rfl

theorem cell19_443146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_443146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443146 prefixEnd_443146 := by exact prefixLift 443146
  have htrace : WordTrace (prefixWord ++ tailWord_443146) baseStart_443146 baseEnd_443146 := by
    simpa [prefixWord, tailWord_443146, baseEnd_443146] using wordTrace_append hprefix tailTrace_443146
  have hstable : (prefixWord ++ tailWord_443146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443146).length < 2 ^ (prefixWord ++ tailWord_443146).sum := by decide
  have hdescent : baseEnd_443146 < baseStart_443146 := by decide
  rcases family_descends (prefixWord ++ tailWord_443146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443317 : List Nat := [1, 3, 3, 2, 1, 1, 8]
def baseStart_443317 : Nat := 118140960795 + 443317 * 2 ^ 59
def prefixEnd_443317 : Nat := 4983230072969 + 3 ^ 40 * 443317 * 2
def baseEnd_443317 : Nat := 44964879666043902004687

theorem tailTrace_443317 : CollatzResearch.WordTrace tailWord_443317 prefixEnd_443317 44964879666043902004687 := by
  unfold tailWord_443317
  simp only [CollatzResearch.WordTrace]
  refine ⟨16169099334945696360928205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10779399556630464240618803 16169099334945696360928205)
  ·
    refine ⟨6063412250604636135348077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16169099334945696360928205 6063412250604636135348077)
    ·
      refine ⟨2273779593976738550755529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6063412250604636135348077 2273779593976738550755529)
      ·
        refine ⟨1705334695482553913066647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2273779593976738550755529 1705334695482553913066647)
        ·
          refine ⟨2558002043223830869599971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705334695482553913066647 2558002043223830869599971)
          ·
            refine ⟨3837003064835746304399957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558002043223830869599971 3837003064835746304399957)
            ·
              refine ⟨44964879666043902004687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3837003064835746304399957 44964879666043902004687)
              ·
                rfl

theorem cell19_443317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_443317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443317 prefixEnd_443317 := by exact prefixLift 443317
  have htrace : WordTrace (prefixWord ++ tailWord_443317) baseStart_443317 baseEnd_443317 := by
    simpa [prefixWord, tailWord_443317, baseEnd_443317] using wordTrace_append hprefix tailTrace_443317
  have hstable : (prefixWord ++ tailWord_443317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443317).length < 2 ^ (prefixWord ++ tailWord_443317).sum := by decide
  have hdescent : baseEnd_443317 < baseStart_443317 := by decide
  rcases family_descends (prefixWord ++ tailWord_443317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443349 : List Nat := [1, 3, 2, 3, 4, 1, 2, 3]
def baseStart_443349 : Nat := 118140960795 + 443349 * 2 ^ 59
def prefixEnd_443349 : Nat := 4983230072969 + 3 ^ 40 * 443349 * 2
def baseEnd_443349 : Nat := 134904376112765113302863

theorem tailTrace_443349 : CollatzResearch.WordTrace tailWord_443349 prefixEnd_443349 134904376112765113302863 := by
  unfold tailWord_443349
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170266470829765826093101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10780177647219843884062067 16170266470829765826093101)
  ·
    refine ⟨6063849926561162184784913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16170266470829765826093101 6063849926561162184784913)
    ·
      refine ⟨4547887444920871638588685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6063849926561162184784913 4547887444920871638588685)
      ·
        refine ⟨1705457791845326864470757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4547887444920871638588685 1705457791845326864470757)
        ·
          refine ⟨319773335970998787088267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1705457791845326864470757 319773335970998787088267)
          ·
            refine ⟨479660003956498180632401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319773335970998787088267 479660003956498180632401)
            ·
              refine ⟨359745002967373635474301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479660003956498180632401 359745002967373635474301)
              ·
                refine ⟨134904376112765113302863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359745002967373635474301 134904376112765113302863)
                ·
                  rfl

theorem cell19_443349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 3].length) (baseStart_443349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443349 prefixEnd_443349 := by exact prefixLift 443349
  have htrace : WordTrace (prefixWord ++ tailWord_443349) baseStart_443349 baseEnd_443349 := by
    simpa [prefixWord, tailWord_443349, baseEnd_443349] using wordTrace_append hprefix tailTrace_443349
  have hstable : (prefixWord ++ tailWord_443349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443349).length < 2 ^ (prefixWord ++ tailWord_443349).sum := by decide
  have hdescent : baseEnd_443349 < baseStart_443349 := by decide
  rcases family_descends (prefixWord ++ tailWord_443349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443353 : List Nat := [1, 2, 1, 2, 5, 1, 4, 3]
def baseStart_443353 : Nat := 118140960795 + 443353 * 2 ^ 59
def prefixEnd_443353 : Nat := 4983230072969 + 3 ^ 40 * 443353 * 2
def baseEnd_443353 : Nat := 134905593252094289213963

theorem tailTrace_443353 : CollatzResearch.WordTrace tailWord_443353 prefixEnd_443353 134905593252094289213963 := by
  unfold tailWord_443353
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170412362815274509238713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10780274908543516339492475 16170412362815274509238713)
  ·
    refine ⟨12127809272111455881929035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16170412362815274509238713 12127809272111455881929035)
    ·
      refine ⟨18191713908167183822893553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127809272111455881929035 18191713908167183822893553)
      ·
        refine ⟨13643785431125387867170165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18191713908167183822893553 13643785431125387867170165)
        ·
          refine ⟨1279104884168005112547203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13643785431125387867170165 1279104884168005112547203)
          ·
            refine ⟨1918657326252007668820805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279104884168005112547203 1918657326252007668820805)
            ·
              refine ⟨359748248672251437903901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1918657326252007668820805 359748248672251437903901)
              ·
                refine ⟨134905593252094289213963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359748248672251437903901 134905593252094289213963)
                ·
                  rfl

theorem cell19_443353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_443353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443353 prefixEnd_443353 := by exact prefixLift 443353
  have htrace : WordTrace (prefixWord ++ tailWord_443353) baseStart_443353 baseEnd_443353 := by
    simpa [prefixWord, tailWord_443353, baseEnd_443353] using wordTrace_append hprefix tailTrace_443353
  have hstable : (prefixWord ++ tailWord_443353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443353).length < 2 ^ (prefixWord ++ tailWord_443353).sum := by decide
  have hdescent : baseEnd_443353 < baseStart_443353 := by decide
  rcases family_descends (prefixWord ++ tailWord_443353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443393 : List Nat := [1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_443393 : Nat := 118140960795 + 443393 * 2 ^ 59
def prefixEnd_443393 : Nat := 4983230072969 + 3 ^ 40 * 443393 * 2
def baseEnd_443393 : Nat := 134917764645386048324965

theorem tailTrace_443393 : CollatzResearch.WordTrace tailWord_443393 prefixEnd_443393 134917764645386048324965 := by
  unfold tailWord_443393
  simp only [CollatzResearch.WordTrace]
  refine ⟨16171871282670361340694833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10781247521780240893796555 16171871282670361340694833)
  ·
    refine ⟨12128903462002771005521125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16171871282670361340694833 12128903462002771005521125)
    ·
      refine ⟨2274169399125519563535211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12128903462002771005521125 2274169399125519563535211)
      ·
        refine ⟨3411254098688279345302817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274169399125519563535211 3411254098688279345302817)
        ·
          refine ⟨2558440574016209508977113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3411254098688279345302817 2558440574016209508977113)
          ·
            refine ⟨1918830430512157131732835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2558440574016209508977113 1918830430512157131732835)
            ·
              refine ⟨2878245645768235697599253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918830430512157131732835 2878245645768235697599253)
              ·
                refine ⟨134917764645386048324965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2878245645768235697599253 134917764645386048324965)
                ·
                  rfl

theorem cell19_443393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_443393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443393 prefixEnd_443393 := by exact prefixLift 443393
  have htrace : WordTrace (prefixWord ++ tailWord_443393) baseStart_443393 baseEnd_443393 := by
    simpa [prefixWord, tailWord_443393, baseEnd_443393] using wordTrace_append hprefix tailTrace_443393
  have hstable : (prefixWord ++ tailWord_443393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443393).length < 2 ^ (prefixWord ++ tailWord_443393).sum := by decide
  have hdescent : baseEnd_443393 < baseStart_443393 := by decide
  rcases family_descends (prefixWord ++ tailWord_443393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443446 : List Nat := [5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_443446 : Nat := 118140960795 + 443446 * 2 ^ 59
def prefixEnd_443446 : Nat := 4983230072969 + 3 ^ 40 * 443446 * 2
def baseEnd_443446 : Nat := 134933891741497629147043

theorem tailTrace_443446 : CollatzResearch.WordTrace tailWord_443446 prefixEnd_443446 134933891741497629147043 := by
  unfold tailWord_443446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010862771967396962023387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10782536234318900928249461 1010862771967396962023387)
  ·
    refine ⟨1516294157951095443035081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010862771967396962023387 1516294157951095443035081)
    ·
      refine ⟨1137220618463321582276311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1516294157951095443035081 1137220618463321582276311)
      ·
        refine ⟨1705830927694982373414467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137220618463321582276311 1705830927694982373414467)
        ·
          refine ⟨2558746391542473560121701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705830927694982373414467 2558746391542473560121701)
          ·
            refine ⟨479764948414213792522819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2558746391542473560121701 479764948414213792522819)
            ·
              refine ⟨719647422621320688784229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479764948414213792522819 719647422621320688784229)
              ·
                refine ⟨134933891741497629147043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719647422621320688784229 134933891741497629147043)
                ·
                  rfl

theorem cell19_443446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_443446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443446 prefixEnd_443446 := by exact prefixLift 443446
  have htrace : WordTrace (prefixWord ++ tailWord_443446) baseStart_443446 baseEnd_443446 := by
    simpa [prefixWord, tailWord_443446, baseEnd_443446] using wordTrace_append hprefix tailTrace_443446
  have hstable : (prefixWord ++ tailWord_443446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443446).length < 2 ^ (prefixWord ++ tailWord_443446).sum := by decide
  have hdescent : baseEnd_443446 < baseStart_443446 := by decide
  rcases family_descends (prefixWord ++ tailWord_443446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443448 : List Nat := [2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_443448 : Nat := 118140960795 + 443448 * 2 ^ 59
def prefixEnd_443448 : Nat := 4983230072969 + 3 ^ 40 * 443448 * 2
def baseEnd_443448 : Nat := 134934500311162217102593

theorem tailTrace_443448 : CollatzResearch.WordTrace tailWord_443448 prefixEnd_443448 134934500311162217102593 := by
  unfold tailWord_443448
  simp only [CollatzResearch.WordTrace]
  refine ⟨8086938648735552866973499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10782584864980737155964665 8086938648735552866973499)
  ·
    refine ⟨12130407973103329300460249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8086938648735552866973499 12130407973103329300460249)
    ·
      refine ⟨9097805979827496975345187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12130407973103329300460249 9097805979827496975345187)
      ·
        refine ⟨13646708969741245463017781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097805979827496975345187 13646708969741245463017781)
        ·
          refine ⟨1279378965913241762157917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13646708969741245463017781 1279378965913241762157917)
          ·
            refine ⟨479767112217465660809219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1279378965913241762157917 479767112217465660809219)
            ·
              refine ⟨719650668326198491213829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479767112217465660809219 719650668326198491213829)
              ·
                refine ⟨134934500311162217102593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719650668326198491213829 134934500311162217102593)
                ·
                  rfl

theorem cell19_443448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_443448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443448 prefixEnd_443448 := by exact prefixLift 443448
  have htrace : WordTrace (prefixWord ++ tailWord_443448) baseStart_443448 baseEnd_443448 := by
    simpa [prefixWord, tailWord_443448, baseEnd_443448] using wordTrace_append hprefix tailTrace_443448
  have hstable : (prefixWord ++ tailWord_443448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443448).length < 2 ^ (prefixWord ++ tailWord_443448).sum := by decide
  have hdescent : baseEnd_443448 < baseStart_443448 := by decide
  rcases family_descends (prefixWord ++ tailWord_443448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443450 : List Nat := [3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_443450 : Nat := 118140960795 + 443450 * 2 ^ 59
def prefixEnd_443450 : Nat := 4983230072969 + 3 ^ 40 * 443450 * 2
def baseEnd_443450 : Nat := 134935108880826805058143

theorem tailTrace_443450 : CollatzResearch.WordTrace tailWord_443450 prefixEnd_443450 134935108880826805058143 := by
  unfold tailWord_443450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043487560865965018879951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10782633495642573383679869 4043487560865965018879951)
  ·
    refine ⟨6065231341298947528319927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4043487560865965018879951 6065231341298947528319927)
    ·
      refine ⟨9097847011948421292479891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065231341298947528319927 9097847011948421292479891)
      ·
        refine ⟨13646770517922631938719837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097847011948421292479891 13646770517922631938719837)
        ·
          refine ⟨5117538944220986977019939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13646770517922631938719837 5117538944220986977019939)
          ·
            refine ⟨7676308416331480465529909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117538944220986977019939 7676308416331480465529909)
            ·
              refine ⟨719653914031076293643429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7676308416331480465529909 719653914031076293643429)
              ·
                refine ⟨134935108880826805058143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719653914031076293643429 134935108880826805058143)
                ·
                  rfl

theorem cell19_443450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_443450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443450 prefixEnd_443450 := by exact prefixLift 443450
  have htrace : WordTrace (prefixWord ++ tailWord_443450) baseStart_443450 baseEnd_443450 := by
    simpa [prefixWord, tailWord_443450, baseEnd_443450] using wordTrace_append hprefix tailTrace_443450
  have hstable : (prefixWord ++ tailWord_443450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443450).length < 2 ^ (prefixWord ++ tailWord_443450).sum := by decide
  have hdescent : baseEnd_443450 < baseStart_443450 := by decide
  rcases family_descends (prefixWord ++ tailWord_443450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443524 : List Nat := [2, 3, 2, 1, 2, 2, 4, 3]
def baseStart_443524 : Nat := 118140960795 + 443524 * 2 ^ 59
def prefixEnd_443524 : Nat := 4983230072969 + 3 ^ 40 * 443524 * 2
def baseEnd_443524 : Nat := 134957625958416559413497

theorem tailTrace_443524 : CollatzResearch.WordTrace tailWord_443524 prefixEnd_443524 134957625958416559413497 := by
  unfold tailWord_443524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088324622597885356856813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10784432830130513809142417 8088324622597885356856813)
  ·
    refine ⟨3033121733474207008821305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8088324622597885356856813 3033121733474207008821305)
    ·
      refine ⟨2274841300105655256615979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3033121733474207008821305 2274841300105655256615979)
      ·
        refine ⟨3412261950158482884923969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274841300105655256615979 3412261950158482884923969)
        ·
          refine ⟨2559196462618862163692977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3412261950158482884923969 2559196462618862163692977)
          ·
            refine ⟨1919397346964146622769733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559196462618862163692977 1919397346964146622769733)
            ·
              refine ⟨359887002555777491769325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1919397346964146622769733 359887002555777491769325)
              ·
                refine ⟨134957625958416559413497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359887002555777491769325 134957625958416559413497)
                ·
                  rfl

theorem cell19_443524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_443524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443524 prefixEnd_443524 := by exact prefixLift 443524
  have htrace : WordTrace (prefixWord ++ tailWord_443524) baseStart_443524 baseEnd_443524 := by
    simpa [prefixWord, tailWord_443524, baseEnd_443524] using wordTrace_append hprefix tailTrace_443524
  have hstable : (prefixWord ++ tailWord_443524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443524).length < 2 ^ (prefixWord ++ tailWord_443524).sum := by decide
  have hdescent : baseEnd_443524 < baseStart_443524 := by decide
  rcases family_descends (prefixWord ++ tailWord_443524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443562 : List Nat := [3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_443562 : Nat := 118140960795 + 443562 * 2 ^ 59
def prefixEnd_443562 : Nat := 4983230072969 + 3 ^ 40 * 443562 * 2
def baseEnd_443562 : Nat := 134969188782043730568949

theorem tailTrace_443562 : CollatzResearch.WordTrace tailWord_443562 prefixEnd_443562 134969188782043730568949 := by
  unfold tailWord_443562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044508804764525800899235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10785356812705402135731293 4044508804764525800899235)
  ·
    refine ⟨6066763207146788701348853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4044508804764525800899235 6066763207146788701348853)
    ·
      refine ⟨568759050670011440751455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6066763207146788701348853 568759050670011440751455)
      ·
        refine ⟨853138576005017161127183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568759050670011440751455 853138576005017161127183)
        ·
          refine ⟨1279707864007525741690775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853138576005017161127183 1279707864007525741690775)
          ·
            refine ⟨1919561796011288612536163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279707864007525741690775 1919561796011288612536163)
            ·
              refine ⟨2879342694016932918804245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919561796011288612536163 2879342694016932918804245)
              ·
                refine ⟨134969188782043730568949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2879342694016932918804245 134969188782043730568949)
                ·
                  rfl

theorem cell19_443562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_443562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443562 prefixEnd_443562 := by exact prefixLift 443562
  have htrace : WordTrace (prefixWord ++ tailWord_443562) baseStart_443562 baseEnd_443562 := by
    simpa [prefixWord, tailWord_443562, baseEnd_443562] using wordTrace_append hprefix tailTrace_443562
  have hstable : (prefixWord ++ tailWord_443562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443562).length < 2 ^ (prefixWord ++ tailWord_443562).sum := by decide
  have hdescent : baseEnd_443562 < baseStart_443562 := by decide
  rcases family_descends (prefixWord ++ tailWord_443562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443693 : List Nat := [1, 5, 3, 1, 1, 1, 4, 3]
def baseStart_443693 : Nat := 118140960795 + 443693 * 2 ^ 59
def prefixEnd_443693 : Nat := 4983230072969 + 3 ^ 40 * 443693 * 2
def baseEnd_443693 : Nat := 135009050095074241657481

theorem tailTrace_443693 : CollatzResearch.WordTrace tailWord_443693 prefixEnd_443693 135009050095074241657481 := by
  unfold tailWord_443693
  simp only [CollatzResearch.WordTrace]
  refine ⟨16182813181583512576615733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10788542121055675051077155 16182813181583512576615733)
  ·
    refine ⟨1517138735773454304057725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16182813181583512576615733 1517138735773454304057725)
    ·
      refine ⟨568927025915045364021647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1517138735773454304057725 568927025915045364021647)
      ·
        refine ⟨853390538872568046032471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568927025915045364021647 853390538872568046032471)
        ·
          refine ⟨1280085808308852069048707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853390538872568046032471 1280085808308852069048707)
          ·
            refine ⟨1920128712463278103573061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280085808308852069048707 1920128712463278103573061)
            ·
              refine ⟨360024133586864644419949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1920128712463278103573061 360024133586864644419949)
              ·
                refine ⟨135009050095074241657481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360024133586864644419949 135009050095074241657481)
                ·
                  rfl

theorem cell19_443693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_443693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443693 prefixEnd_443693 := by exact prefixLift 443693
  have htrace : WordTrace (prefixWord ++ tailWord_443693) baseStart_443693 baseEnd_443693 := by
    simpa [prefixWord, tailWord_443693, baseEnd_443693] using wordTrace_append hprefix tailTrace_443693
  have hstable : (prefixWord ++ tailWord_443693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443693).length < 2 ^ (prefixWord ++ tailWord_443693).sum := by decide
  have hdescent : baseEnd_443693 < baseStart_443693 := by decide
  rcases family_descends (prefixWord ++ tailWord_443693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443697 : List Nat := [1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_443697 : Nat := 118140960795 + 443697 * 2 ^ 59
def prefixEnd_443697 : Nat := 4983230072969 + 3 ^ 40 * 443697 * 2
def baseEnd_443697 : Nat := 135010267234403417568581

theorem tailTrace_443697 : CollatzResearch.WordTrace tailWord_443697 prefixEnd_443697 135010267234403417568581 := by
  unfold tailWord_443697
  simp only [CollatzResearch.WordTrace]
  refine ⟨16182959073569021259761345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10788639382379347506507563 16182959073569021259761345)
  ·
    refine ⟨12137219305176765944821009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16182959073569021259761345 12137219305176765944821009)
    ·
      refine ⟨9102914478882574458615757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12137219305176765944821009 9102914478882574458615757)
      ·
        refine ⟨3413592929580965421980909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9102914478882574458615757 3413592929580965421980909)
        ·
          refine ⟨1280097348592862033242841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3413592929580965421980909 1280097348592862033242841)
          ·
            refine ⟨960073011444646524932131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280097348592862033242841 960073011444646524932131)
            ·
              refine ⟨1440109517166969787398197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960073011444646524932131 1440109517166969787398197)
              ·
                refine ⟨135010267234403417568581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1440109517166969787398197 135010267234403417568581)
                ·
                  rfl

theorem cell19_443697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_443697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443697 prefixEnd_443697 := by exact prefixLift 443697
  have htrace : WordTrace (prefixWord ++ tailWord_443697) baseStart_443697 baseEnd_443697 := by
    simpa [prefixWord, tailWord_443697, baseEnd_443697] using wordTrace_append hprefix tailTrace_443697
  have hstable : (prefixWord ++ tailWord_443697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443697).length < 2 ^ (prefixWord ++ tailWord_443697).sum := by decide
  have hdescent : baseEnd_443697 < baseStart_443697 := by decide
  rcases family_descends (prefixWord ++ tailWord_443697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443735 : List Nat := [1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_443735 : Nat := 118140960795 + 443735 * 2 ^ 59
def prefixEnd_443735 : Nat := 4983230072969 + 3 ^ 40 * 443735 * 2
def baseEnd_443735 : Nat := 135021830058030588724033

theorem tailTrace_443735 : CollatzResearch.WordTrace tailWord_443735 prefixEnd_443735 135021830058030588724033 := by
  unfold tailWord_443735
  simp only [CollatzResearch.WordTrace]
  refine ⟨16184345047431353749644659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10789563364954235833096439 16184345047431353749644659)
  ·
    refine ⟨24276517571147030624466989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16184345047431353749644659 24276517571147030624466989)
    ·
      refine ⟨9103694089180136484175121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24276517571147030624466989 9103694089180136484175121)
      ·
        refine ⟨6827770566885102363131341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9103694089180136484175121 6827770566885102363131341)
        ·
          refine ⟨2560413962581913386174253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6827770566885102363131341 2560413962581913386174253)
          ·
            refine ⟨960155235968217519815345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2560413962581913386174253 960155235968217519815345)
            ·
              refine ⟨720116426976163139861509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960155235968217519815345 720116426976163139861509)
              ·
                refine ⟨135021830058030588724033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720116426976163139861509 135021830058030588724033)
                ·
                  rfl

theorem cell19_443735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_443735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443735 prefixEnd_443735 := by exact prefixLift 443735
  have htrace : WordTrace (prefixWord ++ tailWord_443735) baseStart_443735 baseEnd_443735 := by
    simpa [prefixWord, tailWord_443735, baseEnd_443735] using wordTrace_append hprefix tailTrace_443735
  have hstable : (prefixWord ++ tailWord_443735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443735).length < 2 ^ (prefixWord ++ tailWord_443735).sum := by decide
  have hdescent : baseEnd_443735 < baseStart_443735 := by decide
  rcases family_descends (prefixWord ++ tailWord_443735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443737 : List Nat := [1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_443737 : Nat := 118140960795 + 443737 * 2 ^ 59
def prefixEnd_443737 : Nat := 4983230072969 + 3 ^ 40 * 443737 * 2
def baseEnd_443737 : Nat := 135022438627695176679583

theorem tailTrace_443737 : CollatzResearch.WordTrace tailWord_443737 prefixEnd_443737 135022438627695176679583 := by
  unfold tailWord_443737
  simp only [CollatzResearch.WordTrace]
  refine ⟨16184417993424108091217465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10789611995616072060811643 16184417993424108091217465)
  ·
    refine ⟨12138313495068081068413099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16184417993424108091217465 12138313495068081068413099)
    ·
      refine ⟨18207470242602121602619649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12138313495068081068413099 18207470242602121602619649)
      ·
        refine ⟨13655602681951591201964737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18207470242602121602619649 13655602681951591201964737)
        ·
          refine ⟨10241702011463693401473553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13655602681951591201964737 10241702011463693401473553)
          ·
            refine ⟨7681276508597770051105165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10241702011463693401473553 7681276508597770051105165)
            ·
              refine ⟨2880478690724163769164437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7681276508597770051105165 2880478690724163769164437)
              ·
                refine ⟨135022438627695176679583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2880478690724163769164437 135022438627695176679583)
                ·
                  rfl

theorem cell19_443737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_443737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443737 prefixEnd_443737 := by exact prefixLift 443737
  have htrace : WordTrace (prefixWord ++ tailWord_443737) baseStart_443737 baseEnd_443737 := by
    simpa [prefixWord, tailWord_443737, baseEnd_443737] using wordTrace_append hprefix tailTrace_443737
  have hstable : (prefixWord ++ tailWord_443737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443737).length < 2 ^ (prefixWord ++ tailWord_443737).sum := by decide
  have hdescent : baseEnd_443737 < baseStart_443737 := by decide
  rcases family_descends (prefixWord ++ tailWord_443737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443811 : List Nat := [1, 1, 1, 4, 1, 3, 5, 3]
def baseStart_443811 : Nat := 118140960795 + 443811 * 2 ^ 59
def prefixEnd_443811 : Nat := 4983230072969 + 3 ^ 40 * 443811 * 2
def baseEnd_443811 : Nat := 135044955705284931034937

theorem tailTrace_443811 : CollatzResearch.WordTrace tailWord_443811 prefixEnd_443811 135044955705284931034937 := by
  unfold tailWord_443811
  simp only [CollatzResearch.WordTrace]
  refine ⟨16187116995156018729411287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10791411330104012486274191 16187116995156018729411287)
  ·
    refine ⟨24280675492734028094116931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16187116995156018729411287 24280675492734028094116931)
    ·
      refine ⟨36421013239101042141175397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24280675492734028094116931 36421013239101042141175397)
      ·
        refine ⟨6828939982331445401470387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36421013239101042141175397 6828939982331445401470387)
        ·
          refine ⟨10243409973497168102205581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828939982331445401470387 10243409973497168102205581)
          ·
            refine ⟨3841278740061438038327093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10243409973497168102205581 3841278740061438038327093)
            ·
              refine ⟨360119881880759816093165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3841278740061438038327093 360119881880759816093165)
              ·
                refine ⟨135044955705284931034937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360119881880759816093165 135044955705284931034937)
                ·
                  rfl

theorem cell19_443811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_443811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443811 prefixEnd_443811 := by exact prefixLift 443811
  have htrace : WordTrace (prefixWord ++ tailWord_443811) baseStart_443811 baseEnd_443811 := by
    simpa [prefixWord, tailWord_443811, baseEnd_443811] using wordTrace_append hprefix tailTrace_443811
  have hstable : (prefixWord ++ tailWord_443811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443811).length < 2 ^ (prefixWord ++ tailWord_443811).sum := by decide
  have hdescent : baseEnd_443811 < baseStart_443811 := by decide
  rcases family_descends (prefixWord ++ tailWord_443811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443866 : List Nat := [3, 1, 1, 2, 3, 4, 2, 3]
def baseStart_443866 : Nat := 118140960795 + 443866 * 2 ^ 59
def prefixEnd_443866 : Nat := 4983230072969 + 3 ^ 40 * 443866 * 2
def baseEnd_443866 : Nat := 135061691371061099812565

theorem tailTrace_443866 : CollatzResearch.WordTrace tailWord_443866 prefixEnd_443866 135061691371061099812565 := by
  unfold tailWord_443866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047280752489190780665863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10792748673304508748442301 4047280752489190780665863)
  ·
    refine ⟨6070921128733786170998795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4047280752489190780665863 6070921128733786170998795)
    ·
      refine ⟨9106381693100679256498193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6070921128733786170998795 9106381693100679256498193)
      ·
        refine ⟨6829786269825509442373645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9106381693100679256498193 6829786269825509442373645)
        ·
          refine ⟨2561169851184566040890117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6829786269825509442373645 2561169851184566040890117)
          ·
            refine ⟨480219347097106132666897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2561169851184566040890117 480219347097106132666897)
            ·
              refine ⟨360164510322829599500173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480219347097106132666897 360164510322829599500173)
              ·
                refine ⟨135061691371061099812565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360164510322829599500173 135061691371061099812565)
                ·
                  rfl

theorem cell19_443866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_443866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443866 prefixEnd_443866 := by exact prefixLift 443866
  have htrace : WordTrace (prefixWord ++ tailWord_443866) baseStart_443866 baseEnd_443866 := by
    simpa [prefixWord, tailWord_443866, baseEnd_443866] using wordTrace_append hprefix tailTrace_443866
  have hstable : (prefixWord ++ tailWord_443866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443866).length < 2 ^ (prefixWord ++ tailWord_443866).sum := by decide
  have hdescent : baseEnd_443866 < baseStart_443866 := by decide
  rcases family_descends (prefixWord ++ tailWord_443866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443885 : List Nat := [1, 5, 1, 3, 2, 2, 5]
def baseStart_443885 : Nat := 118140960795 + 443885 * 2 ^ 59
def prefixEnd_443885 : Nat := 4983230072969 + 3 ^ 40 * 443885 * 2
def baseEnd_443885 : Nat := 45022490927624895130097

theorem tailTrace_443885 : CollatzResearch.WordTrace tailWord_443885 prefixEnd_443885 45022490927624895130097 := by
  unfold tailWord_443885
  simp only [CollatzResearch.WordTrace]
  refine ⟨16189815996887929367605109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10793210664591952911736739 16189815996887929367605109)
  ·
    refine ⟨1517795249708243378212979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16189815996887929367605109 1517795249708243378212979)
    ·
      refine ⟨2276692874562365067319469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1517795249708243378212979 2276692874562365067319469)
      ·
        refine ⟨853759827960886900244801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2276692874562365067319469 853759827960886900244801)
        ·
          refine ⟨640319870970665175183601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853759827960886900244801 640319870970665175183601)
          ·
            refine ⟨480239903227998881387701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640319870970665175183601 480239903227998881387701)
            ·
              refine ⟨45022490927624895130097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 480239903227998881387701 45022490927624895130097)
              ·
                rfl

theorem cell19_443885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_443885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443885 prefixEnd_443885 := by exact prefixLift 443885
  have htrace : WordTrace (prefixWord ++ tailWord_443885) baseStart_443885 baseEnd_443885 := by
    simpa [prefixWord, tailWord_443885, baseEnd_443885] using wordTrace_append hprefix tailTrace_443885
  have hstable : (prefixWord ++ tailWord_443885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443885).length < 2 ^ (prefixWord ++ tailWord_443885).sum := by decide
  have hdescent : baseEnd_443885 < baseStart_443885 := by decide
  rcases family_descends (prefixWord ++ tailWord_443885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443889 : List Nat := [1, 2, 2, 2, 3, 2, 7]
def baseStart_443889 : Nat := 118140960795 + 443889 * 2 ^ 59
def prefixEnd_443889 : Nat := 4983230072969 + 3 ^ 40 * 443889 * 2
def baseEnd_443889 : Nat := 45022896640734620433797

theorem tailTrace_443889 : CollatzResearch.WordTrace tailWord_443889 prefixEnd_443889 45022896640734620433797 := by
  unfold tailWord_443889
  simp only [CollatzResearch.WordTrace]
  refine ⟨16189961888873438050750721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10793307925915625367167147 16189961888873438050750721)
  ·
    refine ⟨12142471416655078538063041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16189961888873438050750721 12142471416655078538063041)
    ·
      refine ⟨9106853562491308903547281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12142471416655078538063041 9106853562491308903547281)
      ·
        refine ⟨6830140171868481677660461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9106853562491308903547281 6830140171868481677660461)
        ·
          refine ⟨2561302564450680629122673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6830140171868481677660461 2561302564450680629122673)
          ·
            refine ⟨1920976923338010471842005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2561302564450680629122673 1920976923338010471842005)
            ·
              refine ⟨45022896640734620433797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1920976923338010471842005 45022896640734620433797)
              ·
                rfl

theorem cell19_443889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_443889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443889 prefixEnd_443889 := by exact prefixLift 443889
  have htrace : WordTrace (prefixWord ++ tailWord_443889) baseStart_443889 baseEnd_443889 := by
    simpa [prefixWord, tailWord_443889, baseEnd_443889] using wordTrace_append hprefix tailTrace_443889
  have hstable : (prefixWord ++ tailWord_443889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443889).length < 2 ^ (prefixWord ++ tailWord_443889).sum := by decide
  have hdescent : baseEnd_443889 < baseStart_443889 := by decide
  rcases family_descends (prefixWord ++ tailWord_443889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443902 : List Nat := [4, 2, 2, 3, 1, 1, 2, 4]
def baseStart_443902 : Nat := 118140960795 + 443902 * 2 ^ 59
def prefixEnd_443902 : Nat := 4983230072969 + 3 ^ 40 * 443902 * 2
def baseEnd_443902 : Nat := 135072645625023683012467

theorem tailTrace_443902 : CollatzResearch.WordTrace tailWord_443902 prefixEnd_443902 135072645625023683012467 := by
  unfold tailWord_443902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023804504728292658871745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10793624025217560847315973 2023804504728292658871745)
  ·
    refine ⟨1517853378546219494153809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2023804504728292658871745 1517853378546219494153809)
    ·
      refine ⟨1138390033909664620615357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1517853378546219494153809 1138390033909664620615357)
      ·
        refine ⟨426896262716124232730759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1138390033909664620615357 426896262716124232730759)
        ·
          refine ⟨640344394074186349096139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426896262716124232730759 640344394074186349096139)
          ·
            refine ⟨960516591111279523644209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640344394074186349096139 960516591111279523644209)
            ·
              refine ⟨720387443333459642733157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960516591111279523644209 720387443333459642733157)
              ·
                refine ⟨135072645625023683012467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720387443333459642733157 135072645625023683012467)
                ·
                  rfl

theorem cell19_443902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_443902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443902 prefixEnd_443902 := by exact prefixLift 443902
  have htrace : WordTrace (prefixWord ++ tailWord_443902) baseStart_443902 baseEnd_443902 := by
    simpa [prefixWord, tailWord_443902, baseEnd_443902] using wordTrace_append hprefix tailTrace_443902
  have hstable : (prefixWord ++ tailWord_443902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443902).length < 2 ^ (prefixWord ++ tailWord_443902).sum := by decide
  have hdescent : baseEnd_443902 < baseStart_443902 := by decide
  rcases family_descends (prefixWord ++ tailWord_443902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443944 : List Nat := [2, 1, 5, 2, 2, 7]
def baseStart_443944 : Nat := 118140960795 + 443944 * 2 ^ 59
def prefixEnd_443944 : Nat := 4983230072969 + 3 ^ 40 * 443944 * 2
def baseEnd_443944 : Nat := 15009491731997781119891

theorem tailTrace_443944 : CollatzResearch.WordTrace tailWord_443944 prefixEnd_443944 15009491731997781119891 := by
  unfold tailWord_443944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8095983951837091222001443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10794645269116121629335257 8095983951837091222001443)
  ·
    refine ⟨12143975927755636833002165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8095983951837091222001443 12143975927755636833002165)
    ·
      refine ⟨1138497743227090953093953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12143975927755636833002165 1138497743227090953093953)
      ·
        refine ⟨853873307420318214820465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138497743227090953093953 853873307420318214820465)
        ·
          refine ⟨640404980565238661115349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853873307420318214820465 640404980565238661115349)
          ·
            refine ⟨15009491731997781119891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 640404980565238661115349 15009491731997781119891)
            ·
              rfl

theorem cell19_443944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 7].length) (baseStart_443944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_443944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_443944 prefixEnd_443944 := by exact prefixLift 443944
  have htrace : WordTrace (prefixWord ++ tailWord_443944) baseStart_443944 baseEnd_443944 := by
    simpa [prefixWord, tailWord_443944, baseEnd_443944] using wordTrace_append hprefix tailTrace_443944
  have hstable : (prefixWord ++ tailWord_443944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443944).length < 2 ^ (prefixWord ++ tailWord_443944).sum := by decide
  have hdescent : baseEnd_443944 < baseStart_443944 := by decide
  rcases family_descends (prefixWord ++ tailWord_443944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444003 : List Nat := [1, 1, 1, 5, 1, 4, 6]
def baseStart_444003 : Nat := 118140960795 + 444003 * 2 ^ 59
def prefixEnd_444003 : Nat := 4983230072969 + 3 ^ 40 * 444003 * 2
def baseEnd_444003 : Nat := 45034459464361791589249

theorem tailTrace_444003 : CollatzResearch.WordTrace tailWord_444003 prefixEnd_444003 45034459464361791589249 := by
  unfold tailWord_444003
  simp only [CollatzResearch.WordTrace]
  refine ⟨16194119810460435520400663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10796079873640290346933775 16194119810460435520400663)
  ·
    refine ⟨24291179715690653280600995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16194119810460435520400663 24291179715690653280600995)
    ·
      refine ⟨36436769573535979920901493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24291179715690653280600995 36436769573535979920901493)
      ·
        refine ⟨3415947147518998117584515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36436769573535979920901493 3415947147518998117584515)
        ·
          refine ⟨5123920721278497176376773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415947147518998117584515 5123920721278497176376773)
          ·
            refine ⟨960735135239718220570645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5123920721278497176376773 960735135239718220570645)
            ·
              refine ⟨45034459464361791589249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 960735135239718220570645 45034459464361791589249)
              ·
                rfl

theorem cell19_444003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_444003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444003 prefixEnd_444003 := by exact prefixLift 444003
  have htrace : WordTrace (prefixWord ++ tailWord_444003) baseStart_444003 baseEnd_444003 := by
    simpa [prefixWord, tailWord_444003, baseEnd_444003] using wordTrace_append hprefix tailTrace_444003
  have hstable : (prefixWord ++ tailWord_444003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444003).length < 2 ^ (prefixWord ++ tailWord_444003).sum := by decide
  have hdescent : baseEnd_444003 < baseStart_444003 := by decide
  rcases family_descends (prefixWord ++ tailWord_444003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444039 : List Nat := [1, 1, 4, 2, 1, 3, 4, 3]
def baseStart_444039 : Nat := 118140960795 + 444039 * 2 ^ 59
def prefixEnd_444039 : Nat := 4983230072969 + 3 ^ 40 * 444039 * 2
def baseEnd_444039 : Nat := 135114332647047957967649

theorem tailTrace_444039 : CollatzResearch.WordTrace tailWord_444039 prefixEnd_444039 135114332647047957967649 := by
  unfold tailWord_444039
  simp only [CollatzResearch.WordTrace]
  refine ⟨16195432838330013668711171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10796955225553342445807447 16195432838330013668711171)
  ·
    refine ⟨24293149257495020503066757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16195432838330013668711171 24293149257495020503066757)
    ·
      refine ⟨4554965485780316344325017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24293149257495020503066757 4554965485780316344325017)
      ·
        refine ⟨3416224114335237258243763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4554965485780316344325017 3416224114335237258243763)
        ·
          refine ⟨5124336171502855887365645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416224114335237258243763 5124336171502855887365645)
          ·
            refine ⟨1921626064313570957762117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5124336171502855887365645 1921626064313570957762117)
            ·
              refine ⟨360304887058794554580397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1921626064313570957762117 360304887058794554580397)
              ·
                refine ⟨135114332647047957967649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360304887058794554580397 135114332647047957967649)
                ·
                  rfl

theorem cell19_444039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_444039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444039 prefixEnd_444039 := by exact prefixLift 444039
  have htrace : WordTrace (prefixWord ++ tailWord_444039) baseStart_444039 baseEnd_444039 := by
    simpa [prefixWord, tailWord_444039, baseEnd_444039] using wordTrace_append hprefix tailTrace_444039
  have hstable : (prefixWord ++ tailWord_444039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444039).length < 2 ^ (prefixWord ++ tailWord_444039).sum := by decide
  have hdescent : baseEnd_444039 < baseStart_444039 := by decide
  rcases family_descends (prefixWord ++ tailWord_444039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444077 : List Nat := [1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_444077 : Nat := 118140960795 + 444077 * 2 ^ 59
def prefixEnd_444077 : Nat := 4983230072969 + 3 ^ 40 * 444077 * 2
def baseEnd_444077 : Nat := 135125895470675129123101

theorem tailTrace_444077 : CollatzResearch.WordTrace tailWord_444077 prefixEnd_444077 135125895470675129123101 := by
  unfold tailWord_444077
  simp only [CollatzResearch.WordTrace]
  refine ⟨16196818812192346158594485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10797879208128230772396323 16196818812192346158594485)
  ·
    refine ⟨1518451763643032452368233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16196818812192346158594485 1518451763643032452368233)
    ·
      refine ⟨1138838822732274339276175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1518451763643032452368233 1138838822732274339276175)
      ·
        refine ⟨1708258234098411508914263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138838822732274339276175 1708258234098411508914263)
        ·
          refine ⟨2562387351147617263371395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708258234098411508914263 2562387351147617263371395)
          ·
            refine ⟨3843581026721425895057093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562387351147617263371395 3843581026721425895057093)
            ·
              refine ⟨720671442510267355323205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3843581026721425895057093 720671442510267355323205)
              ·
                refine ⟨135125895470675129123101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720671442510267355323205 135125895470675129123101)
                ·
                  rfl

theorem cell19_444077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_444077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444077 prefixEnd_444077 := by exact prefixLift 444077
  have htrace : WordTrace (prefixWord ++ tailWord_444077) baseStart_444077 baseEnd_444077 := by
    simpa [prefixWord, tailWord_444077, baseEnd_444077] using wordTrace_append hprefix tailTrace_444077
  have hstable : (prefixWord ++ tailWord_444077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444077).length < 2 ^ (prefixWord ++ tailWord_444077).sum := by decide
  have hdescent : baseEnd_444077 < baseStart_444077 := by decide
  rcases family_descends (prefixWord ++ tailWord_444077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444079 : List Nat := [1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_444079 : Nat := 118140960795 + 444079 * 2 ^ 59
def prefixEnd_444079 : Nat := 4983230072969 + 3 ^ 40 * 444079 * 2
def baseEnd_444079 : Nat := 135126504040339717078651

theorem tailTrace_444079 : CollatzResearch.WordTrace tailWord_444079 prefixEnd_444079 135126504040339717078651 := by
  unfold tailWord_444079
  simp only [CollatzResearch.WordTrace]
  refine ⟨16196891758185100500167291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10797927838790067000111527 16196891758185100500167291)
  ·
    refine ⟨24295337637277650750250937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16196891758185100500167291 24295337637277650750250937)
    ·
      refine ⟨18221503227958238062688203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24295337637277650750250937 18221503227958238062688203)
      ·
        refine ⟨27332254841937357094032305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18221503227958238062688203 27332254841937357094032305)
        ·
          refine ⟨20499191131453017820524229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27332254841937357094032305 20499191131453017820524229)
          ·
            refine ⟨3843598337147440841348293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20499191131453017820524229 3843598337147440841348293)
            ·
              refine ⟨720674688215145157752805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3843598337147440841348293 720674688215145157752805)
              ·
                refine ⟨135126504040339717078651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720674688215145157752805 135126504040339717078651)
                ·
                  rfl

theorem cell19_444079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_444079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444079 prefixEnd_444079 := by exact prefixLift 444079
  have htrace : WordTrace (prefixWord ++ tailWord_444079) baseStart_444079 baseEnd_444079 := by
    simpa [prefixWord, tailWord_444079, baseEnd_444079] using wordTrace_append hprefix tailTrace_444079
  have hstable : (prefixWord ++ tailWord_444079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444079).length < 2 ^ (prefixWord ++ tailWord_444079).sum := by decide
  have hdescent : baseEnd_444079 < baseStart_444079 := by decide
  rcases family_descends (prefixWord ++ tailWord_444079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444206 : List Nat := [4, 1, 3, 2, 2, 2, 2, 3]
def baseStart_444206 : Nat := 118140960795 + 444206 * 2 ^ 59
def prefixEnd_444206 : Nat := 4983230072969 + 3 ^ 40 * 444206 * 2
def baseEnd_444206 : Nat := 135165148214041052256083

theorem tailTrace_444206 : CollatzResearch.WordTrace tailWord_444206 prefixEnd_444206 135165148214041052256083 := by
  unfold tailWord_444206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025190478590625148755059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10801015885816667460026981 2025190478590625148755059)
  ·
    refine ⟨3037785717885937723132589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2025190478590625148755059 3037785717885937723132589)
    ·
      refine ⟨1139169644207226646174721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3037785717885937723132589 1139169644207226646174721)
      ·
        refine ⟨854377233155419984631041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1139169644207226646174721 854377233155419984631041)
        ·
          refine ⟨640782924866564988473281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854377233155419984631041 640782924866564988473281)
          ·
            refine ⟨480587193649923741354961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640782924866564988473281 480587193649923741354961)
            ·
              refine ⟨360440395237442806016221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480587193649923741354961 360440395237442806016221)
              ·
                refine ⟨135165148214041052256083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360440395237442806016221 135165148214041052256083)
                ·
                  rfl

theorem cell19_444206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_444206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444206 prefixEnd_444206 := by exact prefixLift 444206
  have htrace : WordTrace (prefixWord ++ tailWord_444206) baseStart_444206 baseEnd_444206 := by
    simpa [prefixWord, tailWord_444206, baseEnd_444206] using wordTrace_append hprefix tailTrace_444206
  have hstable : (prefixWord ++ tailWord_444206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444206).length < 2 ^ (prefixWord ++ tailWord_444206).sum := by decide
  have hdescent : baseEnd_444206 < baseStart_444206 := by decide
  rcases family_descends (prefixWord ++ tailWord_444206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444210 : List Nat := [3, 2, 1, 1, 3, 2, 4, 3]
def baseStart_444210 : Nat := 118140960795 + 444210 * 2 ^ 59
def prefixEnd_444210 : Nat := 4983230072969 + 3 ^ 40 * 444210 * 2
def baseEnd_444210 : Nat := 135166365353370228167183

theorem tailTrace_444210 : CollatzResearch.WordTrace tailWord_444210 prefixEnd_444210 135166365353370228167183 := by
  unfold tailWord_444210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4050417430177627468296521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10801113147140339915457389 4050417430177627468296521)
  ·
    refine ⟨3037813072633220601222391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4050417430177627468296521 3037813072633220601222391)
    ·
      refine ⟨4556719608949830901833587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3037813072633220601222391 4556719608949830901833587)
      ·
        refine ⟨6835079413424746352750381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4556719608949830901833587 6835079413424746352750381)
        ·
          refine ⟨2563154780034279882281393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6835079413424746352750381 2563154780034279882281393)
          ·
            refine ⟨1922366085025709911711045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2563154780034279882281393 1922366085025709911711045)
            ·
              refine ⟨360443640942320608445821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1922366085025709911711045 360443640942320608445821)
              ·
                refine ⟨135166365353370228167183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360443640942320608445821 135166365353370228167183)
                ·
                  rfl

theorem cell19_444210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_444210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444210 prefixEnd_444210 := by exact prefixLift 444210
  have htrace : WordTrace (prefixWord ++ tailWord_444210) baseStart_444210 baseEnd_444210 := by
    simpa [prefixWord, tailWord_444210, baseEnd_444210] using wordTrace_append hprefix tailTrace_444210
  have hstable : (prefixWord ++ tailWord_444210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444210).length < 2 ^ (prefixWord ++ tailWord_444210).sum := by decide
  have hdescent : baseEnd_444210 < baseStart_444210 := by decide
  rcases family_descends (prefixWord ++ tailWord_444210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444250 : List Nat := [3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_444250 : Nat := 118140960795 + 444250 * 2 ^ 59
def prefixEnd_444250 : Nat := 4983230072969 + 3 ^ 40 * 444250 * 2
def baseEnd_444250 : Nat := 135178536746661987278185

theorem tailTrace_444250 : CollatzResearch.WordTrace tailWord_444250 prefixEnd_444250 135178536746661987278185 := by
  unfold tailWord_444250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4050782160141399176160551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10802085760377064469761469 4050782160141399176160551)
  ·
    refine ⟨6076173240212098764240827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4050782160141399176160551 6076173240212098764240827)
    ·
      refine ⟨9114259860318148146361241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076173240212098764240827 9114259860318148146361241)
      ·
        refine ⟨6835694895238611109770931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9114259860318148146361241 6835694895238611109770931)
        ·
          refine ⟨10253542342857916664656397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835694895238611109770931 10253542342857916664656397)
          ·
            refine ⟨3845078378571718749246149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10253542342857916664656397 3845078378571718749246149)
            ·
              refine ⟨720952195982197265483653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3845078378571718749246149 720952195982197265483653)
              ·
                refine ⟨135178536746661987278185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720952195982197265483653 135178536746661987278185)
                ·
                  rfl

theorem cell19_444250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_444250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444250 prefixEnd_444250 := by exact prefixLift 444250
  have htrace : WordTrace (prefixWord ++ tailWord_444250) baseStart_444250 baseEnd_444250 := by
    simpa [prefixWord, tailWord_444250, baseEnd_444250] using wordTrace_append hprefix tailTrace_444250
  have hstable : (prefixWord ++ tailWord_444250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444250).length < 2 ^ (prefixWord ++ tailWord_444250).sum := by decide
  have hdescent : baseEnd_444250 < baseStart_444250 := by decide
  rcases family_descends (prefixWord ++ tailWord_444250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444269 : List Nat := [1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_444269 : Nat := 118140960795 + 444269 * 2 ^ 59
def prefixEnd_444269 : Nat := 4983230072969 + 3 ^ 40 * 444269 * 2
def baseEnd_444269 : Nat := 135184318158475572855911

theorem tailTrace_444269 : CollatzResearch.WordTrace tailWord_444269 prefixEnd_444269 135184318158475572855911 := by
  unfold tailWord_444269
  simp only [CollatzResearch.WordTrace]
  refine ⟨16203821627496762949583861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10802547751664508633055907 16203821627496762949583861)
  ·
    refine ⟨1519108277577821526523487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16203821627496762949583861 1519108277577821526523487)
    ·
      refine ⟨2278662416366732289785231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1519108277577821526523487 2278662416366732289785231)
      ·
        refine ⟨3417993624550098434677847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2278662416366732289785231 3417993624550098434677847)
        ·
          refine ⟨5126990436825147652016771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417993624550098434677847 5126990436825147652016771)
          ·
            refine ⟨7690485655237721478025157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126990436825147652016771 7690485655237721478025157)
            ·
              refine ⟨1441966060357072777129717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7690485655237721478025157 1441966060357072777129717)
              ·
                refine ⟨135184318158475572855911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1441966060357072777129717 135184318158475572855911)
                ·
                  rfl

theorem cell19_444269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_444269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444269 prefixEnd_444269 := by exact prefixLift 444269
  have htrace : WordTrace (prefixWord ++ tailWord_444269) baseStart_444269 baseEnd_444269 := by
    simpa [prefixWord, tailWord_444269, baseEnd_444269] using wordTrace_append hprefix tailTrace_444269
  have hstable : (prefixWord ++ tailWord_444269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444269).length < 2 ^ (prefixWord ++ tailWord_444269).sum := by decide
  have hdescent : baseEnd_444269 < baseStart_444269 := by decide
  rcases family_descends (prefixWord ++ tailWord_444269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444286 : List Nat := [4, 2, 3, 1, 1, 8]
def baseStart_444286 : Nat := 118140960795 + 444286 * 2 ^ 59
def prefixEnd_444286 : Nat := 4983230072969 + 3 ^ 40 * 444286 * 2
def baseEnd_444286 : Nat := 15021054555624952275343

theorem tailTrace_444286 : CollatzResearch.WordTrace tailWord_444286 prefixEnd_444286 15021054555624952275343 := by
  unfold tailWord_444286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025555208554396856619089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10802961112290116568635141 2025555208554396856619089)
  ·
    refine ⟨1519166406415797642464317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2025555208554396856619089 1519166406415797642464317)
    ·
      refine ⟨569687402405924115924119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1519166406415797642464317 569687402405924115924119)
      ·
        refine ⟨854531103608886173886179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569687402405924115924119 854531103608886173886179)
        ·
          refine ⟨1281796655413329260829269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854531103608886173886179 1281796655413329260829269)
          ·
            refine ⟨15021054555624952275343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1281796655413329260829269 15021054555624952275343)
            ·
              rfl

theorem cell19_444286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 8].length) (baseStart_444286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444286 prefixEnd_444286 := by exact prefixLift 444286
  have htrace : WordTrace (prefixWord ++ tailWord_444286) baseStart_444286 baseEnd_444286 := by
    simpa [prefixWord, tailWord_444286, baseEnd_444286] using wordTrace_append hprefix tailTrace_444286
  have hstable : (prefixWord ++ tailWord_444286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444286).length < 2 ^ (prefixWord ++ tailWord_444286).sum := by decide
  have hdescent : baseEnd_444286 < baseStart_444286 := by decide
  rcases family_descends (prefixWord ++ tailWord_444286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444322 : List Nat := [3, 3, 1, 2, 3, 1, 3, 3]
def baseStart_444322 : Nat := 118140960795 + 444322 * 2 ^ 59
def prefixEnd_444322 : Nat := 4983230072969 + 3 ^ 40 * 444322 * 2
def baseEnd_444322 : Nat := 135200445254587153677989

theorem tailTrace_444322 : CollatzResearch.WordTrace tailWord_444322 prefixEnd_444322 135200445254587153677989 := by
  unfold tailWord_444322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051438674076188250315805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10803836464203168667508813 4051438674076188250315805)
  ·
    refine ⟨1519289502778570593868427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4051438674076188250315805 1519289502778570593868427)
    ·
      refine ⟨2278934254167855890802641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1519289502778570593868427 2278934254167855890802641)
      ·
        refine ⟨1709200690625891918101981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2278934254167855890802641 1709200690625891918101981)
        ·
          refine ⟨640950258984709469288243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1709200690625891918101981 640950258984709469288243)
          ·
            refine ⟨961425388477064203932365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640950258984709469288243 961425388477064203932365)
            ·
              refine ⟨360534520678899076474637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 961425388477064203932365 360534520678899076474637)
              ·
                refine ⟨135200445254587153677989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360534520678899076474637 135200445254587153677989)
                ·
                  rfl

theorem cell19_444322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_444322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444322 prefixEnd_444322 := by exact prefixLift 444322
  have htrace : WordTrace (prefixWord ++ tailWord_444322) baseStart_444322 baseEnd_444322 := by
    simpa [prefixWord, tailWord_444322, baseEnd_444322] using wordTrace_append hprefix tailTrace_444322
  have hstable : (prefixWord ++ tailWord_444322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444322).length < 2 ^ (prefixWord ++ tailWord_444322).sum := by decide
  have hdescent : baseEnd_444322 < baseStart_444322 := by decide
  rcases family_descends (prefixWord ++ tailWord_444322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444324 : List Nat := [2, 3, 1, 2, 1, 4, 3, 3]
def baseStart_444324 : Nat := 118140960795 + 444324 * 2 ^ 59
def prefixEnd_444324 : Nat := 4983230072969 + 3 ^ 40 * 444324 * 2
def baseEnd_444324 : Nat := 135201053824251741633539

theorem tailTrace_444324 : CollatzResearch.WordTrace tailWord_444324 prefixEnd_444324 135201053824251741633539 := by
  unfold tailWord_444324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8102913821148753671418013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10803885094865004895224017 8102913821148753671418013)
  ·
    refine ⟨3038592682930782626781755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8102913821148753671418013 3038592682930782626781755)
    ·
      refine ⟨4557889024396173940172633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038592682930782626781755 4557889024396173940172633)
      ·
        refine ⟨3418416768297130455129475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4557889024396173940172633 3418416768297130455129475)
        ·
          refine ⟨5127625152445695682694213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418416768297130455129475 5127625152445695682694213)
          ·
            refine ⟨961429716083567940505165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5127625152445695682694213 961429716083567940505165)
            ·
              refine ⟨360536143531337977689437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 961429716083567940505165 360536143531337977689437)
              ·
                refine ⟨135201053824251741633539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360536143531337977689437 135201053824251741633539)
                ·
                  rfl

theorem cell19_444324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_444324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444324 prefixEnd_444324 := by exact prefixLift 444324
  have htrace : WordTrace (prefixWord ++ tailWord_444324) baseStart_444324 baseEnd_444324 := by
    simpa [prefixWord, tailWord_444324, baseEnd_444324] using wordTrace_append hprefix tailTrace_444324
  have hstable : (prefixWord ++ tailWord_444324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444324).length < 2 ^ (prefixWord ++ tailWord_444324).sum := by decide
  have hdescent : baseEnd_444324 < baseStart_444324 := by decide
  rcases family_descends (prefixWord ++ tailWord_444324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444381 : List Nat := [1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_444381 : Nat := 118140960795 + 444381 * 2 ^ 59
def prefixEnd_444381 : Nat := 4983230072969 + 3 ^ 40 * 444381 * 2
def baseEnd_444381 : Nat := 135218398059692498366717

theorem tailTrace_444381 : CollatzResearch.WordTrace tailWord_444381 prefixEnd_444381 135218398059692498366717 := by
  unfold tailWord_444381
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207906603091006077660997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10805271068727337385107331 16207906603091006077660997)
  ·
    refine ⟨3038982488079563639561437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16207906603091006077660997 3038982488079563639561437)
    ·
      refine ⟨1139618433029836364835539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3038982488079563639561437 1139618433029836364835539)
      ·
        refine ⟨1709427649544754547253309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139618433029836364835539 1709427649544754547253309)
        ·
          refine ⟨641035368579282955219991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1709427649544754547253309 641035368579282955219991)
          ·
            refine ⟨961553052868924432829987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641035368579282955219991 961553052868924432829987)
            ·
              refine ⟨1442329579303386649244981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961553052868924432829987 1442329579303386649244981)
              ·
                refine ⟨135218398059692498366717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1442329579303386649244981 135218398059692498366717)
                ·
                  rfl

theorem cell19_444381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_444381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444381 prefixEnd_444381 := by exact prefixLift 444381
  have htrace : WordTrace (prefixWord ++ tailWord_444381) baseStart_444381 baseEnd_444381 := by
    simpa [prefixWord, tailWord_444381, baseEnd_444381] using wordTrace_append hprefix tailTrace_444381
  have hstable : (prefixWord ++ tailWord_444381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444381).length < 2 ^ (prefixWord ++ tailWord_444381).sum := by decide
  have hdescent : baseEnd_444381 < baseStart_444381 := by decide
  rcases family_descends (prefixWord ++ tailWord_444381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444383 : List Nat := [1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_444383 : Nat := 118140960795 + 444383 * 2 ^ 59
def prefixEnd_444383 : Nat := 4983230072969 + 3 ^ 40 * 444383 * 2
def baseEnd_444383 : Nat := 135219006629357086322267

theorem tailTrace_444383 : CollatzResearch.WordTrace tailWord_444383 prefixEnd_444383 135219006629357086322267 := by
  unfold tailWord_444383
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207979549083760419233803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10805319699389173612822535 16207979549083760419233803)
  ·
    refine ⟨24311969323625640628850705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16207979549083760419233803 24311969323625640628850705)
    ·
      refine ⟨18233976992719230471638029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24311969323625640628850705 18233976992719230471638029)
      ·
        refine ⟨6837741372269711426864261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18233976992719230471638029 6837741372269711426864261)
        ·
          refine ⟨1282076507300570892537049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6837741372269711426864261 1282076507300570892537049)
          ·
            refine ⟨961557380475428169402787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282076507300570892537049 961557380475428169402787)
            ·
              refine ⟨1442336070713142254104181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961557380475428169402787 1442336070713142254104181)
              ·
                refine ⟨135219006629357086322267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1442336070713142254104181 135219006629357086322267)
                ·
                  rfl

theorem cell19_444383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_444383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444383 prefixEnd_444383 := by exact prefixLift 444383
  have htrace : WordTrace (prefixWord ++ tailWord_444383) baseStart_444383 baseEnd_444383 := by
    simpa [prefixWord, tailWord_444383, baseEnd_444383] using wordTrace_append hprefix tailTrace_444383
  have hstable : (prefixWord ++ tailWord_444383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444383).length < 2 ^ (prefixWord ++ tailWord_444383).sum := by decide
  have hdescent : baseEnd_444383 < baseStart_444383 := by decide
  rcases family_descends (prefixWord ++ tailWord_444383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444421 : List Nat := [1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_444421 : Nat := 118140960795 + 444421 * 2 ^ 59
def prefixEnd_444421 : Nat := 4983230072969 + 3 ^ 40 * 444421 * 2
def baseEnd_444421 : Nat := 135230569452984257477719

theorem tailTrace_444421 : CollatzResearch.WordTrace tailWord_444421 prefixEnd_444421 135230569452984257477719 := by
  unfold tailWord_444421
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209365522946092909117117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10806243681964061939411411 16209365522946092909117117)
  ·
    refine ⟨6078512071104784840918919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16209365522946092909117117 6078512071104784840918919)
    ·
      refine ⟨9117768106657177261378379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6078512071104784840918919 9117768106657177261378379)
      ·
        refine ⟨13676652159985765892067569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9117768106657177261378379 13676652159985765892067569)
        ·
          refine ⟨10257489119989324419050677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13676652159985765892067569 10257489119989324419050677)
          ·
            refine ⟨961639604998999164286001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10257489119989324419050677 961639604998999164286001)
            ·
              refine ⟨721229703749249373214501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961639604998999164286001 721229703749249373214501)
              ·
                refine ⟨135230569452984257477719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 721229703749249373214501 135230569452984257477719)
                ·
                  rfl

theorem cell19_444421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_444421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444421 prefixEnd_444421 := by exact prefixLift 444421
  have htrace : WordTrace (prefixWord ++ tailWord_444421) baseStart_444421 baseEnd_444421 := by
    simpa [prefixWord, tailWord_444421, baseEnd_444421] using wordTrace_append hprefix tailTrace_444421
  have hstable : (prefixWord ++ tailWord_444421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444421).length < 2 ^ (prefixWord ++ tailWord_444421).sum := by decide
  have hdescent : baseEnd_444421 < baseStart_444421 := by decide
  rcases family_descends (prefixWord ++ tailWord_444421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444461 : List Nat := [1, 5, 13]
def baseStart_444461 : Nat := 118140960795 + 444461 * 2 ^ 59
def prefixEnd_444461 : Nat := 4983230072969 + 3 ^ 40 * 444461 * 2
def baseEnd_444461 : Nat := 556554489079325171147

theorem tailTrace_444461 : CollatzResearch.WordTrace tailWord_444461 prefixEnd_444461 556554489079325171147 := by
  unfold tailWord_444461
  simp only [CollatzResearch.WordTrace]
  refine ⟨16210824442801179740573237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10807216295200786493715491 16210824442801179740573237)
  ·
    refine ⟨1519764791512610600678741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16210824442801179740573237 1519764791512610600678741)
    ·
      refine ⟨556554489079325171147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 1519764791512610600678741 556554489079325171147)
      ·
        rfl

theorem cell19_444461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 13].length) (baseStart_444461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444461 prefixEnd_444461 := by exact prefixLift 444461
  have htrace : WordTrace (prefixWord ++ tailWord_444461) baseStart_444461 baseEnd_444461 := by
    simpa [prefixWord, tailWord_444461, baseEnd_444461] using wordTrace_append hprefix tailTrace_444461
  have hstable : (prefixWord ++ tailWord_444461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444461).length < 2 ^ (prefixWord ++ tailWord_444461).sum := by decide
  have hdescent : baseEnd_444461 < baseStart_444461 := by decide
  rcases family_descends (prefixWord ++ tailWord_444461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444514 : List Nat := [3, 3, 2, 2, 2, 1, 6]
def baseStart_444514 : Nat := 118140960795 + 444514 * 2 ^ 59
def prefixEnd_444514 : Nat := 4983230072969 + 3 ^ 40 * 444514 * 2
def baseEnd_444514 : Nat := 45086289314129199136933

theorem tailTrace_444514 : CollatzResearch.WordTrace tailWord_444514 prefixEnd_444514 45086289314129199136933 := by
  unfold tailWord_444514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053189377902292448063149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10808505007739446528168397 4053189377902292448063149)
  ·
    refine ⟨1519946016713359668023681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4053189377902292448063149 1519946016713359668023681)
    ·
      refine ⟨1139959512535019751017761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1519946016713359668023681 1139959512535019751017761)
      ·
        refine ⟨854969634401264813263321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1139959512535019751017761 854969634401264813263321)
        ·
          refine ⟨641227225800948609947491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854969634401264813263321 641227225800948609947491)
          ·
            refine ⟨961840838701422914921237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641227225800948609947491 961840838701422914921237)
            ·
              refine ⟨45086289314129199136933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 961840838701422914921237 45086289314129199136933)
              ·
                rfl

theorem cell19_444514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_444514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444514 prefixEnd_444514 := by exact prefixLift 444514
  have htrace : WordTrace (prefixWord ++ tailWord_444514) baseStart_444514 baseEnd_444514 := by
    simpa [prefixWord, tailWord_444514, baseEnd_444514] using wordTrace_append hprefix tailTrace_444514
  have hstable : (prefixWord ++ tailWord_444514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444514).length < 2 ^ (prefixWord ++ tailWord_444514).sum := by decide
  have hdescent : baseEnd_444514 < baseStart_444514 := by decide
  rcases family_descends (prefixWord ++ tailWord_444514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444552 : List Nat := [2, 1, 3, 4, 1, 1, 4, 3]
def baseStart_444552 : Nat := 118140960795 + 444552 * 2 ^ 59
def prefixEnd_444552 : Nat := 4983230072969 + 3 ^ 40 * 444552 * 2
def baseEnd_444552 : Nat := 135270430766014768566251

theorem tailTrace_444552 : CollatzResearch.WordTrace tailWord_444552 prefixEnd_444552 135270430766014768566251 := by
  unfold tailWord_444552
  simp only [CollatzResearch.WordTrace]
  refine ⟨8107071742735751141067955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10809428990314334854757273 8107071742735751141067955)
  ·
    refine ⟨12160607614103626711601933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8107071742735751141067955 12160607614103626711601933)
    ·
      refine ⟨4560227855288860016850725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12160607614103626711601933 4560227855288860016850725)
      ·
        refine ⟨855042722866661253159511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4560227855288860016850725 855042722866661253159511)
        ·
          refine ⟨1282564084299991879739267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855042722866661253159511 1282564084299991879739267)
          ·
            refine ⟨1923846126449987819608901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282564084299991879739267 1923846126449987819608901)
            ·
              refine ⟨360721148709372716176669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1923846126449987819608901 360721148709372716176669)
              ·
                refine ⟨135270430766014768566251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360721148709372716176669 135270430766014768566251)
                ·
                  rfl

theorem cell19_444552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_444552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444552 prefixEnd_444552 := by exact prefixLift 444552
  have htrace : WordTrace (prefixWord ++ tailWord_444552) baseStart_444552 baseEnd_444552 := by
    simpa [prefixWord, tailWord_444552, baseEnd_444552] using wordTrace_append hprefix tailTrace_444552
  have hstable : (prefixWord ++ tailWord_444552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444552).length < 2 ^ (prefixWord ++ tailWord_444552).sum := by decide
  have hdescent : baseEnd_444552 < baseStart_444552 := by decide
  rcases family_descends (prefixWord ++ tailWord_444552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444554 : List Nat := [3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_444554 : Nat := 118140960795 + 444554 * 2 ^ 59
def prefixEnd_444554 : Nat := 4983230072969 + 3 ^ 40 * 444554 * 2
def baseEnd_444554 : Nat := 135271039335679356521801

theorem tailTrace_444554 : CollatzResearch.WordTrace tailWord_444554 prefixEnd_444554 135271039335679356521801 := by
  unfold tailWord_444554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053554107866064155927179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10809477620976171082472477 4053554107866064155927179)
  ·
    refine ⟨6080331161799096233890769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4053554107866064155927179 6080331161799096233890769)
    ·
      refine ⟨4560248371349322175418077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6080331161799096233890769 4560248371349322175418077)
      ·
        refine ⟨1710093139255995815781779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4560248371349322175418077 1710093139255995815781779)
        ·
          refine ⟨2565139708883993723672669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710093139255995815781779 2565139708883993723672669)
          ·
            refine ⟨961927390831497646377251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2565139708883993723672669 961927390831497646377251)
            ·
              refine ⟨1442891086247246469565877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961927390831497646377251 1442891086247246469565877)
              ·
                refine ⟨135271039335679356521801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1442891086247246469565877 135271039335679356521801)
                ·
                  rfl

theorem cell19_444554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_444554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444554 prefixEnd_444554 := by exact prefixLift 444554
  have htrace : WordTrace (prefixWord ++ tailWord_444554) baseStart_444554 baseEnd_444554 := by
    simpa [prefixWord, tailWord_444554, baseEnd_444554] using wordTrace_append hprefix tailTrace_444554
  have hstable : (prefixWord ++ tailWord_444554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444554).length < 2 ^ (prefixWord ++ tailWord_444554).sum := by decide
  have hdescent : baseEnd_444554 < baseStart_444554 := by decide
  rcases family_descends (prefixWord ++ tailWord_444554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444573 : List Nat := [1, 4, 2, 1, 1, 5, 5]
def baseStart_444573 : Nat := 118140960795 + 444573 * 2 ^ 59
def prefixEnd_444573 : Nat := 4983230072969 + 3 ^ 40 * 444573 * 2
def baseEnd_444573 : Nat := 45092273582497647366509

theorem tailTrace_444573 : CollatzResearch.WordTrace tailWord_444573 prefixEnd_444573 45092273582497647366509 := by
  unfold tailWord_444573
  simp only [CollatzResearch.WordTrace]
  refine ⟨16214909418395422868650373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10809939612263615245766915 16214909418395422868650373)
  ·
    refine ⟨3040295515949141787871945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16214909418395422868650373 3040295515949141787871945)
    ·
      refine ⟨2280221636961856340903959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3040295515949141787871945 2280221636961856340903959)
      ·
        refine ⟨3420332455442784511355939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280221636961856340903959 3420332455442784511355939)
        ·
          refine ⟨5130498683164176767033909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420332455442784511355939 5130498683164176767033909)
          ·
            refine ⟨480984251546641571909429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5130498683164176767033909 480984251546641571909429)
            ·
              refine ⟨45092273582497647366509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 480984251546641571909429 45092273582497647366509)
              ·
                rfl

theorem cell19_444573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_444573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444573 prefixEnd_444573 := by exact prefixLift 444573
  have htrace : WordTrace (prefixWord ++ tailWord_444573) baseStart_444573 baseEnd_444573 := by
    simpa [prefixWord, tailWord_444573, baseEnd_444573] using wordTrace_append hprefix tailTrace_444573
  have hstable : (prefixWord ++ tailWord_444573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444573).length < 2 ^ (prefixWord ++ tailWord_444573).sum := by decide
  have hdescent : baseEnd_444573 < baseStart_444573 := by decide
  rcases family_descends (prefixWord ++ tailWord_444573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444613 : List Nat := [1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_444613 : Nat := 118140960795 + 444613 * 2 ^ 59
def prefixEnd_444613 : Nat := 4983230072969 + 3 ^ 40 * 444613 * 2
def baseEnd_444613 : Nat := 135288992140784701210529

theorem tailTrace_444613 : CollatzResearch.WordTrace tailWord_444613 prefixEnd_444613 135288992140784701210529 := by
  unfold tailWord_444613
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216368338250509700106493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10810912225500339800070995 16216368338250509700106493)
  ·
    refine ⟨6081138126843941137539935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16216368338250509700106493 6081138126843941137539935)
    ·
      refine ⟨9121707190265911706309903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6081138126843941137539935 9121707190265911706309903)
      ·
        refine ⟨13682560785398867559464855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9121707190265911706309903 13682560785398867559464855)
        ·
          refine ⟨20523841178098301339197283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13682560785398867559464855 20523841178098301339197283)
          ·
            refine ⟨30785761767147452008795925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20523841178098301339197283 30785761767147452008795925)
            ·
              refine ⟨1443082582835036812912309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30785761767147452008795925 1443082582835036812912309)
              ·
                refine ⟨135288992140784701210529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443082582835036812912309 135288992140784701210529)
                ·
                  rfl

theorem cell19_444613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_444613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444613 prefixEnd_444613 := by exact prefixLift 444613
  have htrace : WordTrace (prefixWord ++ tailWord_444613) baseStart_444613 baseEnd_444613 := by
    simpa [prefixWord, tailWord_444613, baseEnd_444613] using wordTrace_append hprefix tailTrace_444613
  have hstable : (prefixWord ++ tailWord_444613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444613).length < 2 ^ (prefixWord ++ tailWord_444613).sum := by decide
  have hdescent : baseEnd_444613 < baseStart_444613 := by decide
  rcases family_descends (prefixWord ++ tailWord_444613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444632 : List Nat := [2, 1, 2, 2, 4, 8]
def baseStart_444632 : Nat := 118140960795 + 444632 * 2 ^ 59
def prefixEnd_444632 : Nat := 4983230072969 + 3 ^ 40 * 444632 * 2
def baseEnd_444632 : Nat := 15032752616955365198695

theorem tailTrace_444632 : CollatzResearch.WordTrace tailWord_444632 prefixEnd_444632 15032752616955365198695 := by
  unfold tailWord_444632
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108530662590837972524075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10811374216787783963365433 8108530662590837972524075)
  ·
    refine ⟨12162795993886256958786113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8108530662590837972524075 12162795993886256958786113)
    ·
      refine ⟨9122096995414692719089585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12162795993886256958786113 9122096995414692719089585)
      ·
        refine ⟨6841572746561019539317189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9122096995414692719089585 6841572746561019539317189)
        ·
          refine ⟨1282794889980191163621973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6841572746561019539317189 1282794889980191163621973)
          ·
            refine ⟨15032752616955365198695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1282794889980191163621973 15032752616955365198695)
            ·
              rfl

theorem cell19_444632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 8].length) (baseStart_444632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444632 prefixEnd_444632 := by exact prefixLift 444632
  have htrace : WordTrace (prefixWord ++ tailWord_444632) baseStart_444632 baseEnd_444632 := by
    simpa [prefixWord, tailWord_444632, baseEnd_444632] using wordTrace_append hprefix tailTrace_444632
  have hstable : (prefixWord ++ tailWord_444632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444632).length < 2 ^ (prefixWord ++ tailWord_444632).sum := by decide
  have hdescent : baseEnd_444632 < baseStart_444632 := by decide
  rcases family_descends (prefixWord ++ tailWord_444632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444647 : List Nat := [1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_444647 : Nat := 118140960795 + 444647 * 2 ^ 59
def prefixEnd_444647 : Nat := 4983230072969 + 3 ^ 40 * 444647 * 2
def baseEnd_444647 : Nat := 135299337825082696454881

theorem tailTrace_444647 : CollatzResearch.WordTrace tailWord_444647 prefixEnd_444647 135299337825082696454881 := by
  unfold tailWord_444647
  simp only [CollatzResearch.WordTrace]
  refine ⟨16217608420127333506844195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10811738946751555671229463 16217608420127333506844195)
  ·
    refine ⟨24326412630191000260266293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16217608420127333506844195 24326412630191000260266293)
    ·
      refine ⟨2280601184080406274399965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24326412630191000260266293 2280601184080406274399965)
      ·
        refine ⟨855225444030152352899987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2280601184080406274399965 855225444030152352899987)
        ·
          refine ⟨1282838166045228529349981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855225444030152352899987 1282838166045228529349981)
          ·
            refine ⟨481064312266960698506243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1282838166045228529349981 481064312266960698506243)
            ·
              refine ⟨721596468400441047759365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481064312266960698506243 721596468400441047759365)
              ·
                refine ⟨135299337825082696454881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 721596468400441047759365 135299337825082696454881)
                ·
                  rfl

theorem cell19_444647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_444647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444647 prefixEnd_444647 := by exact prefixLift 444647
  have htrace : WordTrace (prefixWord ++ tailWord_444647) baseStart_444647 baseEnd_444647 := by
    simpa [prefixWord, tailWord_444647, baseEnd_444647] using wordTrace_append hprefix tailTrace_444647
  have hstable : (prefixWord ++ tailWord_444647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444647).length < 2 ^ (prefixWord ++ tailWord_444647).sum := by decide
  have hdescent : baseEnd_444647 < baseStart_444647 := by decide
  rcases family_descends (prefixWord ++ tailWord_444647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444689 : List Nat := [1, 2, 2, 1, 1, 6, 6]
def baseStart_444689 : Nat := 118140960795 + 444689 * 2 ^ 59
def prefixEnd_444689 : Nat := 4983230072969 + 3 ^ 40 * 444689 * 2
def baseEnd_444689 : Nat := 45104039262679681173811

theorem tailTrace_444689 : CollatzResearch.WordTrace tailWord_444689 prefixEnd_444689 45104039262679681173811 := by
  unfold tailWord_444689
  simp only [CollatzResearch.WordTrace]
  refine ⟨16219140285975174679873121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10812760190650116453248747 16219140285975174679873121)
  ·
    refine ⟨12164355214481381009904841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16219140285975174679873121 12164355214481381009904841)
    ·
      refine ⟨9123266410861035757428631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12164355214481381009904841 9123266410861035757428631)
      ·
        refine ⟨13684899616291553636142947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9123266410861035757428631 13684899616291553636142947)
        ·
          refine ⟨20527349424437330454214421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13684899616291553636142947 20527349424437330454214421)
          ·
            refine ⟨962219504270499865041301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20527349424437330454214421 962219504270499865041301)
            ·
              refine ⟨45104039262679681173811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 962219504270499865041301 45104039262679681173811)
              ·
                rfl

theorem cell19_444689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_444689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444689 prefixEnd_444689 := by exact prefixLift 444689
  have htrace : WordTrace (prefixWord ++ tailWord_444689) baseStart_444689 baseEnd_444689 := by
    simpa [prefixWord, tailWord_444689, baseEnd_444689] using wordTrace_append hprefix tailTrace_444689
  have hstable : (prefixWord ++ tailWord_444689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444689).length < 2 ^ (prefixWord ++ tailWord_444689).sum := by decide
  have hdescent : baseEnd_444689 < baseStart_444689 := by decide
  rcases family_descends (prefixWord ++ tailWord_444689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444721 : List Nat := [1, 2, 2, 3, 5, 1, 2, 3]
def baseStart_444721 : Nat := 118140960795 + 444721 * 2 ^ 59
def prefixEnd_444721 : Nat := 4983230072969 + 3 ^ 40 * 444721 * 2
def baseEnd_444721 : Nat := 135321854902672450810235

theorem tailTrace_444721 : CollatzResearch.WordTrace tailWord_444721 prefixEnd_444721 135321854902672450810235 := by
  unfold tailWord_444721
  simp only [CollatzResearch.WordTrace]
  refine ⟨16220307421859244145038017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10813538281239496096692011 16220307421859244145038017)
  ·
    refine ⟨12165230566394433108778513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16220307421859244145038017 12165230566394433108778513)
    ·
      refine ⟨9123922924795824831583885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12165230566394433108778513 9123922924795824831583885)
      ·
        refine ⟨3421471096798434311843957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9123922924795824831583885 3421471096798434311843957)
        ·
          refine ⟨320762915324853216735371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3421471096798434311843957 320762915324853216735371)
          ·
            refine ⟨481144372987279825103057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320762915324853216735371 481144372987279825103057)
            ·
              refine ⟨360858279740459868827293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481144372987279825103057 360858279740459868827293)
              ·
                refine ⟨135321854902672450810235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360858279740459868827293 135321854902672450810235)
                ·
                  rfl

theorem cell19_444721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 3].length) (baseStart_444721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444721 prefixEnd_444721 := by exact prefixLift 444721
  have htrace : WordTrace (prefixWord ++ tailWord_444721) baseStart_444721 baseEnd_444721 := by
    simpa [prefixWord, tailWord_444721, baseEnd_444721] using wordTrace_append hprefix tailTrace_444721
  have hstable : (prefixWord ++ tailWord_444721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444721).length < 2 ^ (prefixWord ++ tailWord_444721).sum := by decide
  have hdescent : baseEnd_444721 < baseStart_444721 := by decide
  rcases family_descends (prefixWord ++ tailWord_444721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444740 : List Nat := [2, 3, 4, 1, 3, 1, 5]
def baseStart_444740 : Nat := 118140960795 + 444740 * 2 ^ 59
def prefixEnd_444740 : Nat := 4983230072969 + 3 ^ 40 * 444740 * 2
def baseEnd_444740 : Nat := 45109212104828678795987

theorem tailTrace_444740 : CollatzResearch.WordTrace tailWord_444740 prefixEnd_444740 45109212104828678795987 := by
  unfold tailWord_444740
  simp only [CollatzResearch.WordTrace]
  refine ⟨8110500204395205194989837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10814000272526940259986449 8110500204395205194989837)
  ·
    refine ⟨3041437576648201948121189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8110500204395205194989837 3041437576648201948121189)
    ·
      refine ⟨570269545621537865272723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3041437576648201948121189 570269545621537865272723)
      ·
        refine ⟨855404318432306797909085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570269545621537865272723 855404318432306797909085)
        ·
          refine ⟨320776619412115049215907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 855404318432306797909085 320776619412115049215907)
          ·
            refine ⟨481164929118172573823861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320776619412115049215907 481164929118172573823861)
            ·
              refine ⟨45109212104828678795987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 481164929118172573823861 45109212104828678795987)
              ·
                rfl

theorem cell19_444740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_444740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444740 prefixEnd_444740 := by exact prefixLift 444740
  have htrace : WordTrace (prefixWord ++ tailWord_444740) baseStart_444740 baseEnd_444740 := by
    simpa [prefixWord, tailWord_444740, baseEnd_444740] using wordTrace_append hprefix tailTrace_444740
  have hstable : (prefixWord ++ tailWord_444740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444740).length < 2 ^ (prefixWord ++ tailWord_444740).sum := by decide
  have hdescent : baseEnd_444740 < baseStart_444740 := by decide
  rcases family_descends (prefixWord ++ tailWord_444740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444784 : List Nat := [2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_444784 : Nat := 118140960795 + 444784 * 2 ^ 59
def prefixEnd_444784 : Nat := 4983230072969 + 3 ^ 40 * 444784 * 2
def baseEnd_444784 : Nat := 135341024847106971410063

theorem tailTrace_444784 : CollatzResearch.WordTrace tailWord_444784 prefixEnd_444784 135341024847106971410063 := by
  unfold tailWord_444784
  simp only [CollatzResearch.WordTrace]
  refine ⟨8111302610315502952290703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10815070147087337269720937 8111302610315502952290703)
  ·
    refine ⟨12166953915473254428436055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8111302610315502952290703 12166953915473254428436055)
    ·
      refine ⟨18250430873209881642654083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12166953915473254428436055 18250430873209881642654083)
      ·
        refine ⟨27375646309814822463981125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18250430873209881642654083 27375646309814822463981125)
        ·
          refine ⟨5132933683090279211996461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27375646309814822463981125 5132933683090279211996461)
          ·
            refine ⟨1924850131158854704498673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5132933683090279211996461 1924850131158854704498673)
            ·
              refine ⟨1443637598369141028374005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924850131158854704498673 1443637598369141028374005)
              ·
                refine ⟨135341024847106971410063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443637598369141028374005 135341024847106971410063)
                ·
                  rfl

theorem cell19_444784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_444784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444784 prefixEnd_444784 := by exact prefixLift 444784
  have htrace : WordTrace (prefixWord ++ tailWord_444784) baseStart_444784 baseEnd_444784 := by
    simpa [prefixWord, tailWord_444784, baseEnd_444784] using wordTrace_append hprefix tailTrace_444784
  have hstable : (prefixWord ++ tailWord_444784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444784).length < 2 ^ (prefixWord ++ tailWord_444784).sum := by decide
  have hdescent : baseEnd_444784 < baseStart_444784 := by decide
  rcases family_descends (prefixWord ++ tailWord_444784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444803 : List Nat := [1, 1, 1, 3, 6, 7]
def baseStart_444803 : Nat := 118140960795 + 444803 * 2 ^ 59
def prefixEnd_444803 : Nat := 4983230072969 + 3 ^ 40 * 444803 * 2
def baseEnd_444803 : Nat := 15038534028768950776421

theorem tailTrace_444803 : CollatzResearch.WordTrace tailWord_444803 prefixEnd_444803 15038534028768950776421 := by
  unfold tailWord_444803
  simp only [CollatzResearch.WordTrace]
  refine ⟨16223298207562172149523063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10815532138374781433015375 16223298207562172149523063)
  ·
    refine ⟨24334947311343258224284595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16223298207562172149523063 24334947311343258224284595)
    ·
      refine ⟨36502420967014887336426893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24334947311343258224284595 36502420967014887336426893)
      ·
        refine ⟨13688407862630582751160085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36502420967014887336426893 13688407862630582751160085)
        ·
          refine ⟨641644118560808566460629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13688407862630582751160085 641644118560808566460629)
          ·
            refine ⟨15038534028768950776421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 641644118560808566460629 15038534028768950776421)
            ·
              rfl

theorem cell19_444803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 7].length) (baseStart_444803 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444803 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444803 prefixEnd_444803 := by exact prefixLift 444803
  have htrace : WordTrace (prefixWord ++ tailWord_444803) baseStart_444803 baseEnd_444803 := by
    simpa [prefixWord, tailWord_444803, baseEnd_444803] using wordTrace_append hprefix tailTrace_444803
  have hstable : (prefixWord ++ tailWord_444803).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444803).length < 2 ^ (prefixWord ++ tailWord_444803).sum := by decide
  have hdescent : baseEnd_444803 < baseStart_444803 := by decide
  rcases family_descends (prefixWord ++ tailWord_444803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444974 : List Nat := [4, 1, 3, 1, 10]
def baseStart_444974 : Nat := 118140960795 + 444974 * 2 ^ 59
def prefixEnd_444974 : Nat := 4983230072969 + 3 ^ 40 * 444974 * 2
def baseEnd_444974 : Nat := 5014771813527512118049

theorem tailTrace_444974 : CollatzResearch.WordTrace tailWord_444974 prefixEnd_444974 5014771813527512118049 := by
  unfold tailWord_444974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028691886242833544249747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10819690059961778902665317 2028691886242833544249747)
  ·
    refine ⟨3043037829364250316374621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2028691886242833544249747 3043037829364250316374621)
    ·
      refine ⟨1141139186011593868640483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3043037829364250316374621 1141139186011593868640483)
      ·
        refine ⟨1711708779017390802960725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141139186011593868640483 1711708779017390802960725)
        ·
          refine ⟨5014771813527512118049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1711708779017390802960725 5014771813527512118049)
          ·
            rfl

theorem cell19_444974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 10].length) (baseStart_444974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_444974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_444974 prefixEnd_444974 := by exact prefixLift 444974
  have htrace : WordTrace (prefixWord ++ tailWord_444974) baseStart_444974 baseEnd_444974 := by
    simpa [prefixWord, tailWord_444974, baseEnd_444974] using wordTrace_append hprefix tailTrace_444974
  have hstable : (prefixWord ++ tailWord_444974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444974).length < 2 ^ (prefixWord ++ tailWord_444974).sum := by decide
  have hdescent : baseEnd_444974 < baseStart_444974 := by decide
  rcases family_descends (prefixWord ++ tailWord_444974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445010 : List Nat := [3, 2, 2, 1, 2, 1, 5, 3]
def baseStart_445010 : Nat := 118140960795 + 445010 * 2 ^ 59
def prefixEnd_445010 : Nat := 4983230072969 + 3 ^ 40 * 445010 * 2
def baseEnd_445010 : Nat := 135409793219205410387225

theorem tailTrace_445010 : CollatzResearch.WordTrace tailWord_445010 prefixEnd_445010 135409793219205410387225 := by
  unfold tailWord_445010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4057712029453061625577121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10820565411874831001538989 4057712029453061625577121)
  ·
    refine ⟨3043284022089796219182841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4057712029453061625577121 3043284022089796219182841)
    ·
      refine ⟨2282463016567347164387131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3043284022089796219182841 2282463016567347164387131)
      ·
        refine ⟨3423694524851020746580697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282463016567347164387131 3423694524851020746580697)
        ·
          refine ⟨2567770893638265559935523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423694524851020746580697 2567770893638265559935523)
          ·
            refine ⟨3851656340457398339903285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567770893638265559935523 3851656340457398339903285)
            ·
              refine ⟨361092781917881094365933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3851656340457398339903285 361092781917881094365933)
              ·
                refine ⟨135409793219205410387225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361092781917881094365933 135409793219205410387225)
                ·
                  rfl

theorem cell19_445010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_445010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445010 prefixEnd_445010 := by exact prefixLift 445010
  have htrace : WordTrace (prefixWord ++ tailWord_445010) baseStart_445010 baseEnd_445010 := by
    simpa [prefixWord, tailWord_445010, baseEnd_445010] using wordTrace_append hprefix tailTrace_445010
  have hstable : (prefixWord ++ tailWord_445010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445010).length < 2 ^ (prefixWord ++ tailWord_445010).sum := by decide
  have hdescent : baseEnd_445010 < baseStart_445010 := by decide
  rcases family_descends (prefixWord ++ tailWord_445010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445071 : List Nat := [1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_445071 : Nat := 118140960795 + 445071 * 2 ^ 59
def prefixEnd_445071 : Nat := 4983230072969 + 3 ^ 40 * 445071 * 2
def baseEnd_445071 : Nat := 135428354593975343031503

theorem tailTrace_445071 : CollatzResearch.WordTrace tailWord_445071 prefixEnd_445071 135428354593975343031503 := by
  unfold tailWord_445071
  simp only [CollatzResearch.WordTrace]
  refine ⟨16233072970591253920279067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10822048647060835946852711 16233072970591253920279067)
  ·
    refine ⟨24349609455886880880418601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16233072970591253920279067 24349609455886880880418601)
    ·
      refine ⟨18262207091915160660313951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24349609455886880880418601 18262207091915160660313951)
      ·
        refine ⟨27393310637872740990470927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18262207091915160660313951 27393310637872740990470927)
        ·
          refine ⟨41089965956809111485706391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27393310637872740990470927 41089965956809111485706391)
          ·
            refine ⟨61634948935213667228559587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41089965956809111485706391 61634948935213667228559587)
            ·
              refine ⟨92452423402820500842839381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61634948935213667228559587 92452423402820500842839381)
              ·
                refine ⟨135428354593975343031503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 92452423402820500842839381 135428354593975343031503)
                ·
                  rfl

theorem cell19_445071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_445071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445071 prefixEnd_445071 := by exact prefixLift 445071
  have htrace : WordTrace (prefixWord ++ tailWord_445071) baseStart_445071 baseEnd_445071 := by
    simpa [prefixWord, tailWord_445071, baseEnd_445071] using wordTrace_append hprefix tailTrace_445071
  have hstable : (prefixWord ++ tailWord_445071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445071).length < 2 ^ (prefixWord ++ tailWord_445071).sum := by decide
  have hdescent : baseEnd_445071 < baseStart_445071 := by decide
  rcases family_descends (prefixWord ++ tailWord_445071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445107 : List Nat := [1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_445107 : Nat := 118140960795 + 445107 * 2 ^ 59
def prefixEnd_445107 : Nat := 4983230072969 + 3 ^ 40 * 445107 * 2
def baseEnd_445107 : Nat := 135439308847937926231405

theorem tailTrace_445107 : CollatzResearch.WordTrace tailWord_445107 prefixEnd_445107 135439308847937926231405 := by
  unfold tailWord_445107
  simp only [CollatzResearch.WordTrace]
  refine ⟨16234385998460832068589575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10822923998973888045726383 16234385998460832068589575)
  ·
    refine ⟨24351578997691248102884363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16234385998460832068589575 24351578997691248102884363)
    ·
      refine ⟨36527368496536872154326545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24351578997691248102884363 36527368496536872154326545)
      ·
        refine ⟨27395526372402654115744909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36527368496536872154326545 27395526372402654115744909)
        ·
          refine ⟨10273322389650995293404341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27395526372402654115744909 10273322389650995293404341)
          ·
            refine ⟨963123974029780808756657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10273322389650995293404341 963123974029780808756657)
            ·
              refine ⟨722342980522335606567493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963123974029780808756657 722342980522335606567493)
              ·
                refine ⟨135439308847937926231405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 722342980522335606567493 135439308847937926231405)
                ·
                  rfl

theorem cell19_445107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_445107 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445107 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445107 prefixEnd_445107 := by exact prefixLift 445107
  have htrace : WordTrace (prefixWord ++ tailWord_445107) baseStart_445107 baseEnd_445107 := by
    simpa [prefixWord, tailWord_445107, baseEnd_445107] using wordTrace_append hprefix tailTrace_445107
  have hstable : (prefixWord ++ tailWord_445107).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445107).length < 2 ^ (prefixWord ++ tailWord_445107).sum := by decide
  have hdescent : baseEnd_445107 < baseStart_445107 := by decide
  rcases family_descends (prefixWord ++ tailWord_445107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445160 : List Nat := [2, 1, 4, 1, 5, 1, 1, 4]
def baseStart_445160 : Nat := 118140960795 + 445160 * 2 ^ 59
def prefixEnd_445160 : Nat := 4983230072969 + 3 ^ 40 * 445160 * 2
def baseEnd_445160 : Nat := 135455435944049507053483

theorem tailTrace_445160 : CollatzResearch.WordTrace tailWord_445160 prefixEnd_445160 135455435944049507053483 := by
  unfold tailWord_445160
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118159533634411060134467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10824212711512548080179289 8118159533634411060134467)
  ·
    refine ⟨12177239300451616590201701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8118159533634411060134467 12177239300451616590201701)
    ·
      refine ⟨2283232368834678110662819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12177239300451616590201701 2283232368834678110662819)
      ·
        refine ⟨3424848553252017165994229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283232368834678110662819 3424848553252017165994229)
        ·
          refine ⟨321079551867376609311959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3424848553252017165994229 321079551867376609311959)
          ·
            refine ⟨481619327801064913967939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321079551867376609311959 481619327801064913967939)
            ·
              refine ⟨722428991701597370951909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481619327801064913967939 722428991701597370951909)
              ·
                refine ⟨135455435944049507053483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 722428991701597370951909 135455435944049507053483)
                ·
                  rfl

theorem cell19_445160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_445160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445160 prefixEnd_445160 := by exact prefixLift 445160
  have htrace : WordTrace (prefixWord ++ tailWord_445160) baseStart_445160 baseEnd_445160 := by
    simpa [prefixWord, tailWord_445160, baseEnd_445160] using wordTrace_append hprefix tailTrace_445160
  have hstable : (prefixWord ++ tailWord_445160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445160).length < 2 ^ (prefixWord ++ tailWord_445160).sum := by decide
  have hdescent : baseEnd_445160 < baseStart_445160 := by decide
  rcases family_descends (prefixWord ++ tailWord_445160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445276 : List Nat := [2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_445276 : Nat := 118140960795 + 445276 * 2 ^ 59
def prefixEnd_445276 : Nat := 4983230072969 + 3 ^ 40 * 445276 * 2
def baseEnd_445276 : Nat := 135490732984595608475389

theorem tailTrace_445276 : CollatzResearch.WordTrace tailWord_445276 prefixEnd_445276 135490732984595608475389 := by
  unfold tailWord_445276
  simp only [CollatzResearch.WordTrace]
  refine ⟨8120274967424286965745841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10827033289899049287661121 8120274967424286965745841)
  ·
    refine ⟨6090206225568215224309381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8120274967424286965745841 6090206225568215224309381)
    ·
      refine ⟨1141913667294040354558009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6090206225568215224309381 1141913667294040354558009)
      ·
        refine ⟨856435250470530265918507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1141913667294040354558009 856435250470530265918507)
        ·
          refine ⟨1284652875705795398877761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856435250470530265918507 1284652875705795398877761)
          ·
            refine ⟨963489656779346549158321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284652875705795398877761 963489656779346549158321)
            ·
              refine ⟨722617242584509911868741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963489656779346549158321 722617242584509911868741)
              ·
                refine ⟨135490732984595608475389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 722617242584509911868741 135490732984595608475389)
                ·
                  rfl

theorem cell19_445276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_445276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445276 prefixEnd_445276 := by exact prefixLift 445276
  have htrace : WordTrace (prefixWord ++ tailWord_445276) baseStart_445276 baseEnd_445276 := by
    simpa [prefixWord, tailWord_445276, baseEnd_445276] using wordTrace_append hprefix tailTrace_445276
  have hstable : (prefixWord ++ tailWord_445276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445276).length < 2 ^ (prefixWord ++ tailWord_445276).sum := by decide
  have hdescent : baseEnd_445276 < baseStart_445276 := by decide
  rcases family_descends (prefixWord ++ tailWord_445276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445299 : List Nat := [1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_445299 : Nat := 118140960795 + 445299 * 2 ^ 59
def prefixEnd_445299 : Nat := 4983230072969 + 3 ^ 40 * 445299 * 2
def baseEnd_445299 : Nat := 135497731535738369964215

theorem tailTrace_445299 : CollatzResearch.WordTrace tailWord_445299 prefixEnd_445299 135497731535738369964215 := by
  unfold tailWord_445299
  simp only [CollatzResearch.WordTrace]
  refine ⟨16241388813765248859578951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10827592542510165906385967 16241388813765248859578951)
  ·
    refine ⟨24362083220647873289368427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16241388813765248859578951 24362083220647873289368427)
    ·
      refine ⟨36543124830971809934052641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24362083220647873289368427 36543124830971809934052641)
      ·
        refine ⟨27407343623228857450539481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36543124830971809934052641 27407343623228857450539481)
        ·
          refine ⟨20555507717421643087904611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27407343623228857450539481 20555507717421643087904611)
          ·
            refine ⟨30833261576132464631856917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20555507717421643087904611 30833261576132464631856917)
            ·
              refine ⟨1445309136381209279618293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30833261576132464631856917 1445309136381209279618293)
              ·
                refine ⟨135497731535738369964215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1445309136381209279618293 135497731535738369964215)
                ·
                  rfl

theorem cell19_445299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_445299 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445299 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445299 prefixEnd_445299 := by exact prefixLift 445299
  have htrace : WordTrace (prefixWord ++ tailWord_445299) baseStart_445299 baseEnd_445299 := by
    simpa [prefixWord, tailWord_445299, baseEnd_445299] using wordTrace_append hprefix tailTrace_445299
  have hstable : (prefixWord ++ tailWord_445299).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445299).length < 2 ^ (prefixWord ++ tailWord_445299).sum := by decide
  have hdescent : baseEnd_445299 < baseStart_445299 := by decide
  rcases family_descends (prefixWord ++ tailWord_445299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445314 : List Nat := [3, 4, 2, 2, 8]
def baseStart_445314 : Nat := 118140960795 + 445314 * 2 ^ 59
def prefixEnd_445314 : Nat := 4983230072969 + 3 ^ 40 * 445314 * 2
def baseEnd_445314 : Nat := 5018603548452695541883

theorem tailTrace_445314 : CollatzResearch.WordTrace tailWord_445314 prefixEnd_445314 5018603548452695541883 := by
  unfold tailWord_445314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060483977177726605343749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10827957272473937614249997 4060483977177726605343749)
  ·
    refine ⟨761340745720823738501953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4060483977177726605343749 761340745720823738501953)
    ·
      refine ⟨571005559290617803876465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 761340745720823738501953 571005559290617803876465)
      ·
        refine ⟨428254169467963352907349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571005559290617803876465 428254169467963352907349)
        ·
          refine ⟨5018603548452695541883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 428254169467963352907349 5018603548452695541883)
          ·
            rfl

theorem cell19_445314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 8].length) (baseStart_445314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445314 prefixEnd_445314 := by exact prefixLift 445314
  have htrace : WordTrace (prefixWord ++ tailWord_445314) baseStart_445314 baseEnd_445314 := by
    simpa [prefixWord, tailWord_445314, baseEnd_445314] using wordTrace_append hprefix tailTrace_445314
  have hstable : (prefixWord ++ tailWord_445314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445314).length < 2 ^ (prefixWord ++ tailWord_445314).sum := by decide
  have hdescent : baseEnd_445314 < baseStart_445314 := by decide
  rcases family_descends (prefixWord ++ tailWord_445314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445373 : List Nat := [1, 4, 1, 2, 4, 1, 6]
def baseStart_445373 : Nat := 118140960795 + 445373 * 2 ^ 59
def prefixEnd_445373 : Nat := 4983230072969 + 3 ^ 40 * 445373 * 2
def baseEnd_445373 : Nat := 45173416204442708106523

theorem tailTrace_445373 : CollatzResearch.WordTrace tailWord_445373 prefixEnd_445373 45173416204442708106523 := by
  unfold tailWord_445373
  simp only [CollatzResearch.WordTrace]
  refine ⟨16244087815497159497772773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10829391876998106331848515 16244087815497159497772773)
  ·
    refine ⟨3045766465405717405832395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16244087815497159497772773 3045766465405717405832395)
    ·
      refine ⟨4568649698108576108748593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045766465405717405832395 4568649698108576108748593)
      ·
        refine ⟨3426487273581432081561445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4568649698108576108748593 3426487273581432081561445)
        ·
          refine ⟨642466363796518515292771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3426487273581432081561445 642466363796518515292771)
          ·
            refine ⟨963699545694777772939157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642466363796518515292771 963699545694777772939157)
            ·
              refine ⟨45173416204442708106523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 963699545694777772939157 45173416204442708106523)
              ·
                rfl

theorem cell19_445373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_445373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445373 prefixEnd_445373 := by exact prefixLift 445373
  have htrace : WordTrace (prefixWord ++ tailWord_445373) baseStart_445373 baseEnd_445373 := by
    simpa [prefixWord, tailWord_445373, baseEnd_445373] using wordTrace_append hprefix tailTrace_445373
  have hstable : (prefixWord ++ tailWord_445373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445373).length < 2 ^ (prefixWord ++ tailWord_445373).sum := by decide
  have hdescent : baseEnd_445373 < baseStart_445373 := by decide
  rcases family_descends (prefixWord ++ tailWord_445373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445407 : List Nat := [1, 1, 2, 3, 6, 1, 2, 3]
def baseStart_445407 : Nat := 118140960795 + 445407 * 2 ^ 59
def prefixEnd_445407 : Nat := 4983230072969 + 3 ^ 40 * 445407 * 2
def baseEnd_445407 : Nat := 135530594297626119563921

theorem tailTrace_445407 : CollatzResearch.WordTrace tailWord_445407 prefixEnd_445407 135530594297626119563921 := by
  unfold tailWord_445407
  simp only [CollatzResearch.WordTrace]
  refine ⟨16245327897373983304510475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10830218598249322203006983 16245327897373983304510475)
  ·
    refine ⟨24367991846060974956765713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16245327897373983304510475 24367991846060974956765713)
    ·
      refine ⟨18275993884545731217574285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24367991846060974956765713 18275993884545731217574285)
      ·
        refine ⟨6853497706704649206590357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18275993884545731217574285 6853497706704649206590357)
        ·
          refine ⟨321257705001780431558923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6853497706704649206590357 321257705001780431558923)
          ·
            refine ⟨481886557502670647338385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321257705001780431558923 481886557502670647338385)
            ·
              refine ⟨361414918127002985503789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481886557502670647338385 361414918127002985503789)
              ·
                refine ⟨135530594297626119563921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361414918127002985503789 135530594297626119563921)
                ·
                  rfl

theorem cell19_445407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 3].length) (baseStart_445407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445407 prefixEnd_445407 := by exact prefixLift 445407
  have htrace : WordTrace (prefixWord ++ tailWord_445407) baseStart_445407 baseEnd_445407 := by
    simpa [prefixWord, tailWord_445407, baseEnd_445407] using wordTrace_append hprefix tailTrace_445407
  have hstable : (prefixWord ++ tailWord_445407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445407).length < 2 ^ (prefixWord ++ tailWord_445407).sum := by decide
  have hdescent : baseEnd_445407 < baseStart_445407 := by decide
  rcases family_descends (prefixWord ++ tailWord_445407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445426 : List Nat := [3, 2, 1, 5, 2, 1, 5]
def baseStart_445426 : Nat := 118140960795 + 445426 * 2 ^ 59
def prefixEnd_445426 : Nat := 4983230072969 + 3 ^ 40 * 445426 * 2
def baseEnd_445426 : Nat := 45178791903146568380549

theorem tailTrace_445426 : CollatzResearch.WordTrace tailWord_445426 prefixEnd_445426 45178791903146568380549 := by
  unfold tailWord_445426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061505221076287387363033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10830680589536766366301421 4061505221076287387363033)
  ·
    refine ⟨3046128915807215540522275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4061505221076287387363033 3046128915807215540522275)
    ·
      refine ⟨4569193373710823310783413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046128915807215540522275 4569193373710823310783413)
      ·
        refine ⟨428361878785389685385945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4569193373710823310783413 428361878785389685385945)
        ·
          refine ⟨321271409089042264039459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428361878785389685385945 321271409089042264039459)
          ·
            refine ⟨481907113633563396059189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321271409089042264039459 481907113633563396059189)
            ·
              refine ⟨45178791903146568380549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 481907113633563396059189 45178791903146568380549)
              ·
                rfl

theorem cell19_445426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_445426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445426 prefixEnd_445426 := by exact prefixLift 445426
  have htrace : WordTrace (prefixWord ++ tailWord_445426) baseStart_445426 baseEnd_445426 := by
    simpa [prefixWord, tailWord_445426, baseEnd_445426] using wordTrace_append hprefix tailTrace_445426
  have hstable : (prefixWord ++ tailWord_445426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445426).length < 2 ^ (prefixWord ++ tailWord_445426).sum := by decide
  have hdescent : baseEnd_445426 < baseStart_445426 := by decide
  rcases family_descends (prefixWord ++ tailWord_445426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445430 : List Nat := [5, 1, 1, 1, 3, 1, 7]
def baseStart_445430 : Nat := 118140960795 + 445430 * 2 ^ 59
def prefixEnd_445430 : Nat := 4983230072969 + 3 ^ 40 * 445430 * 2
def baseEnd_445430 : Nat := 45179197616256293684249

theorem tailTrace_445430 : CollatzResearch.WordTrace tailWord_445430 prefixEnd_445430 45179197616256293684249 := by
  unfold tailWord_445430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1015385423518166139537359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10830777850860438821731829 1015385423518166139537359)
  ·
    refine ⟨1523078135277249209306039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1015385423518166139537359 1523078135277249209306039)
    ·
      refine ⟨2284617202915873813959059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1523078135277249209306039 2284617202915873813959059)
      ·
        refine ⟨3426925804373810720938589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284617202915873813959059 3426925804373810720938589)
        ·
          refine ⟨1285097176640179020351971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3426925804373810720938589 1285097176640179020351971)
          ·
            refine ⟨1927645764960268530527957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285097176640179020351971 1927645764960268530527957)
            ·
              refine ⟨45179197616256293684249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1927645764960268530527957 45179197616256293684249)
              ·
                rfl

theorem cell19_445430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_445430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445430 prefixEnd_445430 := by exact prefixLift 445430
  have htrace : WordTrace (prefixWord ++ tailWord_445430) baseStart_445430 baseEnd_445430 := by
    simpa [prefixWord, tailWord_445430, baseEnd_445430] using wordTrace_append hprefix tailTrace_445430
  have hstable : (prefixWord ++ tailWord_445430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445430).length < 2 ^ (prefixWord ++ tailWord_445430).sum := by decide
  have hdescent : baseEnd_445430 < baseStart_445430 := by decide
  rcases family_descends (prefixWord ++ tailWord_445430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445451 : List Nat := [1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_445451 : Nat := 118140960795 + 445451 * 2 ^ 59
def prefixEnd_445451 : Nat := 4983230072969 + 3 ^ 40 * 445451 * 2
def baseEnd_445451 : Nat := 135543982830247054586023

theorem tailTrace_445451 : CollatzResearch.WordTrace tailWord_445451 prefixEnd_445451 135543982830247054586023 := by
  unfold tailWord_445451
  simp only [CollatzResearch.WordTrace]
  refine ⟨16246932709214578819112207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10831288472809719212741471 16246932709214578819112207)
  ·
    refine ⟨24370399063821868228668311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16246932709214578819112207 24370399063821868228668311)
    ·
      refine ⟨36555598595732802343002467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24370399063821868228668311 36555598595732802343002467)
      ·
        refine ⟨54833397893599203514503701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36555598595732802343002467 54833397893599203514503701)
        ·
          refine ⟨2570315526262462664742361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54833397893599203514503701 2570315526262462664742361)
          ·
            refine ⟨1927736644696846998556771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2570315526262462664742361 1927736644696846998556771)
            ·
              refine ⟨2891604967045270497835157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927736644696846998556771 2891604967045270497835157)
              ·
                refine ⟨135543982830247054586023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2891604967045270497835157 135543982830247054586023)
                ·
                  rfl

theorem cell19_445451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_445451 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445451 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445451 prefixEnd_445451 := by exact prefixLift 445451
  have htrace : WordTrace (prefixWord ++ tailWord_445451) baseStart_445451 baseEnd_445451 := by
    simpa [prefixWord, tailWord_445451, baseEnd_445451] using wordTrace_append hprefix tailTrace_445451
  have hstable : (prefixWord ++ tailWord_445451).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445451).length < 2 ^ (prefixWord ++ tailWord_445451).sum := by decide
  have hdescent : baseEnd_445451 < baseStart_445451 := by decide
  rcases family_descends (prefixWord ++ tailWord_445451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445525 : List Nat := [1, 3, 2, 2, 1, 2, 5, 3]
def baseStart_445525 : Nat := 118140960795 + 445525 * 2 ^ 59
def prefixEnd_445525 : Nat := 4983230072969 + 3 ^ 40 * 445525 * 2
def baseEnd_445525 : Nat := 135566499907836808941377

theorem tailTrace_445525 : CollatzResearch.WordTrace tailWord_445525 prefixEnd_445525 135566499907836808941377 := by
  unfold tailWord_445525
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249631710946489457306029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10833087807297659638204019 16249631710946489457306029)
  ·
    refine ⟨6093611891604933546489761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16249631710946489457306029 6093611891604933546489761)
    ·
      refine ⟨4570208918703700159867321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6093611891604933546489761 4570208918703700159867321)
      ·
        refine ⟨3427656689027775119900491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4570208918703700159867321 3427656689027775119900491)
        ·
          refine ⟨5141485033541662679850737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3427656689027775119900491 5141485033541662679850737)
          ·
            refine ⟨3856113775156247009888053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5141485033541662679850737 3856113775156247009888053)
            ·
              refine ⟨361510666420898157177005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3856113775156247009888053 361510666420898157177005)
              ·
                refine ⟨135566499907836808941377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361510666420898157177005 135566499907836808941377)
                ·
                  rfl

theorem cell19_445525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_445525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445525 prefixEnd_445525 := by exact prefixLift 445525
  have htrace : WordTrace (prefixWord ++ tailWord_445525) baseStart_445525 baseEnd_445525 := by
    simpa [prefixWord, tailWord_445525, baseEnd_445525] using wordTrace_append hprefix tailTrace_445525
  have hstable : (prefixWord ++ tailWord_445525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445525).length < 2 ^ (prefixWord ++ tailWord_445525).sum := by decide
  have hdescent : baseEnd_445525 < baseStart_445525 := by decide
  rcases family_descends (prefixWord ++ tailWord_445525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445565 : List Nat := [1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_445565 : Nat := 118140960795 + 445565 * 2 ^ 59
def prefixEnd_445565 : Nat := 4983230072969 + 3 ^ 40 * 445565 * 2
def baseEnd_445565 : Nat := 135578671301128568052379

theorem tailTrace_445565 : CollatzResearch.WordTrace tailWord_445565 prefixEnd_445565 135578671301128568052379 := by
  unfold tailWord_445565
  simp only [CollatzResearch.WordTrace]
  refine ⟨16251090630801576288762149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10834060420534384192508099 16251090630801576288762149)
  ·
    refine ⟨3047079493275295554142903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16251090630801576288762149 3047079493275295554142903)
    ·
      refine ⟨4570619239912943331214355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047079493275295554142903 4570619239912943331214355)
      ·
        refine ⟨6855928859869414996821533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4570619239912943331214355 6855928859869414996821533)
        ·
          refine ⟨2570973322451030623808075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6855928859869414996821533 2570973322451030623808075)
          ·
            refine ⟨3856459983676545935712113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570973322451030623808075 3856459983676545935712113)
            ·
              refine ⟨2892344987757409451784085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3856459983676545935712113 2892344987757409451784085)
              ·
                refine ⟨135578671301128568052379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2892344987757409451784085 135578671301128568052379)
                ·
                  rfl

theorem cell19_445565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_445565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445565 prefixEnd_445565 := by exact prefixLift 445565
  have htrace : WordTrace (prefixWord ++ tailWord_445565) baseStart_445565 baseEnd_445565 := by
    simpa [prefixWord, tailWord_445565, baseEnd_445565] using wordTrace_append hprefix tailTrace_445565
  have hstable : (prefixWord ++ tailWord_445565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445565).length < 2 ^ (prefixWord ++ tailWord_445565).sum := by decide
  have hdescent : baseEnd_445565 < baseStart_445565 := by decide
  rcases family_descends (prefixWord ++ tailWord_445565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445582 : List Nat := [4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_445582 : Nat := 118140960795 + 445582 * 2 ^ 59
def prefixEnd_445582 : Nat := 4983230072969 + 3 ^ 40 * 445582 * 2
def baseEnd_445582 : Nat := 135583844143277565674555

theorem tailTrace_445582 : CollatzResearch.WordTrace tailWord_445582 prefixEnd_445582 135583844143277565674555 := by
  unfold tailWord_445582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031463833967498524016375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10834473781159992128087333 2031463833967498524016375)
  ·
    refine ⟨3047195750951247786024563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2031463833967498524016375 3047195750951247786024563)
    ·
      refine ⟨4570793626426871679036845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047195750951247786024563 4570793626426871679036845)
      ·
        refine ⟨1714047609910076879638817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4570793626426871679036845 1714047609910076879638817)
        ·
          refine ⟨1285535707432557659729113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1714047609910076879638817 1285535707432557659729113)
          ·
            refine ⟨964151780574418244796835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285535707432557659729113 964151780574418244796835)
            ·
              refine ⟨1446227670861627367195253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964151780574418244796835 1446227670861627367195253)
              ·
                refine ⟨135583844143277565674555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1446227670861627367195253 135583844143277565674555)
                ·
                  rfl

theorem cell19_445582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_445582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445582 prefixEnd_445582 := by exact prefixLift 445582
  have htrace : WordTrace (prefixWord ++ tailWord_445582) baseStart_445582 baseEnd_445582 := by
    simpa [prefixWord, tailWord_445582, baseEnd_445582] using wordTrace_append hprefix tailTrace_445582
  have hstable : (prefixWord ++ tailWord_445582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445582).length < 2 ^ (prefixWord ++ tailWord_445582).sum := by decide
  have hdescent : baseEnd_445582 < baseStart_445582 := by decide
  rcases family_descends (prefixWord ++ tailWord_445582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445599 : List Nat := [1, 1, 2, 6, 3, 1, 5]
def baseStart_445599 : Nat := 118140960795 + 445599 * 2 ^ 59
def prefixEnd_445599 : Nat := 4983230072969 + 3 ^ 40 * 445599 * 2
def baseEnd_445599 : Nat := 45196338995142187765577

theorem tailTrace_445599 : CollatzResearch.WordTrace tailWord_445599 prefixEnd_445599 45196338995142187765577 := by
  unfold tailWord_445599
  simp only [CollatzResearch.WordTrace]
  refine ⟨16252330712678400095499851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10834887141785600063666567 16252330712678400095499851)
  ·
    refine ⟨24378496069017600143249777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16252330712678400095499851 24378496069017600143249777)
    ·
      refine ⟨18283872051763200107437333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24378496069017600143249777 18283872051763200107437333)
      ·
        refine ⟨857056502426400005036125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18283872051763200107437333 857056502426400005036125)
        ·
          refine ⟨321396188409900001888547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 857056502426400005036125 321396188409900001888547)
          ·
            refine ⟨482094282614850002832821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321396188409900001888547 482094282614850002832821)
            ·
              refine ⟨45196338995142187765577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 482094282614850002832821 45196338995142187765577)
              ·
                rfl

theorem cell19_445599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_445599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445599 prefixEnd_445599 := by exact prefixLift 445599
  have htrace : WordTrace (prefixWord ++ tailWord_445599) baseStart_445599 baseEnd_445599 := by
    simpa [prefixWord, tailWord_445599, baseEnd_445599] using wordTrace_append hprefix tailTrace_445599
  have hstable : (prefixWord ++ tailWord_445599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445599).length < 2 ^ (prefixWord ++ tailWord_445599).sum := by decide
  have hdescent : baseEnd_445599 < baseStart_445599 := by decide
  rcases family_descends (prefixWord ++ tailWord_445599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445660 : List Nat := [2, 2, 5, 10]
def baseStart_445660 : Nat := 118140960795 + 445660 * 2 ^ 59
def prefixEnd_445660 : Nat := 4983230072969 + 3 ^ 40 * 445660 * 2
def baseEnd_445660 : Nat := 1674167634076499949889

theorem tailTrace_445660 : CollatzResearch.WordTrace tailWord_445660 prefixEnd_445660 1674167634076499949889 := by
  unfold tailWord_445660
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127277782728703756735217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10836370376971605008980289 8127277782728703756735217)
  ·
    refine ⟨6095458337046527817551413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8127277782728703756735217 6095458337046527817551413)
    ·
      refine ⟨571449219098111982895445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6095458337046527817551413 571449219098111982895445)
      ·
        refine ⟨1674167634076499949889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 571449219098111982895445 1674167634076499949889)
        ·
          rfl

theorem cell19_445660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 10].length) (baseStart_445660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445660 prefixEnd_445660 := by exact prefixLift 445660
  have htrace : WordTrace (prefixWord ++ tailWord_445660) baseStart_445660 baseEnd_445660 := by
    simpa [prefixWord, tailWord_445660, baseEnd_445660] using wordTrace_append hprefix tailTrace_445660
  have hstable : (prefixWord ++ tailWord_445660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445660).length < 2 ^ (prefixWord ++ tailWord_445660).sum := by decide
  have hdescent : baseEnd_445660 < baseStart_445660 := by decide
  rcases family_descends (prefixWord ++ tailWord_445660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445677 : List Nat := [1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_445677 : Nat := 118140960795 + 445677 * 2 ^ 59
def prefixEnd_445677 : Nat := 4983230072969 + 3 ^ 40 * 445677 * 2
def baseEnd_445677 : Nat := 135612751202345493563185

theorem tailTrace_445677 : CollatzResearch.WordTrace tailWord_445677 prefixEnd_445677 135612751202345493563185 := by
  unfold tailWord_445677
  simp only [CollatzResearch.WordTrace]
  refine ⟨16255175606395819416839285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10836783737597212944559523 16255175606395819416839285)
  ·
    refine ⟨1523922713099608070328683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16255175606395819416839285 1523922713099608070328683)
    ·
      refine ⟨2285884069649412105493025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1523922713099608070328683 2285884069649412105493025)
      ·
        refine ⟨1714413052237059079119769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2285884069649412105493025 1714413052237059079119769)
        ·
          refine ⟨1285809789177794309339827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1714413052237059079119769 1285809789177794309339827)
          ·
            refine ⟨1928714683766691464009741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285809789177794309339827 1928714683766691464009741)
            ·
              refine ⟨723268006412509299003653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1928714683766691464009741 723268006412509299003653)
              ·
                refine ⟨135612751202345493563185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 723268006412509299003653 135612751202345493563185)
                ·
                  rfl

theorem cell19_445677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_445677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445677 prefixEnd_445677 := by exact prefixLift 445677
  have htrace : WordTrace (prefixWord ++ tailWord_445677) baseStart_445677 baseEnd_445677 := by
    simpa [prefixWord, tailWord_445677, baseEnd_445677] using wordTrace_append hprefix tailTrace_445677
  have hstable : (prefixWord ++ tailWord_445677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445677).length < 2 ^ (prefixWord ++ tailWord_445677).sum := by decide
  have hdescent : baseEnd_445677 < baseStart_445677 := by decide
  rcases family_descends (prefixWord ++ tailWord_445677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445694 : List Nat := [4, 2, 2, 1, 1, 3, 3, 3]
def baseStart_445694 : Nat := 118140960795 + 445694 * 2 ^ 59
def prefixEnd_445694 : Nat := 4983230072969 + 3 ^ 40 * 445694 * 2
def baseEnd_445694 : Nat := 135617924044494491185361

theorem tailTrace_445694 : CollatzResearch.WordTrace tailWord_445694 prefixEnd_445694 135617924044494491185361 := by
  unfold tailWord_445694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031974455916778915026017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10837197098222820880138757 2031974455916778915026017)
  ·
    refine ⟨1523980841937584186269513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2031974455916778915026017 1523980841937584186269513)
    ·
      refine ⟨1142985631453188139702135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1523980841937584186269513 1142985631453188139702135)
      ·
        refine ⟨1714478447179782209553203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142985631453188139702135 1714478447179782209553203)
        ·
          refine ⟨2571717670769673314329805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714478447179782209553203 2571717670769673314329805)
          ·
            refine ⟨964394126538627492873677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2571717670769673314329805 964394126538627492873677)
            ·
              refine ⟨361647797451985309827629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964394126538627492873677 361647797451985309827629)
              ·
                refine ⟨135617924044494491185361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361647797451985309827629 135617924044494491185361)
                ·
                  rfl

theorem cell19_445694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_445694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445694 prefixEnd_445694 := by exact prefixLift 445694
  have htrace : WordTrace (prefixWord ++ tailWord_445694) baseStart_445694 baseEnd_445694 := by
    simpa [prefixWord, tailWord_445694, baseEnd_445694] using wordTrace_append hprefix tailTrace_445694
  have hstable : (prefixWord ++ tailWord_445694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445694).length < 2 ^ (prefixWord ++ tailWord_445694).sum := by decide
  have hdescent : baseEnd_445694 < baseStart_445694 := by decide
  rcases family_descends (prefixWord ++ tailWord_445694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445753 : List Nat := [1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_445753 : Nat := 118140960795 + 445753 * 2 ^ 59
def prefixEnd_445753 : Nat := 4983230072969 + 3 ^ 40 * 445753 * 2
def baseEnd_445753 : Nat := 135635876849599835874089

theorem tailTrace_445753 : CollatzResearch.WordTrace tailWord_445753 prefixEnd_445753 135635876849599835874089 := by
  unfold tailWord_445753
  simp only [CollatzResearch.WordTrace]
  refine ⟨16257947554120484396605913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10838631702746989597737275 16257947554120484396605913)
  ·
    refine ⟨12193460665590363297454435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16257947554120484396605913 12193460665590363297454435)
    ·
      refine ⟨18290190998385544946181653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12193460665590363297454435 18290190998385544946181653)
      ·
        refine ⟨857352703049322419352265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18290190998385544946181653 857352703049322419352265)
        ·
          refine ⟨643014527286991814514199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857352703049322419352265 643014527286991814514199)
          ·
            refine ⟨964521790930487721771299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643014527286991814514199 964521790930487721771299)
            ·
              refine ⟨1446782686395731582656949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964521790930487721771299 1446782686395731582656949)
              ·
                refine ⟨135635876849599835874089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1446782686395731582656949 135635876849599835874089)
                ·
                  rfl

theorem cell19_445753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_445753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445753 prefixEnd_445753 := by exact prefixLift 445753
  have htrace : WordTrace (prefixWord ++ tailWord_445753) baseStart_445753 baseEnd_445753 := by
    simpa [prefixWord, tailWord_445753, baseEnd_445753] using wordTrace_append hprefix tailTrace_445753
  have hstable : (prefixWord ++ tailWord_445753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445753).length < 2 ^ (prefixWord ++ tailWord_445753).sum := by decide
  have hdescent : baseEnd_445753 < baseStart_445753 := by decide
  rcases family_descends (prefixWord ++ tailWord_445753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445766 : List Nat := [6, 1, 1, 3, 2, 1, 5]
def baseStart_445766 : Nat := 118140960795 + 445766 * 2 ^ 59
def prefixEnd_445766 : Nat := 4983230072969 + 3 ^ 40 * 445766 * 2
def baseEnd_445766 : Nat := 45213277517473219195055

theorem tailTrace_445766 : CollatzResearch.WordTrace tailWord_445766 prefixEnd_445766 45213277517473219195055 := by
  unfold tailWord_445766
  simp only [CollatzResearch.WordTrace]
  refine ⟨508075678221043363025911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10838947802048925077886101 508075678221043363025911)
  ·
    refine ⟨762113517331565044538867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 508075678221043363025911 762113517331565044538867)
    ·
      refine ⟨1143170275997347566808301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762113517331565044538867 1143170275997347566808301)
      ·
        refine ⟨428688853499005337553113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1143170275997347566808301 428688853499005337553113)
        ·
          refine ⟨321516640124254003164835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428688853499005337553113 321516640124254003164835)
          ·
            refine ⟨482274960186381004747253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321516640124254003164835 482274960186381004747253)
            ·
              refine ⟨45213277517473219195055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 482274960186381004747253 45213277517473219195055)
              ·
                rfl

theorem cell19_445766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_445766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445766 prefixEnd_445766 := by exact prefixLift 445766
  have htrace : WordTrace (prefixWord ++ tailWord_445766) baseStart_445766 baseEnd_445766 := by
    simpa [prefixWord, tailWord_445766, baseEnd_445766] using wordTrace_append hprefix tailTrace_445766
  have hstable : (prefixWord ++ tailWord_445766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445766).length < 2 ^ (prefixWord ++ tailWord_445766).sum := by decide
  have hdescent : baseEnd_445766 < baseStart_445766 := by decide
  rcases family_descends (prefixWord ++ tailWord_445766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445833 : List Nat := [1, 2, 1, 1, 14]
def baseStart_445833 : Nat := 118140960795 + 445833 * 2 ^ 59
def prefixEnd_445833 : Nat := 4983230072969 + 3 ^ 40 * 445833 * 2
def baseEnd_445833 : Nat := 5024452579117902003559

theorem tailTrace_445833 : CollatzResearch.WordTrace tailWord_445833 prefixEnd_445833 5024452579117902003559 := by
  unfold tailWord_445833
  simp only [CollatzResearch.WordTrace]
  refine ⟨16260865393830658059518153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10840576929220438706345435 16260865393830658059518153)
  ·
    refine ⟨12195649045372993544638615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16260865393830658059518153 12195649045372993544638615)
    ·
      refine ⟨18293473568059490316957923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12195649045372993544638615 18293473568059490316957923)
      ·
        refine ⟨27440210352089235475436885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18293473568059490316957923 27440210352089235475436885)
        ·
          refine ⟨5024452579117902003559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 27440210352089235475436885 5024452579117902003559)
          ·
            rfl

theorem cell19_445833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 14].length) (baseStart_445833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445833 prefixEnd_445833 := by exact prefixLift 445833
  have htrace : WordTrace (prefixWord ++ tailWord_445833) baseStart_445833 baseEnd_445833 := by
    simpa [prefixWord, tailWord_445833, baseEnd_445833] using wordTrace_append hprefix tailTrace_445833
  have hstable : (prefixWord ++ tailWord_445833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445833).length < 2 ^ (prefixWord ++ tailWord_445833).sum := by decide
  have hdescent : baseEnd_445833 < baseStart_445833 := by decide
  rcases family_descends (prefixWord ++ tailWord_445833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445871 : List Nat := [1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_445871 : Nat := 118140960795 + 445871 * 2 ^ 59
def prefixEnd_445871 : Nat := 4983230072969 + 3 ^ 40 * 445871 * 2
def baseEnd_445871 : Nat := 135671782459810525251545

theorem tailTrace_445871 : CollatzResearch.WordTrace tailWord_445871 prefixEnd_445871 135671782459810525251545 := by
  unfold tailWord_445871
  simp only [CollatzResearch.WordTrace]
  refine ⟨16262251367692990549401467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10841500911795327032934311 16262251367692990549401467)
  ·
    refine ⟨24393377051539485824102201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16262251367692990549401467 24393377051539485824102201)
    ·
      refine ⟨18295032788654614368076651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24393377051539485824102201 18295032788654614368076651)
      ·
        refine ⟨27442549182981921552114977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18295032788654614368076651 27442549182981921552114977)
        ·
          refine ⟨20581911887236441164086233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27442549182981921552114977 20581911887236441164086233)
          ·
            refine ⟨15436433915427330873064675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20581911887236441164086233 15436433915427330873064675)
            ·
              refine ⟨23154650873140996309597013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15436433915427330873064675 23154650873140996309597013)
              ·
                refine ⟨135671782459810525251545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23154650873140996309597013 135671782459810525251545)
                ·
                  rfl

theorem cell19_445871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_445871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_445871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_445871 prefixEnd_445871 := by exact prefixLift 445871
  have htrace : WordTrace (prefixWord ++ tailWord_445871) baseStart_445871 baseEnd_445871 := by
    simpa [prefixWord, tailWord_445871, baseEnd_445871] using wordTrace_append hprefix tailTrace_445871
  have hstable : (prefixWord ++ tailWord_445871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445871).length < 2 ^ (prefixWord ++ tailWord_445871).sum := by decide
  have hdescent : baseEnd_445871 < baseStart_445871 := by decide
  rcases family_descends (prefixWord ++ tailWord_445871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446042 : List Nat := [3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_446042 : Nat := 118140960795 + 446042 * 2 ^ 59
def prefixEnd_446042 : Nat := 4983230072969 + 3 ^ 40 * 446042 * 2
def baseEnd_446042 : Nat := 135723815166132795451079

theorem tailTrace_446042 : CollatzResearch.WordTrace tailWord_446042 prefixEnd_446042 135723815166132795451079 := by
  unfold tailWord_446042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4067122062518371688469095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10845658833382324502584253 4067122062518371688469095)
  ·
    refine ⟨6100683093777557532703643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4067122062518371688469095 6100683093777557532703643)
    ·
      refine ⟨9151024640666336299055465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6100683093777557532703643 9151024640666336299055465)
      ·
        refine ⟨6863268480499752224291599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9151024640666336299055465 6863268480499752224291599)
        ·
          refine ⟨10294902720749628336437399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863268480499752224291599 10294902720749628336437399)
          ·
            refine ⟨15442354081124442504656099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10294902720749628336437399 15442354081124442504656099)
            ·
              refine ⟨23163531121686663756984149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15442354081124442504656099 23163531121686663756984149)
              ·
                refine ⟨135723815166132795451079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23163531121686663756984149 135723815166132795451079)
                ·
                  rfl

theorem cell19_446042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_446042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446042 prefixEnd_446042 := by exact prefixLift 446042
  have htrace : WordTrace (prefixWord ++ tailWord_446042) baseStart_446042 baseEnd_446042 := by
    simpa [prefixWord, tailWord_446042, baseEnd_446042] using wordTrace_append hprefix tailTrace_446042
  have hstable : (prefixWord ++ tailWord_446042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446042).length < 2 ^ (prefixWord ++ tailWord_446042).sum := by decide
  have hdescent : baseEnd_446042 < baseStart_446042 := by decide
  rcases family_descends (prefixWord ++ tailWord_446042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446080 : List Nat := [2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_446080 : Nat := 118140960795 + 446080 * 2 ^ 59
def prefixEnd_446080 : Nat := 4983230072969 + 3 ^ 40 * 446080 * 2
def baseEnd_446080 : Nat := 135735377989759966606531

theorem tailTrace_446080 : CollatzResearch.WordTrace tailWord_446080 prefixEnd_446080 135735377989759966606531 := by
  unfold tailWord_446080
  simp only [CollatzResearch.WordTrace]
  refine ⟨8134937111967909621879847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10846582815957212829173129 8134937111967909621879847)
  ·
    refine ⟨12202405667951864432819771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8134937111967909621879847 12202405667951864432819771)
    ·
      refine ⟨18303608501927796649229657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12202405667951864432819771 18303608501927796649229657)
      ·
        refine ⟨13727706376445847486922243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18303608501927796649229657 13727706376445847486922243)
        ·
          refine ⟨20591559564668771230383365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13727706376445847486922243 20591559564668771230383365)
          ·
            refine ⟨3860917418375394605696881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20591559564668771230383365 3860917418375394605696881)
            ·
              refine ⟨2895688063781545954272661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3860917418375394605696881 2895688063781545954272661)
              ·
                refine ⟨135735377989759966606531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2895688063781545954272661 135735377989759966606531)
                ·
                  rfl

theorem cell19_446080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_446080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446080 prefixEnd_446080 := by exact prefixLift 446080
  have htrace : WordTrace (prefixWord ++ tailWord_446080) baseStart_446080 baseEnd_446080 := by
    simpa [prefixWord, tailWord_446080, baseEnd_446080] using wordTrace_append hprefix tailTrace_446080
  have hstable : (prefixWord ++ tailWord_446080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446080).length < 2 ^ (prefixWord ++ tailWord_446080).sum := by decide
  have hdescent : baseEnd_446080 < baseStart_446080 := by decide
  rcases family_descends (prefixWord ++ tailWord_446080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446116 : List Nat := [2, 3, 1, 2, 2, 4, 5]
def baseStart_446116 : Nat := 118140960795 + 446116 * 2 ^ 59
def prefixEnd_446116 : Nat := 4983230072969 + 3 ^ 40 * 446116 * 2
def baseEnd_446116 : Nat := 45248777414574183268811

theorem tailTrace_446116 : CollatzResearch.WordTrace tailWord_446116 prefixEnd_446116 45248777414574183268811 := by
  unfold tailWord_446116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135593625902698696035101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10847458167870264928046801 8135593625902698696035101)
  ·
    refine ⟨3050847609713512011013163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8135593625902698696035101 3050847609713512011013163)
    ·
      refine ⟨4576271414570268016519745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3050847609713512011013163 4576271414570268016519745)
      ·
        refine ⟨3432203560927701012389809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4576271414570268016519745 3432203560927701012389809)
        ·
          refine ⟨2574152670695775759292357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3432203560927701012389809 2574152670695775759292357)
          ·
            refine ⟨482653625755457954867317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2574152670695775759292357 482653625755457954867317)
            ·
              refine ⟨45248777414574183268811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 482653625755457954867317 45248777414574183268811)
              ·
                rfl

theorem cell19_446116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_446116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446116 prefixEnd_446116 := by exact prefixLift 446116
  have htrace : WordTrace (prefixWord ++ tailWord_446116) baseStart_446116 baseEnd_446116 := by
    simpa [prefixWord, tailWord_446116, baseEnd_446116] using wordTrace_append hprefix tailTrace_446116
  have hstable : (prefixWord ++ tailWord_446116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446116).length < 2 ^ (prefixWord ++ tailWord_446116).sum := by decide
  have hdescent : baseEnd_446116 < baseStart_446116 := by decide
  rcases family_descends (prefixWord ++ tailWord_446116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446133 : List Nat := [1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_446133 : Nat := 118140960795 + 446133 * 2 ^ 59
def prefixEnd_446133 : Nat := 4983230072969 + 3 ^ 40 * 446133 * 2
def baseEnd_446133 : Nat := 135751505085871547428609

theorem tailTrace_446133 : CollatzResearch.WordTrace tailWord_446133 prefixEnd_446133 135751505085871547428609 := by
  unfold tailWord_446133
  simp only [CollatzResearch.WordTrace]
  refine ⟨16271807292743809295439053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10847871528495872863626035 16271807292743809295439053)
  ·
    refine ⟨6101927734778928485789645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16271807292743809295439053 6101927734778928485789645)
    ·
      refine ⟨2288222900542098182171117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6101927734778928485789645 2288222900542098182171117)
      ·
        refine ⟨858083587703286818314169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2288222900542098182171117 858083587703286818314169)
        ·
          refine ⟨643562690777465113735627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858083587703286818314169 643562690777465113735627)
          ·
            refine ⟨965344036166197670603441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643562690777465113735627 965344036166197670603441)
            ·
              refine ⟨724008027124648252952581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965344036166197670603441 724008027124648252952581)
              ·
                refine ⟨135751505085871547428609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 724008027124648252952581 135751505085871547428609)
                ·
                  rfl

theorem cell19_446133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_446133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446133 prefixEnd_446133 := by exact prefixLift 446133
  have htrace : WordTrace (prefixWord ++ tailWord_446133) baseStart_446133 baseEnd_446133 := by
    simpa [prefixWord, tailWord_446133, baseEnd_446133] using wordTrace_append hprefix tailTrace_446133
  have hstable : (prefixWord ++ tailWord_446133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446133).length < 2 ^ (prefixWord ++ tailWord_446133).sum := by decide
  have hdescent : baseEnd_446133 < baseStart_446133 := by decide
  rcases family_descends (prefixWord ++ tailWord_446133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446135 : List Nat := [1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_446135 : Nat := 118140960795 + 446135 * 2 ^ 59
def prefixEnd_446135 : Nat := 4983230072969 + 3 ^ 40 * 446135 * 2
def baseEnd_446135 : Nat := 135752113655536135384159

theorem tailTrace_446135 : CollatzResearch.WordTrace tailWord_446135 prefixEnd_446135 135752113655536135384159 := by
  unfold tailWord_446135
  simp only [CollatzResearch.WordTrace]
  refine ⟨16271880238736563637011859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10847920159157709091341239 16271880238736563637011859)
  ·
    refine ⟨24407820358104845455517789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16271880238736563637011859 24407820358104845455517789)
    ·
      refine ⟨9152932634289317045819171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24407820358104845455517789 9152932634289317045819171)
      ·
        refine ⟨13729398951433975568728757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9152932634289317045819171 13729398951433975568728757)
        ·
          refine ⟨1287131151696935209568321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13729398951433975568728757 1287131151696935209568321)
          ·
            refine ⟨965348363772701407176241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287131151696935209568321 965348363772701407176241)
            ·
              refine ⟨724011272829526055382181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965348363772701407176241 724011272829526055382181)
              ·
                refine ⟨135752113655536135384159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 724011272829526055382181 135752113655536135384159)
                ·
                  rfl

theorem cell19_446135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_446135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446135 prefixEnd_446135 := by exact prefixLift 446135
  have htrace : WordTrace (prefixWord ++ tailWord_446135) baseStart_446135 baseEnd_446135 := by
    simpa [prefixWord, tailWord_446135, baseEnd_446135] using wordTrace_append hprefix tailTrace_446135
  have hstable : (prefixWord ++ tailWord_446135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446135).length < 2 ^ (prefixWord ++ tailWord_446135).sum := by decide
  have hdescent : baseEnd_446135 < baseStart_446135 := by decide
  rcases family_descends (prefixWord ++ tailWord_446135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446137 : List Nat := [1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_446137 : Nat := 118140960795 + 446137 * 2 ^ 59
def prefixEnd_446137 : Nat := 4983230072969 + 3 ^ 40 * 446137 * 2
def baseEnd_446137 : Nat := 135752722225200723339709

theorem tailTrace_446137 : CollatzResearch.WordTrace tailWord_446137 prefixEnd_446137 135752722225200723339709 := by
  unfold tailWord_446137
  simp only [CollatzResearch.WordTrace]
  refine ⟨16271953184729317978584665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10847968789819545319056443 16271953184729317978584665)
  ·
    refine ⟨12203964888546988483938499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16271953184729317978584665 12203964888546988483938499)
    ·
      refine ⟨18305947332820482725907749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12203964888546988483938499 18305947332820482725907749)
      ·
        refine ⟨3432365124903840511107703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18305947332820482725907749 3432365124903840511107703)
        ·
          refine ⟨5148547687355760766661555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3432365124903840511107703 5148547687355760766661555)
          ·
            refine ⟨7722821531033641149992333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5148547687355760766661555 7722821531033641149992333)
            ·
              refine ⟨2896058074137615431247125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7722821531033641149992333 2896058074137615431247125)
              ·
                refine ⟨135752722225200723339709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2896058074137615431247125 135752722225200723339709)
                ·
                  rfl

theorem cell19_446137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_446137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446137 prefixEnd_446137 := by exact prefixLift 446137
  have htrace : WordTrace (prefixWord ++ tailWord_446137) baseStart_446137 baseEnd_446137 := by
    simpa [prefixWord, tailWord_446137, baseEnd_446137] using wordTrace_append hprefix tailTrace_446137
  have hstable : (prefixWord ++ tailWord_446137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446137).length < 2 ^ (prefixWord ++ tailWord_446137).sum := by decide
  have hdescent : baseEnd_446137 < baseStart_446137 := by decide
  rcases family_descends (prefixWord ++ tailWord_446137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446150 : List Nat := [6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_446150 : Nat := 118140960795 + 446150 * 2 ^ 59
def prefixEnd_446150 : Nat := 4983230072969 + 3 ^ 40 * 446150 * 2
def baseEnd_446150 : Nat := 135756677928020545050785

theorem tailTrace_446150 : CollatzResearch.WordTrace tailWord_446150 prefixEnd_446150 135756677928020545050785 := by
  unfold tailWord_446150
  simp only [CollatzResearch.WordTrace]
  refine ⟨508513354177569412462747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10848284889121480799205269 508513354177569412462747)
  ·
    refine ⟨762770031266354118694121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 508513354177569412462747 762770031266354118694121)
    ·
      refine ⟨572077523449765589020591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 762770031266354118694121 572077523449765589020591)
      ·
        refine ⟨858116285174648383530887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572077523449765589020591 858116285174648383530887)
        ·
          refine ⟨1287174427761972575296331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858116285174648383530887 1287174427761972575296331)
          ·
            refine ⟨1930761641642958862944497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287174427761972575296331 1930761641642958862944497)
            ·
              refine ⟨1448071231232219147208373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1930761641642958862944497 1448071231232219147208373)
              ·
                refine ⟨135756677928020545050785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1448071231232219147208373 135756677928020545050785)
                ·
                  rfl

theorem cell19_446150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_446150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446150 prefixEnd_446150 := by exact prefixLift 446150
  have htrace : WordTrace (prefixWord ++ tailWord_446150) baseStart_446150 baseEnd_446150 := by
    simpa [prefixWord, tailWord_446150, baseEnd_446150] using wordTrace_append hprefix tailTrace_446150
  have hstable : (prefixWord ++ tailWord_446150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446150).length < 2 ^ (prefixWord ++ tailWord_446150).sum := by decide
  have hdescent : baseEnd_446150 < baseStart_446150 := by decide
  rcases family_descends (prefixWord ++ tailWord_446150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446173 : List Nat := [1, 4, 3, 3, 8]
def baseStart_446173 : Nat := 118140960795 + 446173 * 2 ^ 59
def prefixEnd_446173 : Nat := 4983230072969 + 3 ^ 40 * 446173 * 2
def baseEnd_446173 : Nat := 5028284314043085427393

theorem tailTrace_446173 : CollatzResearch.WordTrace tailWord_446173 prefixEnd_446173 5028284314043085427393 := by
  unfold tailWord_446173
  simp only [CollatzResearch.WordTrace]
  refine ⟨16273266212598896126895173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10848844141732597417930115 16273266212598896126895173)
  ·
    refine ⟨3051237414862293023792845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16273266212598896126895173 3051237414862293023792845)
    ·
      refine ⟨1144214030573359883922317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3051237414862293023792845 1144214030573359883922317)
      ·
        refine ⟨429080261465009956470869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1144214030573359883922317 429080261465009956470869)
        ·
          refine ⟨5028284314043085427393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 429080261465009956470869 5028284314043085427393)
          ·
            rfl

theorem cell19_446173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 8].length) (baseStart_446173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446173 prefixEnd_446173 := by exact prefixLift 446173
  have htrace : WordTrace (prefixWord ++ tailWord_446173) baseStart_446173 baseEnd_446173 := by
    simpa [prefixWord, tailWord_446173, baseEnd_446173] using wordTrace_append hprefix tailTrace_446173
  have hstable : (prefixWord ++ tailWord_446173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446173).length < 2 ^ (prefixWord ++ tailWord_446173).sum := by decide
  have hdescent : baseEnd_446173 < baseStart_446173 := by decide
  rcases family_descends (prefixWord ++ tailWord_446173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446266 : List Nat := [3, 1, 1, 1, 5, 3, 2, 3]
def baseStart_446266 : Nat := 118140960795 + 446266 * 2 ^ 59
def prefixEnd_446266 : Nat := 4983230072969 + 3 ^ 40 * 446266 * 2
def baseEnd_446266 : Nat := 135791974968566646472691

theorem tailTrace_446266 : CollatzResearch.WordTrace tailWord_446266 prefixEnd_446266 135791974968566646472691 := by
  unfold tailWord_446266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069164550315493252507663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10851105467507982006687101 4069164550315493252507663)
  ·
    refine ⟨6103746825473239878761495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4069164550315493252507663 6103746825473239878761495)
    ·
      refine ⟨9155620238209859818142243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6103746825473239878761495 9155620238209859818142243)
      ·
        refine ⟨13733430357314789727213365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9155620238209859818142243 13733430357314789727213365)
        ·
          refine ⟨1287509095998261536926253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13733430357314789727213365 1287509095998261536926253)
          ·
            refine ⟨482815910999348076347345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1287509095998261536926253 482815910999348076347345)
            ·
              refine ⟨362111933249511057260509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482815910999348076347345 362111933249511057260509)
              ·
                refine ⟨135791974968566646472691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362111933249511057260509 135791974968566646472691)
                ·
                  rfl

theorem cell19_446266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_446266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446266 prefixEnd_446266 := by exact prefixLift 446266
  have htrace : WordTrace (prefixWord ++ tailWord_446266) baseStart_446266 baseEnd_446266 := by
    simpa [prefixWord, tailWord_446266, baseEnd_446266] using wordTrace_append hprefix tailTrace_446266
  have hstable : (prefixWord ++ tailWord_446266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446266).length < 2 ^ (prefixWord ++ tailWord_446266).sum := by decide
  have hdescent : baseEnd_446266 < baseStart_446266 := by decide
  rcases family_descends (prefixWord ++ tailWord_446266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446268 : List Nat := [2, 2, 2, 2, 1, 1, 6, 3]
def baseStart_446268 : Nat := 118140960795 + 446268 * 2 ^ 59
def prefixEnd_446268 : Nat := 4983230072969 + 3 ^ 40 * 446268 * 2
def baseEnd_446268 : Nat := 135792583538231234428241

theorem tailTrace_446268 : CollatzResearch.WordTrace tailWord_446268 prefixEnd_446268 135792583538231234428241 := by
  unfold tailWord_446268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138365573627363675801729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10851154098169818234402305 8138365573627363675801729)
  ·
    refine ⟨6103774180220522756851297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8138365573627363675801729 6103774180220522756851297)
    ·
      refine ⟨4577830635165392067638473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6103774180220522756851297 4577830635165392067638473)
      ·
        refine ⟨3433372976374044050728855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4577830635165392067638473 3433372976374044050728855)
        ·
          refine ⟨5150059464561066076093283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433372976374044050728855 5150059464561066076093283)
          ·
            refine ⟨7725089196841599114139925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150059464561066076093283 7725089196841599114139925)
            ·
              refine ⟨362113556101949958475309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7725089196841599114139925 362113556101949958475309)
              ·
                refine ⟨135792583538231234428241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362113556101949958475309 135792583538231234428241)
                ·
                  rfl

theorem cell19_446268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_446268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446268 prefixEnd_446268 := by exact prefixLift 446268
  have htrace : WordTrace (prefixWord ++ tailWord_446268) baseStart_446268 baseEnd_446268 := by
    simpa [prefixWord, tailWord_446268, baseEnd_446268] using wordTrace_append hprefix tailTrace_446268
  have hstable : (prefixWord ++ tailWord_446268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446268).length < 2 ^ (prefixWord ++ tailWord_446268).sum := by decide
  have hdescent : baseEnd_446268 < baseStart_446268 := by decide
  rcases family_descends (prefixWord ++ tailWord_446268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446285 : List Nat := [1, 6, 1, 2, 1, 3, 5]
def baseStart_446285 : Nat := 118140960795 + 446285 * 2 ^ 59
def prefixEnd_446285 : Nat := 4983230072969 + 3 ^ 40 * 446285 * 2
def baseEnd_446285 : Nat := 45265918793460077350139

theorem tailTrace_446285 : CollatzResearch.WordTrace tailWord_446285 prefixEnd_446285 45265918793460077350139 := by
  unfold tailWord_446285
  simp only [CollatzResearch.WordTrace]
  refine ⟨16277351188193139254972309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10851567458795426169981539 16277351188193139254972309)
  ·
    refine ⟨763000836946553402576827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16277351188193139254972309 763000836946553402576827)
    ·
      refine ⟨1144501255419830103865241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763000836946553402576827 1144501255419830103865241)
      ·
        refine ⟨858375941564872577898931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1144501255419830103865241 858375941564872577898931)
        ·
          refine ⟨1287563912347308866848397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858375941564872577898931 1287563912347308866848397)
          ·
            refine ⟨482836467130240825068149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1287563912347308866848397 482836467130240825068149)
            ·
              refine ⟨45265918793460077350139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 482836467130240825068149 45265918793460077350139)
              ·
                rfl

theorem cell19_446285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_446285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446285 prefixEnd_446285 := by exact prefixLift 446285
  have htrace : WordTrace (prefixWord ++ tailWord_446285) baseStart_446285 baseEnd_446285 := by
    simpa [prefixWord, tailWord_446285, baseEnd_446285] using wordTrace_append hprefix tailTrace_446285
  have hstable : (prefixWord ++ tailWord_446285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446285).length < 2 ^ (prefixWord ++ tailWord_446285).sum := by decide
  have hdescent : baseEnd_446285 < baseStart_446285 := by decide
  rcases family_descends (prefixWord ++ tailWord_446285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446289 : List Nat := [1, 2, 2, 1, 5, 1, 7]
def baseStart_446289 : Nat := 118140960795 + 446289 * 2 ^ 59
def prefixEnd_446289 : Nat := 4983230072969 + 3 ^ 40 * 446289 * 2
def baseEnd_446289 : Nat := 45266324506569802653839

theorem tailTrace_446289 : CollatzResearch.WordTrace tailWord_446289 prefixEnd_446289 45266324506569802653839 := by
  unfold tailWord_446289
  simp only [CollatzResearch.WordTrace]
  refine ⟨16277497080178647938117921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10851664720119098625411947 16277497080178647938117921)
  ·
    refine ⟨12208122810133985953588441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16277497080178647938117921 12208122810133985953588441)
    ·
      refine ⟨9156092107600489465191331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12208122810133985953588441 9156092107600489465191331)
      ·
        refine ⟨13734138161400734197786997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9156092107600489465191331 13734138161400734197786997)
        ·
          refine ⟨1287575452631318831042531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13734138161400734197786997 1287575452631318831042531)
          ·
            refine ⟨1931363178946978246563797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287575452631318831042531 1931363178946978246563797)
            ·
              refine ⟨45266324506569802653839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1931363178946978246563797 45266324506569802653839)
              ·
                rfl

theorem cell19_446289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_446289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446289 prefixEnd_446289 := by exact prefixLift 446289
  have htrace : WordTrace (prefixWord ++ tailWord_446289) baseStart_446289 baseEnd_446289 := by
    simpa [prefixWord, tailWord_446289, baseEnd_446289] using wordTrace_append hprefix tailTrace_446289
  have hstable : (prefixWord ++ tailWord_446289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446289).length < 2 ^ (prefixWord ++ tailWord_446289).sum := by decide
  have hdescent : baseEnd_446289 < baseStart_446289 := by decide
  rcases family_descends (prefixWord ++ tailWord_446289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446306 : List Nat := [3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_446306 : Nat := 118140960795 + 446306 * 2 ^ 59
def prefixEnd_446306 : Nat := 4983230072969 + 3 ^ 40 * 446306 * 2
def baseEnd_446306 : Nat := 135804146361858405583693

theorem tailTrace_446306 : CollatzResearch.WordTrace tailWord_446306 prefixEnd_446306 135804146361858405583693 := by
  unfold tailWord_446306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069529280279264960371693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10852078080744706560991181 4069529280279264960371693)
  ·
    refine ⟨1526073480104724360139385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4069529280279264960371693 1526073480104724360139385)
    ·
      refine ⟨1144555110078543270104539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1526073480104724360139385 1144555110078543270104539)
      ·
        refine ⟨1716832665117814905156809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144555110078543270104539 1716832665117814905156809)
        ·
          refine ⟨1287624498838361178867607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716832665117814905156809 1287624498838361178867607)
          ·
            refine ⟨1931436748257541768301411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287624498838361178867607 1931436748257541768301411)
            ·
              refine ⟨2897155122386312652452117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931436748257541768301411 2897155122386312652452117)
              ·
                refine ⟨135804146361858405583693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2897155122386312652452117 135804146361858405583693)
                ·
                  rfl

theorem cell19_446306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_446306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446306 prefixEnd_446306 := by exact prefixLift 446306
  have htrace : WordTrace (prefixWord ++ tailWord_446306) baseStart_446306 baseEnd_446306 := by
    simpa [prefixWord, tailWord_446306, baseEnd_446306] using wordTrace_append hprefix tailTrace_446306
  have hstable : (prefixWord ++ tailWord_446306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446306).length < 2 ^ (prefixWord ++ tailWord_446306).sum := by decide
  have hdescent : baseEnd_446306 < baseStart_446306 := by decide
  rcases family_descends (prefixWord ++ tailWord_446306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446344 : List Nat := [2, 1, 3, 3, 4, 6]
def baseStart_446344 : Nat := 118140960795 + 446344 * 2 ^ 59
def prefixEnd_446344 : Nat := 4983230072969 + 3 ^ 40 * 446344 * 2
def baseEnd_446344 : Nat := 15090634353942841859905

theorem tailTrace_446344 : CollatzResearch.WordTrace tailWord_446344 prefixEnd_446344 15090634353942841859905 := by
  unfold tailWord_446344
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139751547489696165685043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10853002063319594887580057 8139751547489696165685043)
  ·
    refine ⟨12209627321234544248527565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8139751547489696165685043 12209627321234544248527565)
    ·
      refine ⟨4578610245462954093197837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12209627321234544248527565 4578610245462954093197837)
      ·
        refine ⟨1716978842048607784949189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4578610245462954093197837 1716978842048607784949189)
        ·
          refine ⟨321933532884113959677973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1716978842048607784949189 321933532884113959677973)
          ·
            refine ⟨15090634353942841859905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 321933532884113959677973 15090634353942841859905)
            ·
              rfl

theorem cell19_446344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 6].length) (baseStart_446344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446344 prefixEnd_446344 := by exact prefixLift 446344
  have htrace : WordTrace (prefixWord ++ tailWord_446344) baseStart_446344 baseEnd_446344 := by
    simpa [prefixWord, tailWord_446344, baseEnd_446344] using wordTrace_append hprefix tailTrace_446344
  have hstable : (prefixWord ++ tailWord_446344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446344).length < 2 ^ (prefixWord ++ tailWord_446344).sum := by decide
  have hdescent : baseEnd_446344 < baseStart_446344 := by decide
  rcases family_descends (prefixWord ++ tailWord_446344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446346 : List Nat := [3, 1, 2, 4, 9]
def baseStart_446346 : Nat := 118140960795 + 446346 * 2 ^ 59
def prefixEnd_446346 : Nat := 4983230072969 + 3 ^ 40 * 446346 * 2
def baseEnd_446346 : Nat := 5030233990931487581285

theorem tailTrace_446346 : CollatzResearch.WordTrace tailWord_446346 prefixEnd_446346 5030233990931487581285 := by
  unfold tailWord_446346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069894010243036668235723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10853050693981431115295261 4069894010243036668235723)
  ·
    refine ⟨6104841015364555002353585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4069894010243036668235723 6104841015364555002353585)
    ·
      refine ⟨4578630761523416251765189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6104841015364555002353585 4578630761523416251765189)
      ·
        refine ⟨858493267785640547205973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4578630761523416251765189 858493267785640547205973)
        ·
          refine ⟨5030233990931487581285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 858493267785640547205973 5030233990931487581285)
          ·
            rfl

theorem cell19_446346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 9].length) (baseStart_446346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446346 prefixEnd_446346 := by exact prefixLift 446346
  have htrace : WordTrace (prefixWord ++ tailWord_446346) baseStart_446346 baseEnd_446346 := by
    simpa [prefixWord, tailWord_446346, baseEnd_446346] using wordTrace_append hprefix tailTrace_446346
  have hstable : (prefixWord ++ tailWord_446346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446346).length < 2 ^ (prefixWord ++ tailWord_446346).sum := by decide
  have hdescent : baseEnd_446346 < baseStart_446346 := by decide
  rcases family_descends (prefixWord ++ tailWord_446346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446439 : List Nat := [1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_446439 : Nat := 118140960795 + 446439 * 2 ^ 59
def prefixEnd_446439 : Nat := 4983230072969 + 3 ^ 40 * 446439 * 2
def baseEnd_446439 : Nat := 135844616244553504627775

theorem tailTrace_446439 : CollatzResearch.WordTrace tailWord_446439 prefixEnd_446439 135844616244553504627775 := by
  unfold tailWord_446439
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282968029635223556078371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10855312019756815704052247 16282968029635223556078371)
  ·
    refine ⟨24424452044452835334117557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16282968029635223556078371 24424452044452835334117557)
    ·
      refine ⟨2289792379167453312573521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24424452044452835334117557 2289792379167453312573521)
      ·
        refine ⟨1717344284375589984430141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2289792379167453312573521 1717344284375589984430141)
        ·
          refine ⟨644004106640846244161303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1717344284375589984430141 644004106640846244161303)
          ·
            refine ⟨966006159961269366241955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644004106640846244161303 966006159961269366241955)
            ·
              refine ⟨1449009239941904049362933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966006159961269366241955 1449009239941904049362933)
              ·
                refine ⟨135844616244553504627775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1449009239941904049362933 135844616244553504627775)
                ·
                  rfl

theorem cell19_446439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_446439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446439 prefixEnd_446439 := by exact prefixLift 446439
  have htrace : WordTrace (prefixWord ++ tailWord_446439) baseStart_446439 baseEnd_446439 := by
    simpa [prefixWord, tailWord_446439, baseEnd_446439] using wordTrace_append hprefix tailTrace_446439
  have hstable : (prefixWord ++ tailWord_446439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446439).length < 2 ^ (prefixWord ++ tailWord_446439).sum := by decide
  have hdescent : baseEnd_446439 < baseStart_446439 := by decide
  rcases family_descends (prefixWord ++ tailWord_446439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446498 : List Nat := [3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_446498 : Nat := 118140960795 + 446498 * 2 ^ 59
def prefixEnd_446498 : Nat := 4983230072969 + 3 ^ 40 * 446498 * 2
def baseEnd_446498 : Nat := 135862569049658849316503

theorem tailTrace_446498 : CollatzResearch.WordTrace tailWord_446498 prefixEnd_446498 135862569049658849316503 := by
  unfold tailWord_446498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071279984105369158119037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10856746624280984421650765 4071279984105369158119037)
  ·
    refine ⟨1526729994039513434294639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4071279984105369158119037 1526729994039513434294639)
    ·
      refine ⟨2290094991059270151441959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526729994039513434294639 2290094991059270151441959)
      ·
        refine ⟨3435142486588905227162939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290094991059270151441959 3435142486588905227162939)
        ·
          refine ⟨5152713729883357840744409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435142486588905227162939 5152713729883357840744409)
          ·
            refine ⟨3864535297412518380558307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5152713729883357840744409 3864535297412518380558307)
            ·
              refine ⟨5796802946118777570837461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864535297412518380558307 5796802946118777570837461)
              ·
                refine ⟨135862569049658849316503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5796802946118777570837461 135862569049658849316503)
                ·
                  rfl

theorem cell19_446498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_446498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446498 prefixEnd_446498 := by exact prefixLift 446498
  have htrace : WordTrace (prefixWord ++ tailWord_446498) baseStart_446498 baseEnd_446498 := by
    simpa [prefixWord, tailWord_446498, baseEnd_446498] using wordTrace_append hprefix tailTrace_446498
  have hstable : (prefixWord ++ tailWord_446498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446498).length < 2 ^ (prefixWord ++ tailWord_446498).sum := by decide
  have hdescent : baseEnd_446498 < baseStart_446498 := by decide
  rcases family_descends (prefixWord ++ tailWord_446498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446574 : List Nat := [4, 1, 2, 2, 1, 1, 8]
def baseStart_446574 : Nat := 118140960795 + 446574 * 2 ^ 59
def prefixEnd_446574 : Nat := 4983230072969 + 3 ^ 40 * 446574 * 2
def baseEnd_446574 : Nat := 45295231565637730542469

theorem tailTrace_446574 : CollatzResearch.WordTrace tailWord_446574 prefixEnd_446574 45295231565637730542469 := by
  unfold tailWord_446574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035986485518267701530347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10858594589430761074828517 2035986485518267701530347)
  ·
    refine ⟨3053979728277401552295521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2035986485518267701530347 3053979728277401552295521)
    ·
      refine ⟨2290484796208051164221641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3053979728277401552295521 2290484796208051164221641)
      ·
        refine ⟨1717863597156038373166231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2290484796208051164221641 1717863597156038373166231)
        ·
          refine ⟨2576795395734057559749347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717863597156038373166231 2576795395734057559749347)
          ·
            refine ⟨3865193093601086339624021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576795395734057559749347 3865193093601086339624021)
            ·
              refine ⟨45295231565637730542469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3865193093601086339624021 45295231565637730542469)
              ·
                rfl

theorem cell19_446574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_446574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446574 prefixEnd_446574 := by exact prefixLift 446574
  have htrace : WordTrace (prefixWord ++ tailWord_446574) baseStart_446574 baseEnd_446574 := by
    simpa [prefixWord, tailWord_446574, baseEnd_446574] using wordTrace_append hprefix tailTrace_446574
  have hstable : (prefixWord ++ tailWord_446574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446574).length < 2 ^ (prefixWord ++ tailWord_446574).sum := by decide
  have hdescent : baseEnd_446574 < baseStart_446574 := by decide
  rcases family_descends (prefixWord ++ tailWord_446574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446606 : List Nat := [4, 1, 1, 3, 4, 1, 2, 3]
def baseStart_446606 : Nat := 118140960795 + 446606 * 2 ^ 59
def prefixEnd_446606 : Nat := 4983230072969 + 3 ^ 40 * 446606 * 2
def baseEnd_446606 : Nat := 135895431811546598916209

theorem tailTrace_446606 : CollatzResearch.WordTrace tailWord_446606 prefixEnd_446606 135895431811546598916209 := by
  unfold tailWord_446606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036132377503776384675959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10859372680020140718271781 2036132377503776384675959)
  ·
    refine ⟨3054198566255664577013939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2036132377503776384675959 3054198566255664577013939)
    ·
      refine ⟨4581297849383496865520909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3054198566255664577013939 4581297849383496865520909)
      ·
        refine ⟨1717986693518811324570341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4581297849383496865520909 1717986693518811324570341)
        ·
          refine ⟨322122505034777123356939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1717986693518811324570341 322122505034777123356939)
          ·
            refine ⟨483183757552165685035409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322122505034777123356939 483183757552165685035409)
            ·
              refine ⟨362387818164124263776557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483183757552165685035409 362387818164124263776557)
              ·
                refine ⟨135895431811546598916209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362387818164124263776557 135895431811546598916209)
                ·
                  rfl

theorem cell19_446606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_446606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446606 prefixEnd_446606 := by exact prefixLift 446606
  have htrace : WordTrace (prefixWord ++ tailWord_446606) baseStart_446606 baseEnd_446606 := by
    simpa [prefixWord, tailWord_446606, baseEnd_446606] using wordTrace_append hprefix tailTrace_446606
  have hstable : (prefixWord ++ tailWord_446606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446606).length < 2 ^ (prefixWord ++ tailWord_446606).sum := by decide
  have hdescent : baseEnd_446606 < baseStart_446606 := by decide
  rcases family_descends (prefixWord ++ tailWord_446606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446671 : List Nat := [1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_446671 : Nat := 118140960795 + 446671 * 2 ^ 59
def prefixEnd_446671 : Nat := 4983230072969 + 3 ^ 40 * 446671 * 2
def baseEnd_446671 : Nat := 135915210325645707471587

theorem tailTrace_446671 : CollatzResearch.WordTrace tailWord_446671 prefixEnd_446671 135915210325645707471587 := by
  unfold tailWord_446671
  simp only [CollatzResearch.WordTrace]
  refine ⟨16291429764794727178523867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10860953176529818119015911 16291429764794727178523867)
  ·
    refine ⟨24437144647192090767785801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16291429764794727178523867 24437144647192090767785801)
    ·
      refine ⟨18327858485394068075839351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24437144647192090767785801 18327858485394068075839351)
      ·
        refine ⟨27491787728091102113759027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18327858485394068075839351 27491787728091102113759027)
        ·
          refine ⟨41237681592136653170638541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27491787728091102113759027 41237681592136653170638541)
          ·
            refine ⟨15464130597051244938989453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41237681592136653170638541 15464130597051244938989453)
            ·
              refine ⟨5799048973894216852121045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15464130597051244938989453 5799048973894216852121045)
              ·
                refine ⟨135915210325645707471587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5799048973894216852121045 135915210325645707471587)
                ·
                  rfl

theorem cell19_446671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_446671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446671 prefixEnd_446671 := by exact prefixLift 446671
  have htrace : WordTrace (prefixWord ++ tailWord_446671) baseStart_446671 baseEnd_446671 := by
    simpa [prefixWord, tailWord_446671, baseEnd_446671] using wordTrace_append hprefix tailTrace_446671
  have hstable : (prefixWord ++ tailWord_446671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446671).length < 2 ^ (prefixWord ++ tailWord_446671).sum := by decide
  have hdescent : baseEnd_446671 < baseStart_446671 := by decide
  rcases family_descends (prefixWord ++ tailWord_446671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446684 : List Nat := [2, 2, 5, 2, 2, 6]
def baseStart_446684 : Nat := 118140960795 + 446684 * 2 ^ 59
def prefixEnd_446684 : Nat := 4983230072969 + 3 ^ 40 * 446684 * 2
def baseEnd_446684 : Nat := 15102129558718392131407

theorem tailTrace_446684 : CollatzResearch.WordTrace tailWord_446684 prefixEnd_446684 15102129558718392131407 := by
  unfold tailWord_446684
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145951956873815199373553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10861269275831753599164737 8145951956873815199373553)
  ·
    refine ⟨6109463967655361399530165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8145951956873815199373553 6109463967655361399530165)
    ·
      refine ⟨572762246967690131205953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6109463967655361399530165 572762246967690131205953)
      ·
        refine ⟨429571685225767598404465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572762246967690131205953 429571685225767598404465)
        ·
          refine ⟨322178763919325698803349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429571685225767598404465 322178763919325698803349)
          ·
            refine ⟨15102129558718392131407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 322178763919325698803349 15102129558718392131407)
            ·
              rfl

theorem cell19_446684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 6].length) (baseStart_446684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446684 prefixEnd_446684 := by exact prefixLift 446684
  have htrace : WordTrace (prefixWord ++ tailWord_446684) baseStart_446684 baseEnd_446684 := by
    simpa [prefixWord, tailWord_446684, baseEnd_446684] using wordTrace_append hprefix tailTrace_446684
  have hstable : (prefixWord ++ tailWord_446684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446684).length < 2 ^ (prefixWord ++ tailWord_446684).sum := by decide
  have hdescent : baseEnd_446684 < baseStart_446684 := by decide
  rcases family_descends (prefixWord ++ tailWord_446684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446722 : List Nat := [3, 4, 1, 1, 2, 2, 3, 3]
def baseStart_446722 : Nat := 118140960795 + 446722 * 2 ^ 59
def prefixEnd_446722 : Nat := 4983230072969 + 3 ^ 40 * 446722 * 2
def baseEnd_446722 : Nat := 135930728852092700338115

theorem tailTrace_446722 : CollatzResearch.WordTrace tailWord_446722 prefixEnd_446722 135930728852092700338115 := by
  unfold tailWord_446722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073322471902490722157605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10862193258406641925753613 4073322471902490722157605)
  ·
    refine ⟨763747963481717010404551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4073322471902490722157605 763747963481717010404551)
    ·
      refine ⟨1145621945222575515606827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763747963481717010404551 1145621945222575515606827)
      ·
        refine ⟨1718432917833863273410241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145621945222575515606827 1718432917833863273410241)
        ·
          refine ⟨1288824688375397455057681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1718432917833863273410241 1288824688375397455057681)
          ·
            refine ⟨966618516281548091293261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288824688375397455057681 966618516281548091293261)
            ·
              refine ⟨362481943605580534234973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 966618516281548091293261 362481943605580534234973)
              ·
                refine ⟨135930728852092700338115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362481943605580534234973 135930728852092700338115)
                ·
                  rfl

theorem cell19_446722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_446722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446722 prefixEnd_446722 := by exact prefixLift 446722
  have htrace : WordTrace (prefixWord ++ tailWord_446722) baseStart_446722 baseEnd_446722 := by
    simpa [prefixWord, tailWord_446722, baseEnd_446722] using wordTrace_append hprefix tailTrace_446722
  have hstable : (prefixWord ++ tailWord_446722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446722).length < 2 ^ (prefixWord ++ tailWord_446722).sum := by decide
  have hdescent : baseEnd_446722 < baseStart_446722 := by decide
  rcases family_descends (prefixWord ++ tailWord_446722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446821 : List Nat := [1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_446821 : Nat := 118140960795 + 446821 * 2 ^ 59
def prefixEnd_446821 : Nat := 4983230072969 + 3 ^ 40 * 446821 * 2
def baseEnd_446821 : Nat := 135960853050489804137845

theorem tailTrace_446821 : CollatzResearch.WordTrace tailWord_446821 prefixEnd_446821 135960853050489804137845 := by
  unfold tailWord_446821
  simp only [CollatzResearch.WordTrace]
  refine ⟨16296900714251302796484317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10864600476167535197656211 16296900714251302796484317)
  ·
    refine ⟨6111337767844238548681619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16296900714251302796484317 6111337767844238548681619)
    ·
      refine ⟨9167006651766357823022429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6111337767844238548681619 9167006651766357823022429)
      ·
        refine ⟨3437627494412384183633411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9167006651766357823022429 3437627494412384183633411)
        ·
          refine ⟨5156441241618576275450117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437627494412384183633411 5156441241618576275450117)
          ·
            refine ⟨966832732803483051646897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5156441241618576275450117 966832732803483051646897)
            ·
              refine ⟨725124549602612288735173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966832732803483051646897 725124549602612288735173)
              ·
                refine ⟨135960853050489804137845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 725124549602612288735173 135960853050489804137845)
                ·
                  rfl

theorem cell19_446821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_446821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446821 prefixEnd_446821 := by exact prefixLift 446821
  have htrace : WordTrace (prefixWord ++ tailWord_446821) baseStart_446821 baseEnd_446821 := by
    simpa [prefixWord, tailWord_446821, baseEnd_446821] using wordTrace_append hprefix tailTrace_446821
  have hstable : (prefixWord ++ tailWord_446821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446821).length < 2 ^ (prefixWord ++ tailWord_446821).sum := by decide
  have hdescent : baseEnd_446821 < baseStart_446821 := by decide
  rcases family_descends (prefixWord ++ tailWord_446821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446870 : List Nat := [5, 3, 1, 2, 1, 2, 1, 4]
def baseStart_446870 : Nat := 118140960795 + 446870 * 2 ^ 59
def prefixEnd_446870 : Nat := 4983230072969 + 3 ^ 40 * 446870 * 2
def baseEnd_446870 : Nat := 135975763007272209048823

theorem tailTrace_446870 : CollatzResearch.WordTrace tailWord_446870 prefixEnd_446870 135975763007272209048823 := by
  unfold tailWord_446870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018667993192111510313629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10865791927382522776678709 1018667993192111510313629)
  ·
    refine ⟨382000497447041816367611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1018667993192111510313629 382000497447041816367611)
    ·
      refine ⟨573000746170562724551417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382000497447041816367611 573000746170562724551417)
      ·
        refine ⟨429750559627922043413563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573000746170562724551417 429750559627922043413563)
        ·
          refine ⟨644625839441883065120345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429750559627922043413563 644625839441883065120345)
          ·
            refine ⟨483469379581412298840259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644625839441883065120345 483469379581412298840259)
            ·
              refine ⟨725204069372118448260389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483469379581412298840259 725204069372118448260389)
              ·
                refine ⟨135975763007272209048823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 725204069372118448260389 135975763007272209048823)
                ·
                  rfl

theorem cell19_446870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_446870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446870 prefixEnd_446870 := by exact prefixLift 446870
  have htrace : WordTrace (prefixWord ++ tailWord_446870) baseStart_446870 baseEnd_446870 := by
    simpa [prefixWord, tailWord_446870, baseEnd_446870] using wordTrace_append hprefix tailTrace_446870
  have hstable : (prefixWord ++ tailWord_446870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446870).length < 2 ^ (prefixWord ++ tailWord_446870).sum := by decide
  have hdescent : baseEnd_446870 < baseStart_446870 := by decide
  rcases family_descends (prefixWord ++ tailWord_446870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446893 : List Nat := [1, 5, 2, 2, 2, 1, 3, 3]
def baseStart_446893 : Nat := 118140960795 + 446893 * 2 ^ 59
def prefixEnd_446893 : Nat := 4983230072969 + 3 ^ 40 * 446893 * 2
def baseEnd_446893 : Nat := 135982761558414970537649

theorem tailTrace_446893 : CollatzResearch.WordTrace tailWord_446893 prefixEnd_446893 135982761558414970537649 := by
  unfold tailWord_446893
  simp only [CollatzResearch.WordTrace]
  refine ⟨16299526769990459093105333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10866351179993639395403555 16299526769990459093105333)
  ·
    refine ⟨1528080634686605539978625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16299526769990459093105333 1528080634686605539978625)
    ·
      refine ⟨1146060476014954154983969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528080634686605539978625 1146060476014954154983969)
      ·
        refine ⟨859545357011215616237977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146060476014954154983969 859545357011215616237977)
        ·
          refine ⟨644659017758411712178483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859545357011215616237977 644659017758411712178483)
          ·
            refine ⟨966988526637617568267725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644659017758411712178483 966988526637617568267725)
            ·
              refine ⟨362620697489106588100397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 966988526637617568267725 362620697489106588100397)
              ·
                refine ⟨135982761558414970537649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362620697489106588100397 135982761558414970537649)
                ·
                  rfl

theorem cell19_446893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_446893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446893 prefixEnd_446893 := by exact prefixLift 446893
  have htrace : WordTrace (prefixWord ++ tailWord_446893) baseStart_446893 baseEnd_446893 := by
    simpa [prefixWord, tailWord_446893, baseEnd_446893] using wordTrace_append hprefix tailTrace_446893
  have hstable : (prefixWord ++ tailWord_446893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446893).length < 2 ^ (prefixWord ++ tailWord_446893).sum := by decide
  have hdescent : baseEnd_446893 < baseStart_446893 := by decide
  rcases family_descends (prefixWord ++ tailWord_446893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446937 : List Nat := [1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_446937 : Nat := 118140960795 + 446937 * 2 ^ 59
def prefixEnd_446937 : Nat := 4983230072969 + 3 ^ 40 * 446937 * 2
def baseEnd_446937 : Nat := 135996150091035905559751

theorem tailTrace_446937 : CollatzResearch.WordTrace tailWord_446937 prefixEnd_446937 135996150091035905559751 := by
  unfold tailWord_446937
  simp only [CollatzResearch.WordTrace]
  refine ⟨16301131581831054607707065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10867421054554036405138043 16301131581831054607707065)
  ·
    refine ⟨12225848686373290955780299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16301131581831054607707065 12225848686373290955780299)
    ·
      refine ⟨18338773029559936433670449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12225848686373290955780299 18338773029559936433670449)
      ·
        refine ⟨13754079772169952325252837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18338773029559936433670449 13754079772169952325252837)
        ·
          refine ⟨2578889957281866060984907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13754079772169952325252837 2578889957281866060984907)
          ·
            refine ⟨3868334935922799091477361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578889957281866060984907 3868334935922799091477361)
            ·
              refine ⟨2901251201942099318608021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3868334935922799091477361 2901251201942099318608021)
              ·
                refine ⟨135996150091035905559751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2901251201942099318608021 135996150091035905559751)
                ·
                  rfl

theorem cell19_446937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_446937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446937 prefixEnd_446937 := by exact prefixLift 446937
  have htrace : WordTrace (prefixWord ++ tailWord_446937) baseStart_446937 baseEnd_446937 := by
    simpa [prefixWord, tailWord_446937, baseEnd_446937] using wordTrace_append hprefix tailTrace_446937
  have hstable : (prefixWord ++ tailWord_446937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446937).length < 2 ^ (prefixWord ++ tailWord_446937).sum := by decide
  have hdescent : baseEnd_446937 < baseStart_446937 := by decide
  rcases family_descends (prefixWord ++ tailWord_446937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446946 : List Nat := [3, 3, 3, 2, 2, 1, 2, 3]
def baseStart_446946 : Nat := 118140960795 + 446946 * 2 ^ 59
def prefixEnd_446946 : Nat := 4983230072969 + 3 ^ 40 * 446946 * 2
def baseEnd_446946 : Nat := 135998888654526551359727

theorem tailTrace_446946 : CollatzResearch.WordTrace tailWord_446946 prefixEnd_446946 135998888654526551359727 := by
  unfold tailWord_446946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075364959699612286196173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10867639892532299429856461 4075364959699612286196173)
  ·
    refine ⟨1528261859887354607323565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4075364959699612286196173 1528261859887354607323565)
    ·
      refine ⟨573098197457757977746337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1528261859887354607323565 573098197457757977746337)
      ·
        refine ⟨429823648093318483309753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573098197457757977746337 429823648093318483309753)
        ·
          refine ⟨322367736069988862482315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429823648093318483309753 322367736069988862482315)
          ·
            refine ⟨483551604104983293723473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322367736069988862482315 483551604104983293723473)
            ·
              refine ⟨362663703078737470292605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483551604104983293723473 362663703078737470292605)
              ·
                refine ⟨135998888654526551359727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362663703078737470292605 135998888654526551359727)
                ·
                  rfl

theorem cell19_446946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_446946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446946 prefixEnd_446946 := by exact prefixLift 446946
  have htrace : WordTrace (prefixWord ++ tailWord_446946) baseStart_446946 baseEnd_446946 := by
    simpa [prefixWord, tailWord_446946, baseEnd_446946] using wordTrace_append hprefix tailTrace_446946
  have hstable : (prefixWord ++ tailWord_446946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446946).length < 2 ^ (prefixWord ++ tailWord_446946).sum := by decide
  have hdescent : baseEnd_446946 < baseStart_446946 := by decide
  rcases family_descends (prefixWord ++ tailWord_446946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446952 : List Nat := [2, 1, 4, 1, 1, 5, 2, 3]
def baseStart_446952 : Nat := 118140960795 + 446952 * 2 ^ 59
def prefixEnd_446952 : Nat := 4983230072969 + 3 ^ 40 * 446952 * 2
def baseEnd_446952 : Nat := 136000714363520315226377

theorem tailTrace_446952 : CollatzResearch.WordTrace tailWord_446952 prefixEnd_446952 136000714363520315226377 := by
  unfold tailWord_446952
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150839338388356084751555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10867785784517808113002073 8150839338388356084751555)
  ·
    refine ⟨12226259007582534127127333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8150839338388356084751555 12226259007582534127127333)
    ·
      refine ⟨2292423563921725148836375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12226259007582534127127333 2292423563921725148836375)
      ·
        refine ⟨3438635345882587723254563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292423563921725148836375 3438635345882587723254563)
        ·
          refine ⟨5157953018823881584881845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3438635345882587723254563 5157953018823881584881845)
          ·
            refine ⟨483558095514738898582673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5157953018823881584881845 483558095514738898582673)
            ·
              refine ⟨362668571636054173937005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483558095514738898582673 362668571636054173937005)
              ·
                refine ⟨136000714363520315226377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362668571636054173937005 136000714363520315226377)
                ·
                  rfl

theorem cell19_446952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_446952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446952 prefixEnd_446952 := by exact prefixLift 446952
  have htrace : WordTrace (prefixWord ++ tailWord_446952) baseStart_446952 baseEnd_446952 := by
    simpa [prefixWord, tailWord_446952, baseEnd_446952] using wordTrace_append hprefix tailTrace_446952
  have hstable : (prefixWord ++ tailWord_446952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446952).length < 2 ^ (prefixWord ++ tailWord_446952).sum := by decide
  have hdescent : baseEnd_446952 < baseStart_446952 := by decide
  rcases family_descends (prefixWord ++ tailWord_446952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446954 : List Nat := [3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_446954 : Nat := 118140960795 + 446954 * 2 ^ 59
def prefixEnd_446954 : Nat := 4983230072969 + 3 ^ 40 * 446954 * 2
def baseEnd_446954 : Nat := 136001322933184903181927

theorem tailTrace_446954 : CollatzResearch.WordTrace tailWord_446954 prefixEnd_446954 136001322933184903181927 := by
  unfold tailWord_446954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075437905692366627768979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10867834415179644340717277 4075437905692366627768979)
  ·
    refine ⟨6113156858538549941653469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4075437905692366627768979 6113156858538549941653469)
    ·
      refine ⟨2292433821951956228120051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6113156858538549941653469 2292433821951956228120051)
      ·
        refine ⟨3438650732927934342180077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292433821951956228120051 3438650732927934342180077)
        ·
          refine ⟨1289494024847975378317529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3438650732927934342180077 1289494024847975378317529)
          ·
            refine ⟨967120518635981533738147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289494024847975378317529 967120518635981533738147)
            ·
              refine ⟨1450680777953972300607221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967120518635981533738147 1450680777953972300607221)
              ·
                refine ⟨136001322933184903181927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1450680777953972300607221 136001322933184903181927)
                ·
                  rfl

theorem cell19_446954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_446954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446954 prefixEnd_446954 := by exact prefixLift 446954
  have htrace : WordTrace (prefixWord ++ tailWord_446954) baseStart_446954 baseEnd_446954 := by
    simpa [prefixWord, tailWord_446954, baseEnd_446954] using wordTrace_append hprefix tailTrace_446954
  have hstable : (prefixWord ++ tailWord_446954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446954).length < 2 ^ (prefixWord ++ tailWord_446954).sum := by decide
  have hdescent : baseEnd_446954 < baseStart_446954 := by decide
  rcases family_descends (prefixWord ++ tailWord_446954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446956 : List Nat := [2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_446956 : Nat := 118140960795 + 446956 * 2 ^ 59
def prefixEnd_446956 : Nat := 4983230072969 + 3 ^ 40 * 446956 * 2
def baseEnd_446956 : Nat := 136001931502849491137477

theorem tailTrace_446956 : CollatzResearch.WordTrace tailWord_446956 prefixEnd_446956 136001931502849491137477 := by
  unfold tailWord_446956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150912284381110426324361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10867883045841480568432481 8150912284381110426324361)
  ·
    refine ⟨6113184213285832819743271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8150912284381110426324361 6113184213285832819743271)
    ·
      refine ⟨9169776319928749229614907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6113184213285832819743271 9169776319928749229614907)
      ·
        refine ⟨13754664479893123844422361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9169776319928749229614907 13754664479893123844422361)
        ·
          refine ⟨10315998359919842883316771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13754664479893123844422361 10315998359919842883316771)
          ·
            refine ⟨15473997539879764324975157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10315998359919842883316771 15473997539879764324975157)
            ·
              refine ⟨1450687269363727905466421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15473997539879764324975157 1450687269363727905466421)
              ·
                refine ⟨136001931502849491137477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1450687269363727905466421 136001931502849491137477)
                ·
                  rfl

theorem cell19_446956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_446956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_446956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_446956 prefixEnd_446956 := by exact prefixLift 446956
  have htrace : WordTrace (prefixWord ++ tailWord_446956) baseStart_446956 baseEnd_446956 := by
    simpa [prefixWord, tailWord_446956, baseEnd_446956] using wordTrace_append hprefix tailTrace_446956
  have hstable : (prefixWord ++ tailWord_446956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446956).length < 2 ^ (prefixWord ++ tailWord_446956).sum := by decide
  have hdescent : baseEnd_446956 < baseStart_446956 := by decide
  rcases family_descends (prefixWord ++ tailWord_446956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447013 : List Nat := [1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_447013 : Nat := 118140960795 + 447013 * 2 ^ 59
def prefixEnd_447013 : Nat := 4983230072969 + 3 ^ 40 * 447013 * 2
def baseEnd_447013 : Nat := 136019275738290247870655

theorem tailTrace_447013 : CollatzResearch.WordTrace tailWord_447013 prefixEnd_447013 136019275738290247870655 := by
  unfold tailWord_447013
  simp only [CollatzResearch.WordTrace]
  refine ⟨16303903529555719587473693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10869269019703813058315795 16303903529555719587473693)
  ·
    refine ⟨6113963823583394845302635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16303903529555719587473693 6113963823583394845302635)
    ·
      refine ⟨9170945735375092267953953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6113963823583394845302635 9170945735375092267953953)
      ·
        refine ⟨6878209301531319200965465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9170945735375092267953953 6878209301531319200965465)
        ·
          refine ⟨5158656976148489400724099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6878209301531319200965465 5158656976148489400724099)
          ·
            refine ⟨7737985464222734101086149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158656976148489400724099 7737985464222734101086149)
            ·
              refine ⟨1450872274541762643953653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7737985464222734101086149 1450872274541762643953653)
              ·
                refine ⟨136019275738290247870655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1450872274541762643953653 136019275738290247870655)
                ·
                  rfl

theorem cell19_447013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_447013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447013 prefixEnd_447013 := by exact prefixLift 447013
  have htrace : WordTrace (prefixWord ++ tailWord_447013) baseStart_447013 baseEnd_447013 := by
    simpa [prefixWord, tailWord_447013, baseEnd_447013] using wordTrace_append hprefix tailTrace_447013
  have hstable : (prefixWord ++ tailWord_447013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447013).length < 2 ^ (prefixWord ++ tailWord_447013).sum := by decide
  have hdescent : baseEnd_447013 < baseStart_447013 := by decide
  rcases family_descends (prefixWord ++ tailWord_447013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447028 : List Nat := [2, 5, 1, 3, 1, 7]
def baseStart_447028 : Nat := 118140960795 + 447028 * 2 ^ 59
def prefixEnd_447028 : Nat := 4983230072969 + 3 ^ 40 * 447028 * 2
def baseEnd_447028 : Nat := 15113760001197184170809

theorem tailTrace_447028 : CollatzResearch.WordTrace tailWord_447028 prefixEnd_447028 15113760001197184170809 := by
  unfold tailWord_447028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8152225312250688574634869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10869633749667584766179825 8152225312250688574634869)
  ·
    refine ⟨764271123023502053872019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8152225312250688574634869 764271123023502053872019)
    ·
      refine ⟨1146406684535253080808029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764271123023502053872019 1146406684535253080808029)
      ·
        refine ⟨429902506700719905303011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1146406684535253080808029 429902506700719905303011)
        ·
          refine ⟨644853760051079857954517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429902506700719905303011 644853760051079857954517)
          ·
            refine ⟨15113760001197184170809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 644853760051079857954517 15113760001197184170809)
            ·
              rfl

theorem cell19_447028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 7].length) (baseStart_447028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447028 prefixEnd_447028 := by exact prefixLift 447028
  have htrace : WordTrace (prefixWord ++ tailWord_447028) baseStart_447028 baseEnd_447028 := by
    simpa [prefixWord, tailWord_447028, baseEnd_447028] using wordTrace_append hprefix tailTrace_447028
  have hstable : (prefixWord ++ tailWord_447028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447028).length < 2 ^ (prefixWord ++ tailWord_447028).sum := by decide
  have hdescent : baseEnd_447028 < baseStart_447028 := by decide
  rcases family_descends (prefixWord ++ tailWord_447028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447030 : List Nat := [5, 1, 2, 1, 2, 8]
def baseStart_447030 : Nat := 118140960795 + 447030 * 2 ^ 59
def prefixEnd_447030 : Nat := 4983230072969 + 3 ^ 40 * 447030 * 2
def baseEnd_447030 : Nat := 15113827620048805054759

theorem tailTrace_447030 : CollatzResearch.WordTrace tailWord_447030 prefixEnd_447030 15113827620048805054759 := by
  unfold tailWord_447030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019032723155883218177659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10869682380329420993895029 1019032723155883218177659)
  ·
    refine ⟨1528549084733824827266489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1019032723155883218177659 1528549084733824827266489)
    ·
      refine ⟨1146411813550368620449867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528549084733824827266489 1146411813550368620449867)
      ·
        refine ⟨1719617720325552930674801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146411813550368620449867 1719617720325552930674801)
        ·
          refine ⟨1289713290244164698006101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1719617720325552930674801 1289713290244164698006101)
          ·
            refine ⟨15113827620048805054759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1289713290244164698006101 15113827620048805054759)
            ·
              rfl

theorem cell19_447030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 8].length) (baseStart_447030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447030 prefixEnd_447030 := by exact prefixLift 447030
  have htrace : WordTrace (prefixWord ++ tailWord_447030) baseStart_447030 baseEnd_447030 := by
    simpa [prefixWord, tailWord_447030, baseEnd_447030] using wordTrace_append hprefix tailTrace_447030
  have hstable : (prefixWord ++ tailWord_447030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447030).length < 2 ^ (prefixWord ++ tailWord_447030).sum := by decide
  have hdescent : baseEnd_447030 < baseStart_447030 := by decide
  rcases family_descends (prefixWord ++ tailWord_447030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447051 : List Nat := [1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_447051 : Nat := 118140960795 + 447051 * 2 ^ 59
def prefixEnd_447051 : Nat := 4983230072969 + 3 ^ 40 * 447051 * 2
def baseEnd_447051 : Nat := 136030838561917419026107

theorem tailTrace_447051 : CollatzResearch.WordTrace tailWord_447051 prefixEnd_447051 136030838561917419026107 := by
  unfold tailWord_447051
  simp only [CollatzResearch.WordTrace]
  refine ⟨16305289503418052077357007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10870193002278701384904671 16305289503418052077357007)
  ·
    refine ⟨24457934255127078116035511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16305289503418052077357007 24457934255127078116035511)
    ·
      refine ⟨36686901382690617174053267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24457934255127078116035511 36686901382690617174053267)
      ·
        refine ⟨55030352074035925761079901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36686901382690617174053267 55030352074035925761079901)
        ·
          refine ⟨20636382027763472160404963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55030352074035925761079901 20636382027763472160404963)
          ·
            refine ⟨30954573041645208240607445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20636382027763472160404963 30954573041645208240607445)
            ·
              refine ⟨725497805663559568139237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30954573041645208240607445 725497805663559568139237)
              ·
                refine ⟨136030838561917419026107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 725497805663559568139237 136030838561917419026107)
                ·
                  rfl

theorem cell19_447051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_447051 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447051 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447051 prefixEnd_447051 := by exact prefixLift 447051
  have htrace : WordTrace (prefixWord ++ tailWord_447051) baseStart_447051 baseEnd_447051 := by
    simpa [prefixWord, tailWord_447051, baseEnd_447051] using wordTrace_append hprefix tailTrace_447051
  have hstable : (prefixWord ++ tailWord_447051).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447051).length < 2 ^ (prefixWord ++ tailWord_447051).sum := by decide
  have hdescent : baseEnd_447051 < baseStart_447051 := by decide
  rcases family_descends (prefixWord ++ tailWord_447051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447127 : List Nat := [1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_447127 : Nat := 118140960795 + 447127 * 2 ^ 59
def prefixEnd_447127 : Nat := 4983230072969 + 3 ^ 40 * 447127 * 2
def baseEnd_447127 : Nat := 136053964209171761337011

theorem tailTrace_447127 : CollatzResearch.WordTrace tailWord_447127 prefixEnd_447127 136053964209171761337011 := by
  unfold tailWord_447127
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308061451142717057123635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10872040967428478038082423 16308061451142717057123635)
  ·
    refine ⟨24462092176714075585685453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16308061451142717057123635 24462092176714075585685453)
    ·
      refine ⟨9173284566267778344632045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24462092176714075585685453 9173284566267778344632045)
      ·
        refine ⟨3439981712350416879237017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9173284566267778344632045 3439981712350416879237017)
        ·
          refine ⟨2579986284262812659427763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3439981712350416879237017 2579986284262812659427763)
          ·
            refine ⟨3869979426394218989141645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579986284262812659427763 3869979426394218989141645)
            ·
              refine ⟨1451242284897832120928117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3869979426394218989141645 1451242284897832120928117)
              ·
                refine ⟨136053964209171761337011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1451242284897832120928117 136053964209171761337011)
                ·
                  rfl

theorem cell19_447127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_447127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447127 prefixEnd_447127 := by exact prefixLift 447127
  have htrace : WordTrace (prefixWord ++ tailWord_447127) baseStart_447127 baseEnd_447127 := by
    simpa [prefixWord, tailWord_447127, baseEnd_447127] using wordTrace_append hprefix tailTrace_447127
  have hstable : (prefixWord ++ tailWord_447127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447127).length < 2 ^ (prefixWord ++ tailWord_447127).sum := by decide
  have hdescent : baseEnd_447127 < baseStart_447127 := by decide
  rcases family_descends (prefixWord ++ tailWord_447127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447165 : List Nat := [1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_447165 : Nat := 118140960795 + 447165 * 2 ^ 59
def prefixEnd_447165 : Nat := 4983230072969 + 3 ^ 40 * 447165 * 2
def baseEnd_447165 : Nat := 136065527032798932492463

theorem tailTrace_447165 : CollatzResearch.WordTrace tailWord_447165 prefixEnd_447165 136065527032798932492463 := by
  unfold tailWord_447165
  simp only [CollatzResearch.WordTrace]
  refine ⟨16309447425005049547006949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10872964950003366364671299 16309447425005049547006949)
  ·
    refine ⟨3058021392188446790063803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16309447425005049547006949 3058021392188446790063803)
    ·
      refine ⟨4587032088282670185095705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3058021392188446790063803 4587032088282670185095705)
      ·
        refine ⟨3440274066212002638821779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4587032088282670185095705 3440274066212002638821779)
        ·
          refine ⟨5160411099318003958232669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440274066212002638821779 5160411099318003958232669)
          ·
            refine ⟨1935154162244251484337251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5160411099318003958232669 1935154162244251484337251)
            ·
              refine ⟨2902731243366377226505877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935154162244251484337251 2902731243366377226505877)
              ·
                refine ⟨136065527032798932492463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2902731243366377226505877 136065527032798932492463)
                ·
                  rfl

theorem cell19_447165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_447165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447165 prefixEnd_447165 := by exact prefixLift 447165
  have htrace : WordTrace (prefixWord ++ tailWord_447165) baseStart_447165 baseEnd_447165 := by
    simpa [prefixWord, tailWord_447165, baseEnd_447165] using wordTrace_append hprefix tailTrace_447165
  have hstable : (prefixWord ++ tailWord_447165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447165).length < 2 ^ (prefixWord ++ tailWord_447165).sum := by decide
  have hdescent : baseEnd_447165 < baseStart_447165 := by decide
  rcases family_descends (prefixWord ++ tailWord_447165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447203 : List Nat := [1, 1, 1, 7, 1, 8]
def baseStart_447203 : Nat := 118140960795 + 447203 * 2 ^ 59
def prefixEnd_447203 : Nat := 4983230072969 + 3 ^ 40 * 447203 * 2
def baseEnd_447203 : Nat := 15119676650714011516435

theorem tailTrace_447203 : CollatzResearch.WordTrace tailWord_447203 prefixEnd_447203 15119676650714011516435 := by
  unfold tailWord_447203
  simp only [CollatzResearch.WordTrace]
  refine ⟨16310833398867382036890263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10873888932578254691260175 16310833398867382036890263)
  ·
    refine ⟨24466250098301073055335395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16310833398867382036890263 24466250098301073055335395)
    ·
      refine ⟨36699375147451609583003093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24466250098301073055335395 36699375147451609583003093)
      ·
        refine ⟨860141605018397099601635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36699375147451609583003093 860141605018397099601635)
        ·
          refine ⟨1290212407527595649402453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860141605018397099601635 1290212407527595649402453)
          ·
            refine ⟨15119676650714011516435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1290212407527595649402453 15119676650714011516435)
            ·
              rfl

theorem cell19_447203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 8].length) (baseStart_447203 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447203 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447203 prefixEnd_447203 := by exact prefixLift 447203
  have htrace : WordTrace (prefixWord ++ tailWord_447203) baseStart_447203 baseEnd_447203 := by
    simpa [prefixWord, tailWord_447203, baseEnd_447203] using wordTrace_append hprefix tailTrace_447203
  have hstable : (prefixWord ++ tailWord_447203).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447203).length < 2 ^ (prefixWord ++ tailWord_447203).sum := by decide
  have hdescent : baseEnd_447203 < baseStart_447203 := by decide
  rcases family_descends (prefixWord ++ tailWord_447203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447260 : List Nat := [2, 2, 3, 1, 1, 4, 6]
def baseStart_447260 : Nat := 118140960795 + 447260 * 2 ^ 59
def prefixEnd_447260 : Nat := 4983230072969 + 3 ^ 40 * 447260 * 2
def baseEnd_447260 : Nat := 45364811363955620127031

theorem tailTrace_447260 : CollatzResearch.WordTrace tailWord_447260 prefixEnd_447260 45364811363955620127031 := by
  unfold tailWord_447260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156456179830440385857617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10875274906440587181143489 8156456179830440385857617)
  ·
    refine ⟨6117342134872830289393213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8156456179830440385857617 6117342134872830289393213)
    ·
      refine ⟨2294003300577311358522455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6117342134872830289393213 2294003300577311358522455)
      ·
        refine ⟨3441004950865967037783683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294003300577311358522455 3441004950865967037783683)
        ·
          refine ⟨5161507426298950556675525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441004950865967037783683 5161507426298950556675525)
          ·
            refine ⟨967782642431053229376661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5161507426298950556675525 967782642431053229376661)
            ·
              refine ⟨45364811363955620127031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 967782642431053229376661 45364811363955620127031)
              ·
                rfl

theorem cell19_447260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_447260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447260 prefixEnd_447260 := by exact prefixLift 447260
  have htrace : WordTrace (prefixWord ++ tailWord_447260) baseStart_447260 baseEnd_447260 := by
    simpa [prefixWord, tailWord_447260, baseEnd_447260] using wordTrace_append hprefix tailTrace_447260
  have hstable : (prefixWord ++ tailWord_447260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447260).length < 2 ^ (prefixWord ++ tailWord_447260).sum := by decide
  have hdescent : baseEnd_447260 < baseStart_447260 := by decide
  rcases family_descends (prefixWord ++ tailWord_447260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447336 : List Nat := [2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_447336 : Nat := 118140960795 + 447336 * 2 ^ 59
def prefixEnd_447336 : Nat := 4983230072969 + 3 ^ 40 * 447336 * 2
def baseEnd_447336 : Nat := 136117559739121202691997

theorem tailTrace_447336 : CollatzResearch.WordTrace tailWord_447336 prefixEnd_447336 136117559739121202691997 := by
  unfold tailWord_447336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157842153692772875740931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10877122871590363834321241 8157842153692772875740931)
  ·
    refine ⟨12236763230539159313611397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8157842153692772875740931 12236763230539159313611397)
    ·
      refine ⟨2294393105726092371302137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12236763230539159313611397 2294393105726092371302137)
      ·
        refine ⟨1720794829294569278476603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2294393105726092371302137 1720794829294569278476603)
        ·
          refine ⟨2581192243941853917714905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720794829294569278476603 2581192243941853917714905)
          ·
            refine ⟨1935894182956390438286179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2581192243941853917714905 1935894182956390438286179)
            ·
              refine ⟨2903841274434585657429269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935894182956390438286179 2903841274434585657429269)
              ·
                refine ⟨136117559739121202691997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2903841274434585657429269 136117559739121202691997)
                ·
                  rfl

theorem cell19_447336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_447336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447336 prefixEnd_447336 := by exact prefixLift 447336
  have htrace : WordTrace (prefixWord ++ tailWord_447336) baseStart_447336 baseEnd_447336 := by
    simpa [prefixWord, tailWord_447336, baseEnd_447336] using wordTrace_append hprefix tailTrace_447336
  have hstable : (prefixWord ++ tailWord_447336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447336).length < 2 ^ (prefixWord ++ tailWord_447336).sum := by decide
  have hdescent : baseEnd_447336 < baseStart_447336 := by decide
  rcases family_descends (prefixWord ++ tailWord_447336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447391 : List Nat := [1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_447391 : Nat := 118140960795 + 447391 * 2 ^ 59
def prefixEnd_447391 : Nat := 4983230072969 + 3 ^ 40 * 447391 * 2
def baseEnd_447391 : Nat := 136134295404897371469625

theorem tailTrace_447391 : CollatzResearch.WordTrace tailWord_447391 prefixEnd_447391 136134295404897371469625 := by
  unfold tailWord_447391
  simp only [CollatzResearch.WordTrace]
  refine ⟨16317690322186290144734027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10878460214790860096489351 16317690322186290144734027)
  ·
    refine ⟨24476535483279435217101041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16317690322186290144734027 24476535483279435217101041)
    ·
      refine ⟨18357401612459576412825781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24476535483279435217101041 18357401612459576412825781)
      ·
        refine ⟨1721006401168085288702417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18357401612459576412825781 1721006401168085288702417)
        ·
          refine ⟨1290754800876063966526813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721006401168085288702417 1290754800876063966526813)
          ·
            refine ⟨484033050328523987447555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1290754800876063966526813 484033050328523987447555)
            ·
              refine ⟨726049575492785981171333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484033050328523987447555 726049575492785981171333)
              ·
                refine ⟨136134295404897371469625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726049575492785981171333 136134295404897371469625)
                ·
                  rfl

theorem cell19_447391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_447391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447391 prefixEnd_447391 := by exact prefixLift 447391
  have htrace : WordTrace (prefixWord ++ tailWord_447391) baseStart_447391 baseEnd_447391 := by
    simpa [prefixWord, tailWord_447391, baseEnd_447391] using wordTrace_append hprefix tailTrace_447391
  have hstable : (prefixWord ++ tailWord_447391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447391).length < 2 ^ (prefixWord ++ tailWord_447391).sum := by decide
  have hdescent : baseEnd_447391 < baseStart_447391 := by decide
  rcases family_descends (prefixWord ++ tailWord_447391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447583 : List Nat := [1, 1, 2, 3, 1, 1, 7, 3]
def baseStart_447583 : Nat := 118140960795 + 447583 * 2 ^ 59
def prefixEnd_447583 : Nat := 4983230072969 + 3 ^ 40 * 447583 * 2
def baseEnd_447583 : Nat := 136192718092697815202435

theorem tailTrace_447583 : CollatzResearch.WordTrace tailWord_447583 prefixEnd_447583 136192718092697815202435 := by
  unfold tailWord_447583
  simp only [CollatzResearch.WordTrace]
  refine ⟨16324693137490706935723403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10883128758327137957148935 16324693137490706935723403)
  ·
    refine ⟨24487039706236060403585105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16324693137490706935723403 24487039706236060403585105)
    ·
      refine ⟨18365279779677045302688829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24487039706236060403585105 18365279779677045302688829)
      ·
        refine ⟨6886979917378891988508311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18365279779677045302688829 6886979917378891988508311)
        ·
          refine ⟨10330469876068337982762467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6886979917378891988508311 10330469876068337982762467)
          ·
            refine ⟨15495704814102506974143701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10330469876068337982762467 15495704814102506974143701)
            ·
              refine ⟨363180581580527507206493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15495704814102506974143701 363180581580527507206493)
              ·
                refine ⟨136192718092697815202435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363180581580527507206493 136192718092697815202435)
                ·
                  rfl

theorem cell19_447583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_447583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447583 prefixEnd_447583 := by exact prefixLift 447583
  have htrace : WordTrace (prefixWord ++ tailWord_447583) baseStart_447583 baseEnd_447583 := by
    simpa [prefixWord, tailWord_447583, baseEnd_447583] using wordTrace_append hprefix tailTrace_447583
  have hstable : (prefixWord ++ tailWord_447583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447583).length < 2 ^ (prefixWord ++ tailWord_447583).sum := by decide
  have hdescent : baseEnd_447583 < baseStart_447583 := by decide
  rcases family_descends (prefixWord ++ tailWord_447583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447585 : List Nat := [1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_447585 : Nat := 118140960795 + 447585 * 2 ^ 59
def prefixEnd_447585 : Nat := 4983230072969 + 3 ^ 40 * 447585 * 2
def baseEnd_447585 : Nat := 136193326662362403157985

theorem tailTrace_447585 : CollatzResearch.WordTrace tailWord_447585 prefixEnd_447585 136193326662362403157985 := by
  unfold tailWord_447585
  simp only [CollatzResearch.WordTrace]
  refine ⟨16324766083483461277296209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10883177388988974184864139 16324766083483461277296209)
  ·
    refine ⟨12243574562612595957972157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16324766083483461277296209 12243574562612595957972157)
    ·
      refine ⟨4591340460979723484239559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12243574562612595957972157 4591340460979723484239559)
      ·
        refine ⟨6887010691469585226359339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591340460979723484239559 6887010691469585226359339)
        ·
          refine ⟨10330516037204377839539009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887010691469585226359339 10330516037204377839539009)
          ·
            refine ⟨7747887027903283379654257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10330516037204377839539009 7747887027903283379654257)
            ·
              refine ⟨5810915270927462534740693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7747887027903283379654257 5810915270927462534740693)
              ·
                refine ⟨136193326662362403157985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5810915270927462534740693 136193326662362403157985)
                ·
                  rfl

theorem cell19_447585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_447585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447585 prefixEnd_447585 := by exact prefixLift 447585
  have htrace : WordTrace (prefixWord ++ tailWord_447585) baseStart_447585 baseEnd_447585 := by
    simpa [prefixWord, tailWord_447585, baseEnd_447585] using wordTrace_append hprefix tailTrace_447585
  have hstable : (prefixWord ++ tailWord_447585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447585).length < 2 ^ (prefixWord ++ tailWord_447585).sum := by decide
  have hdescent : baseEnd_447585 < baseStart_447585 := by decide
  rcases family_descends (prefixWord ++ tailWord_447585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447623 : List Nat := [1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_447623 : Nat := 118140960795 + 447623 * 2 ^ 59
def prefixEnd_447623 : Nat := 4983230072969 + 3 ^ 40 * 447623 * 2
def baseEnd_447623 : Nat := 136204889485989574313437

theorem tailTrace_447623 : CollatzResearch.WordTrace tailWord_447623 prefixEnd_447623 136204889485989574313437 := by
  unfold tailWord_447623
  simp only [CollatzResearch.WordTrace]
  refine ⟨16326152057345793767179523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10884101371563862511453015 16326152057345793767179523)
  ·
    refine ⟨24489228086018690650769285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16326152057345793767179523 24489228086018690650769285)
    ·
      refine ⟨4591730266128504497019241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24489228086018690650769285 4591730266128504497019241)
      ·
        refine ⟨3443797699596378372764431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4591730266128504497019241 3443797699596378372764431)
        ·
          refine ⟨5165696549394567559146647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443797699596378372764431 5165696549394567559146647)
          ·
            refine ⟨7748544824091851338719971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165696549394567559146647 7748544824091851338719971)
            ·
              refine ⟨11622817236137777008079957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748544824091851338719971 11622817236137777008079957)
              ·
                refine ⟨136204889485989574313437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11622817236137777008079957 136204889485989574313437)
                ·
                  rfl

theorem cell19_447623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_447623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447623 prefixEnd_447623 := by exact prefixLift 447623
  have htrace : WordTrace (prefixWord ++ tailWord_447623) baseStart_447623 baseEnd_447623 := by
    simpa [prefixWord, tailWord_447623, baseEnd_447623] using wordTrace_append hprefix tailTrace_447623
  have hstable : (prefixWord ++ tailWord_447623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447623).length < 2 ^ (prefixWord ++ tailWord_447623).sum := by decide
  have hdescent : baseEnd_447623 < baseStart_447623 := by decide
  rcases family_descends (prefixWord ++ tailWord_447623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447640 : List Nat := [2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_447640 : Nat := 118140960795 + 447640 * 2 ^ 59
def prefixEnd_447640 : Nat := 4983230072969 + 3 ^ 40 * 447640 * 2
def baseEnd_447640 : Nat := 136210062328138571935613

theorem tailTrace_447640 : CollatzResearch.WordTrace tailWord_447640 prefixEnd_447640 136210062328138571935613 := by
  unfold tailWord_447640
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163386049142102835274187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10884514732189470447032249 8163386049142102835274187)
  ·
    refine ⟨12245079073713154252911281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163386049142102835274187 12245079073713154252911281)
    ·
      refine ⟨9183809305284865689683461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12245079073713154252911281 9183809305284865689683461)
      ·
        refine ⟨1721964244740912316815649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9183809305284865689683461 1721964244740912316815649)
        ·
          refine ⟨1291473183555684237611737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721964244740912316815649 1291473183555684237611737)
          ·
            refine ⟨968604887666763178208803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291473183555684237611737 968604887666763178208803)
            ·
              refine ⟨1452907331500144767313205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968604887666763178208803 1452907331500144767313205)
              ·
                refine ⟨136210062328138571935613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1452907331500144767313205 136210062328138571935613)
                ·
                  rfl

theorem cell19_447640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_447640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447640 prefixEnd_447640 := by exact prefixLift 447640
  have htrace : WordTrace (prefixWord ++ tailWord_447640) baseStart_447640 baseEnd_447640 := by
    simpa [prefixWord, tailWord_447640, baseEnd_447640] using wordTrace_append hprefix tailTrace_447640
  have hstable : (prefixWord ++ tailWord_447640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447640).length < 2 ^ (prefixWord ++ tailWord_447640).sum := by decide
  have hdescent : baseEnd_447640 < baseStart_447640 := by decide
  rcases family_descends (prefixWord ++ tailWord_447640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447678 : List Nat := [4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_447678 : Nat := 118140960795 + 447678 * 2 ^ 59
def prefixEnd_447678 : Nat := 4983230072969 + 3 ^ 40 * 447678 * 2
def baseEnd_447678 : Nat := 136221625151765743091065

theorem tailTrace_447678 : CollatzResearch.WordTrace tailWord_447678 prefixEnd_447678 136221625151765743091065 := by
  unfold tailWord_447678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041019759018317270053961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10885438714764358773621125 2041019759018317270053961)
  ·
    refine ⟨1530764819263737952540471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2041019759018317270053961 1530764819263737952540471)
    ·
      refine ⟨2296147228895606928810707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530764819263737952540471 2296147228895606928810707)
      ·
        refine ⟨3444220843343410393216061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296147228895606928810707 3444220843343410393216061)
        ·
          refine ⟨1291582816253778897456023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3444220843343410393216061 1291582816253778897456023)
          ·
            refine ⟨1937374224380668346184035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291582816253778897456023 1937374224380668346184035)
            ·
              refine ⟨2906061336571002519276053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937374224380668346184035 2906061336571002519276053)
              ·
                refine ⟨136221625151765743091065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2906061336571002519276053 136221625151765743091065)
                ·
                  rfl

theorem cell19_447678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_447678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447678 prefixEnd_447678 := by exact prefixLift 447678
  have htrace : WordTrace (prefixWord ++ tailWord_447678) baseStart_447678 baseEnd_447678 := by
    simpa [prefixWord, tailWord_447678, baseEnd_447678] using wordTrace_append hprefix tailTrace_447678
  have hstable : (prefixWord ++ tailWord_447678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447678).length < 2 ^ (prefixWord ++ tailWord_447678).sum := by decide
  have hdescent : baseEnd_447678 < baseStart_447678 := by decide
  rcases family_descends (prefixWord ++ tailWord_447678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447752 : List Nat := [2, 1, 3, 2, 4, 1, 3, 3]
def baseStart_447752 : Nat := 118140960795 + 447752 * 2 ^ 59
def prefixEnd_447752 : Nat := 4983230072969 + 3 ^ 40 * 447752 * 2
def baseEnd_447752 : Nat := 136244142229355497446419

theorem tailTrace_447752 : CollatzResearch.WordTrace tailWord_447752 prefixEnd_447752 136244142229355497446419 := by
  unfold tailWord_447752
  simp only [CollatzResearch.WordTrace]
  refine ⟨8165428536939224399312755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10887238049252299199083673 8165428536939224399312755)
  ·
    refine ⟨12248142805408836598969133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8165428536939224399312755 12248142805408836598969133)
    ·
      refine ⟨4593053552028313724613425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12248142805408836598969133 4593053552028313724613425)
      ·
        refine ⟨3444790164021235293460069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4593053552028313724613425 3444790164021235293460069)
        ·
          refine ⟨645898155753981617523763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3444790164021235293460069 645898155753981617523763)
          ·
            refine ⟨968847233630972426285645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645898155753981617523763 968847233630972426285645)
            ·
              refine ⟨363317712611614659857117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 968847233630972426285645 363317712611614659857117)
              ·
                refine ⟨136244142229355497446419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363317712611614659857117 136244142229355497446419)
                ·
                  rfl

theorem cell19_447752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_447752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447752 prefixEnd_447752 := by exact prefixLift 447752
  have htrace : WordTrace (prefixWord ++ tailWord_447752) baseStart_447752 baseEnd_447752 := by
    simpa [prefixWord, tailWord_447752, baseEnd_447752] using wordTrace_append hprefix tailTrace_447752
  have hstable : (prefixWord ++ tailWord_447752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447752).length < 2 ^ (prefixWord ++ tailWord_447752).sum := by decide
  have hdescent : baseEnd_447752 < baseStart_447752 := by decide
  rcases family_descends (prefixWord ++ tailWord_447752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447773 : List Nat := [1, 4, 2, 3, 1, 2, 6]
def baseStart_447773 : Nat := 118140960795 + 447773 * 2 ^ 59
def prefixEnd_447773 : Nat := 4983230072969 + 3 ^ 40 * 447773 * 2
def baseEnd_447773 : Nat := 45416844070277890326565

theorem tailTrace_447773 : CollatzResearch.WordTrace tailWord_447773 prefixEnd_447773 45416844070277890326565 := by
  unfold tailWord_447773
  simp only [CollatzResearch.WordTrace]
  refine ⟨16331623006802369385139973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10887748671201579590093315 16331623006802369385139973)
  ·
    refine ⟨3062179313775444259713745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16331623006802369385139973 3062179313775444259713745)
    ·
      refine ⟨2296634485331583194785309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3062179313775444259713745 2296634485331583194785309)
      ·
        refine ⟨861237931999343698044491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2296634485331583194785309 861237931999343698044491)
        ·
          refine ⟨1291856897999015547066737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861237931999343698044491 1291856897999015547066737)
          ·
            refine ⟨968892673499261660300053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291856897999015547066737 968892673499261660300053)
            ·
              refine ⟨45416844070277890326565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 968892673499261660300053 45416844070277890326565)
              ·
                rfl

theorem cell19_447773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_447773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447773 prefixEnd_447773 := by exact prefixLift 447773
  have htrace : WordTrace (prefixWord ++ tailWord_447773) baseStart_447773 baseEnd_447773 := by
    simpa [prefixWord, tailWord_447773, baseEnd_447773] using wordTrace_append hprefix tailTrace_447773
  have hstable : (prefixWord ++ tailWord_447773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447773).length < 2 ^ (prefixWord ++ tailWord_447773).sum := by decide
  have hdescent : baseEnd_447773 < baseStart_447773 := by decide
  rcases family_descends (prefixWord ++ tailWord_447773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447805 : List Nat := [1, 4, 1, 5, 2, 1, 2, 3]
def baseStart_447805 : Nat := 118140960795 + 447805 * 2 ^ 59
def prefixEnd_447805 : Nat := 4983230072969 + 3 ^ 40 * 447805 * 2
def baseEnd_447805 : Nat := 136260269325467078268497

theorem tailTrace_447805 : CollatzResearch.WordTrace tailWord_447805 prefixEnd_447805 136260269325467078268497 := by
  unfold tailWord_447805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16332790142686438850304869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10888526761790959233536579 16332790142686438850304869)
  ·
    refine ⟨3062398151753707284432163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16332790142686438850304869 3062398151753707284432163)
    ·
      refine ⟨4593597227630560926648245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3062398151753707284432163 4593597227630560926648245)
      ·
        refine ⟨430649740090365086873273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4593597227630560926648245 430649740090365086873273)
        ·
          refine ⟨322987305067773815154955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430649740090365086873273 322987305067773815154955)
          ·
            refine ⟨484480957601660722732433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322987305067773815154955 484480957601660722732433)
            ·
              refine ⟨363360718201245542049325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484480957601660722732433 363360718201245542049325)
              ·
                refine ⟨136260269325467078268497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363360718201245542049325 136260269325467078268497)
                ·
                  rfl

theorem cell19_447805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 3].length) (baseStart_447805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447805 prefixEnd_447805 := by exact prefixLift 447805
  have htrace : WordTrace (prefixWord ++ tailWord_447805) baseStart_447805 baseEnd_447805 := by
    simpa [prefixWord, tailWord_447805, baseEnd_447805] using wordTrace_append hprefix tailTrace_447805
  have hstable : (prefixWord ++ tailWord_447805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447805).length < 2 ^ (prefixWord ++ tailWord_447805).sum := by decide
  have hdescent : baseEnd_447805 < baseStart_447805 := by decide
  rcases family_descends (prefixWord ++ tailWord_447805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447809 : List Nat := [1, 2, 5, 2, 1, 1, 4, 3]
def baseStart_447809 : Nat := 118140960795 + 447809 * 2 ^ 59
def prefixEnd_447809 : Nat := 4983230072969 + 3 ^ 40 * 447809 * 2
def baseEnd_447809 : Nat := 136261486464796254179597

theorem tailTrace_447809 : CollatzResearch.WordTrace tailWord_447809 prefixEnd_447809 136261486464796254179597 := by
  unfold tailWord_447809
  simp only [CollatzResearch.WordTrace]
  refine ⟨16332936034671947533450481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10888624023114631688966987 16332936034671947533450481)
  ·
    refine ⟨12249702026003960650087861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16332936034671947533450481 12249702026003960650087861)
    ·
      refine ⟨1148409564937871310945737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12249702026003960650087861 1148409564937871310945737)
      ·
        refine ⟨861307173703403483209303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148409564937871310945737 861307173703403483209303)
        ·
          refine ⟨1291960760555105224813955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861307173703403483209303 1291960760555105224813955)
          ·
            refine ⟨1937941140832657837220933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291960760555105224813955 1937941140832657837220933)
            ·
              refine ⟨363363963906123344478925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1937941140832657837220933 363363963906123344478925)
              ·
                refine ⟨136261486464796254179597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363363963906123344478925 136261486464796254179597)
                ·
                  rfl

theorem cell19_447809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_447809 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447809 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447809 prefixEnd_447809 := by exact prefixLift 447809
  have htrace : WordTrace (prefixWord ++ tailWord_447809) baseStart_447809 baseEnd_447809 := by
    simpa [prefixWord, tailWord_447809, baseEnd_447809] using wordTrace_append hprefix tailTrace_447809
  have hstable : (prefixWord ++ tailWord_447809).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447809).length < 2 ^ (prefixWord ++ tailWord_447809).sum := by decide
  have hdescent : baseEnd_447809 < baseStart_447809 := by decide
  rcases family_descends (prefixWord ++ tailWord_447809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447902 : List Nat := [4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_447902 : Nat := 118140960795 + 447902 * 2 ^ 59
def prefixEnd_447902 : Nat := 4983230072969 + 3 ^ 40 * 447902 * 2
def baseEnd_447902 : Nat := 136289784954199594112677

theorem tailTrace_447902 : CollatzResearch.WordTrace tailWord_447902 prefixEnd_447902 136289784954199594112677 := by
  unfold tailWord_447902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042041002916878052073245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10890885348890016277723973 2042041002916878052073245)
  ·
    refine ⟨765765376093829269527467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2042041002916878052073245 765765376093829269527467)
    ·
      refine ⟨1148648064140743904291201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765765376093829269527467 1148648064140743904291201)
      ·
        refine ⟨861486048105557928218401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148648064140743904291201 861486048105557928218401)
        ·
          refine ⟨646114536079168446163801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861486048105557928218401 646114536079168446163801)
          ·
            refine ⟨484585902059376334622851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646114536079168446163801 484585902059376334622851)
            ·
              refine ⟨726878853089064501934277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484585902059376334622851 726878853089064501934277)
              ·
                refine ⟨136289784954199594112677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726878853089064501934277 136289784954199594112677)
                ·
                  rfl

theorem cell19_447902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_447902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447902 prefixEnd_447902 := by exact prefixLift 447902
  have htrace : WordTrace (prefixWord ++ tailWord_447902) baseStart_447902 baseEnd_447902 := by
    simpa [prefixWord, tailWord_447902, baseEnd_447902] using wordTrace_append hprefix tailTrace_447902
  have hstable : (prefixWord ++ tailWord_447902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447902).length < 2 ^ (prefixWord ++ tailWord_447902).sum := by decide
  have hdescent : baseEnd_447902 < baseStart_447902 := by decide
  rcases family_descends (prefixWord ++ tailWord_447902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447906 : List Nat := [3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_447906 : Nat := 118140960795 + 447906 * 2 ^ 59
def prefixEnd_447906 : Nat := 4983230072969 + 3 ^ 40 * 447906 * 2
def baseEnd_447906 : Nat := 136291002093528770023777

theorem tailTrace_447906 : CollatzResearch.WordTrace tailWord_447906 prefixEnd_447906 136291002093528770023777 := by
  unfold tailWord_447906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084118478830133274932893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10890982610213688733154381 4084118478830133274932893)
  ·
    refine ⟨1531544429561299978099835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4084118478830133274932893 1531544429561299978099835)
    ·
      refine ⟨2297316644341949967149753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531544429561299978099835 2297316644341949967149753)
      ·
        refine ⟨1722987483256462475362315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2297316644341949967149753 1722987483256462475362315)
        ·
          refine ⟨2584481224884693713043473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722987483256462475362315 2584481224884693713043473)
          ·
            refine ⟨1938360918663520284782605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2584481224884693713043473 1938360918663520284782605)
            ·
              refine ⟨726885344498820106793477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1938360918663520284782605 726885344498820106793477)
              ·
                refine ⟨136291002093528770023777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726885344498820106793477 136291002093528770023777)
                ·
                  rfl

theorem cell19_447906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_447906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447906 prefixEnd_447906 := by exact prefixLift 447906
  have htrace : WordTrace (prefixWord ++ tailWord_447906) baseStart_447906 baseEnd_447906 := by
    simpa [prefixWord, tailWord_447906, baseEnd_447906] using wordTrace_append hprefix tailTrace_447906
  have hstable : (prefixWord ++ tailWord_447906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447906).length < 2 ^ (prefixWord ++ tailWord_447906).sum := by decide
  have hdescent : baseEnd_447906 < baseStart_447906 := by decide
  rcases family_descends (prefixWord ++ tailWord_447906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447938 : List Nat := [3, 5, 2, 1, 1, 1, 6]
def baseStart_447938 : Nat := 118140960795 + 447938 * 2 ^ 59
def prefixEnd_447938 : Nat := 4983230072969 + 3 ^ 40 * 447938 * 2
def baseEnd_447938 : Nat := 45433579736054059104193

theorem tailTrace_447938 : CollatzResearch.WordTrace tailWord_447938 prefixEnd_447938 45433579736054059104193 := by
  unfold tailWord_447938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084410262801150641224117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10891760700803068376597645 4084410262801150641224117)
  ·
    refine ⟨382913462137607872614761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4084410262801150641224117 382913462137607872614761)
    ·
      refine ⟨287185096603205904461071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382913462137607872614761 287185096603205904461071)
      ·
        refine ⟨430777644904808856691607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287185096603205904461071 430777644904808856691607)
        ·
          refine ⟨646166467357213285037411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430777644904808856691607 646166467357213285037411)
          ·
            refine ⟨969249701035819927556117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646166467357213285037411 969249701035819927556117)
            ·
              refine ⟨45433579736054059104193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 969249701035819927556117 45433579736054059104193)
              ·
                rfl

theorem cell19_447938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_447938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447938 prefixEnd_447938 := by exact prefixLift 447938
  have htrace : WordTrace (prefixWord ++ tailWord_447938) baseStart_447938 baseEnd_447938 := by
    simpa [prefixWord, tailWord_447938, baseEnd_447938] using wordTrace_append hprefix tailTrace_447938
  have hstable : (prefixWord ++ tailWord_447938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447938).length < 2 ^ (prefixWord ++ tailWord_447938).sum := by decide
  have hdescent : baseEnd_447938 < baseStart_447938 := by decide
  rcases family_descends (prefixWord ++ tailWord_447938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447946 : List Nat := [3, 1, 2, 1, 2, 4, 6]
def baseStart_447946 : Nat := 118140960795 + 447946 * 2 ^ 59
def prefixEnd_447946 : Nat := 4983230072969 + 3 ^ 40 * 447946 * 2
def baseEnd_447946 : Nat := 45434391162273509711593

theorem tailTrace_447946 : CollatzResearch.WordTrace tailWord_447946 prefixEnd_447946 45434391162273509711593 := by
  unfold tailWord_447946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084483208793904982796923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10891955223450413287458461 4084483208793904982796923)
  ·
    refine ⟨6126724813190857474195385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4084483208793904982796923 6126724813190857474195385)
    ·
      refine ⟨4595043609893143105646539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6126724813190857474195385 4595043609893143105646539)
      ·
        refine ⟨6892565414839714658469809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595043609893143105646539 6892565414839714658469809)
        ·
          refine ⟨5169424061129785993852357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6892565414839714658469809 5169424061129785993852357)
          ·
            refine ⟨969267011461834873847317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5169424061129785993852357 969267011461834873847317)
            ·
              refine ⟨45434391162273509711593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 969267011461834873847317 45434391162273509711593)
              ·
                rfl

theorem cell19_447946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_447946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447946 prefixEnd_447946 := by exact prefixLift 447946
  have htrace : WordTrace (prefixWord ++ tailWord_447946) baseStart_447946 baseEnd_447946 := by
    simpa [prefixWord, tailWord_447946, baseEnd_447946] using wordTrace_append hprefix tailTrace_447946
  have hstable : (prefixWord ++ tailWord_447946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447946).length < 2 ^ (prefixWord ++ tailWord_447946).sum := by decide
  have hdescent : baseEnd_447946 < baseStart_447946 := by decide
  rcases family_descends (prefixWord ++ tailWord_447946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447978 : List Nat := [3, 1, 3, 1, 5, 1, 2, 3]
def baseStart_447978 : Nat := 118140960795 + 447978 * 2 ^ 59
def prefixEnd_447978 : Nat := 4983230072969 + 3 ^ 40 * 447978 * 2
def baseEnd_447978 : Nat := 136312910601453936423581

theorem tailTrace_447978 : CollatzResearch.WordTrace tailWord_447978 prefixEnd_447978 136312910601453936423581 := by
  unfold tailWord_447978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084774992764922349088147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10892733314039792930901725 4084774992764922349088147)
  ·
    refine ⟨6127162489147383523632221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4084774992764922349088147 6127162489147383523632221)
    ·
      refine ⟨2297685933430268821362083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6127162489147383523632221 2297685933430268821362083)
      ·
        refine ⟨3446528900145403232043125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297685933430268821362083 3446528900145403232043125)
        ·
          refine ⟨323112084388631553004043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3446528900145403232043125 323112084388631553004043)
          ·
            refine ⟨484668126582947329506065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323112084388631553004043 484668126582947329506065)
            ·
              refine ⟨363501094937210497129549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484668126582947329506065 363501094937210497129549)
              ·
                refine ⟨136312910601453936423581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363501094937210497129549 136312910601453936423581)
                ·
                  rfl

theorem cell19_447978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_447978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447978 prefixEnd_447978 := by exact prefixLift 447978
  have htrace : WordTrace (prefixWord ++ tailWord_447978) baseStart_447978 baseEnd_447978 := by
    simpa [prefixWord, tailWord_447978, baseEnd_447978] using wordTrace_append hprefix tailTrace_447978
  have hstable : (prefixWord ++ tailWord_447978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447978).length < 2 ^ (prefixWord ++ tailWord_447978).sum := by decide
  have hdescent : baseEnd_447978 < baseStart_447978 := by decide
  rcases family_descends (prefixWord ++ tailWord_447978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447984 : List Nat := [2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_447984 : Nat := 118140960795 + 447984 * 2 ^ 59
def prefixEnd_447984 : Nat := 4983230072969 + 3 ^ 40 * 447984 * 2
def baseEnd_447984 : Nat := 136314736310447700290231

theorem tailTrace_447984 : CollatzResearch.WordTrace tailWord_447984 prefixEnd_447984 136314736310447700290231 := by
  unfold tailWord_447984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8169659404518976210535503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10892879206025301614047337 8169659404518976210535503)
  ·
    refine ⟨12254489106778464315803255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8169659404518976210535503 12254489106778464315803255)
    ·
      refine ⟨18381733660167696473704883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12254489106778464315803255 18381733660167696473704883)
      ·
        refine ⟨27572600490251544710557325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18381733660167696473704883 27572600490251544710557325)
        ·
          refine ⟨10339725183844329266458997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27572600490251544710557325 10339725183844329266458997)
          ·
            refine ⟨969349235985405868730531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10339725183844329266458997 969349235985405868730531)
            ·
              refine ⟨1454023853978108803095797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969349235985405868730531 1454023853978108803095797)
              ·
                refine ⟨136314736310447700290231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1454023853978108803095797 136314736310447700290231)
                ·
                  rfl

theorem cell19_447984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_447984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_447984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_447984 prefixEnd_447984 := by exact prefixLift 447984
  have htrace : WordTrace (prefixWord ++ tailWord_447984) baseStart_447984 baseEnd_447984 := by
    simpa [prefixWord, tailWord_447984, baseEnd_447984] using wordTrace_append hprefix tailTrace_447984
  have hstable : (prefixWord ++ tailWord_447984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447984).length < 2 ^ (prefixWord ++ tailWord_447984).sum := by decide
  have hdescent : baseEnd_447984 < baseStart_447984 := by decide
  rcases family_descends (prefixWord ++ tailWord_447984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448001 : List Nat := [1, 2, 4, 1, 4, 2, 5]
def baseStart_448001 : Nat := 118140960795 + 448001 * 2 ^ 59
def prefixEnd_448001 : Nat := 4983230072969 + 3 ^ 40 * 448001 * 2
def baseEnd_448001 : Nat := 45439969717532232637469

theorem tailTrace_448001 : CollatzResearch.WordTrace tailWord_448001 prefixEnd_448001 45439969717532232637469 := by
  unfold tailWord_448001
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339938849976364324439857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10893292566650909549626571 16339938849976364324439857)
  ·
    refine ⟨12254954137482273243329893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16339938849976364324439857 12254954137482273243329893)
    ·
      refine ⟨2297803900777926233124355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12254954137482273243329893 2297803900777926233124355)
      ·
        refine ⟨3446705851166889349686533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297803900777926233124355 3446705851166889349686533)
        ·
          refine ⟨646257347093791753066225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3446705851166889349686533 646257347093791753066225)
          ·
            refine ⟨484693010320343814799669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646257347093791753066225 484693010320343814799669)
            ·
              refine ⟨45439969717532232637469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 484693010320343814799669 45439969717532232637469)
              ·
                rfl

theorem cell19_448001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_448001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448001 prefixEnd_448001 := by exact prefixLift 448001
  have htrace : WordTrace (prefixWord ++ tailWord_448001) baseStart_448001 baseEnd_448001 := by
    simpa [prefixWord, tailWord_448001, baseEnd_448001] using wordTrace_append hprefix tailTrace_448001
  have hstable : (prefixWord ++ tailWord_448001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448001).length < 2 ^ (prefixWord ++ tailWord_448001).sum := by decide
  have hdescent : baseEnd_448001 < baseStart_448001 := by decide
  rcases family_descends (prefixWord ++ tailWord_448001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448060 : List Nat := [2, 2, 2, 2, 4, 7]
def baseStart_448060 : Nat := 118140960795 + 448060 * 2 ^ 59
def prefixEnd_448060 : Nat := 4983230072969 + 3 ^ 40 * 448060 * 2
def baseEnd_448060 : Nat := 15148651328633560289015

theorem tailTrace_448060 : CollatzResearch.WordTrace tailWord_448060 prefixEnd_448060 15148651328633560289015 := by
  unfold tailWord_448060
  simp only [CollatzResearch.WordTrace]
  refine ⟨8171045378381308700418817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10894727171175078267225089 8171045378381308700418817)
  ·
    refine ⟨6128284033785981525314113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8171045378381308700418817 6128284033785981525314113)
    ·
      refine ⟨4596213025339486143985585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6128284033785981525314113 4596213025339486143985585)
      ·
        refine ⟨3447159769004614607989189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4596213025339486143985585 3447159769004614607989189)
        ·
          refine ⟨646342456688365238997973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3447159769004614607989189 646342456688365238997973)
          ·
            refine ⟨15148651328633560289015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 646342456688365238997973 15148651328633560289015)
            ·
              rfl

theorem cell19_448060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 7].length) (baseStart_448060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448060 prefixEnd_448060 := by exact prefixLift 448060
  have htrace : WordTrace (prefixWord ++ tailWord_448060) baseStart_448060 baseEnd_448060 := by
    simpa [prefixWord, tailWord_448060, baseEnd_448060] using wordTrace_append hprefix tailTrace_448060
  have hstable : (prefixWord ++ tailWord_448060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448060).length < 2 ^ (prefixWord ++ tailWord_448060).sum := by decide
  have hdescent : baseEnd_448060 < baseStart_448060 := by decide
  rcases family_descends (prefixWord ++ tailWord_448060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448168 : List Nat := [2, 1, 7, 1, 1, 2, 5]
def baseStart_448168 : Nat := 118140960795 + 448168 * 2 ^ 59
def prefixEnd_448168 : Nat := 4983230072969 + 3 ^ 40 * 448168 * 2
def baseEnd_448168 : Nat := 45456908239863264066947

theorem tailTrace_448168 : CollatzResearch.WordTrace tailWord_448168 prefixEnd_448168 45456908239863264066947 := by
  unfold tailWord_448168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8173014920185675922884579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10897353226914234563846105 8173014920185675922884579)
  ·
    refine ⟨12259522380278513884326869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8173014920185675922884579 12259522380278513884326869)
    ·
      refine ⟨287332555787777669163911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12259522380278513884326869 287332555787777669163911)
      ·
        refine ⟨430998833681666503745867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287332555787777669163911 430998833681666503745867)
        ·
          refine ⟨646498250522499755618801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430998833681666503745867 646498250522499755618801)
          ·
            refine ⟨484873687891874816714101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646498250522499755618801 484873687891874816714101)
            ·
              refine ⟨45456908239863264066947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 484873687891874816714101 45456908239863264066947)
              ·
                rfl

theorem cell19_448168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_448168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448168 prefixEnd_448168 := by exact prefixLift 448168
  have htrace : WordTrace (prefixWord ++ tailWord_448168) baseStart_448168 baseEnd_448168 := by
    simpa [prefixWord, tailWord_448168, baseEnd_448168] using wordTrace_append hprefix tailTrace_448168
  have hstable : (prefixWord ++ tailWord_448168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448168).length < 2 ^ (prefixWord ++ tailWord_448168).sum := by decide
  have hdescent : baseEnd_448168 < baseStart_448168 := by decide
  rcases family_descends (prefixWord ++ tailWord_448168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448176 : List Nat := [2, 1, 1, 1, 2, 1, 11]
def baseStart_448176 : Nat := 118140960795 + 448176 * 2 ^ 59
def prefixEnd_448176 : Nat := 4983230072969 + 3 ^ 40 * 448176 * 2
def baseEnd_448176 : Nat := 45457719666082714674347

theorem tailTrace_448176 : CollatzResearch.WordTrace tailWord_448176 prefixEnd_448176 45457719666082714674347 := by
  unfold tailWord_448176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8173160812171184606030191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10897547749561579474706921 8173160812171184606030191)
  ·
    refine ⟨12259741218256776909045287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8173160812171184606030191 12259741218256776909045287)
    ·
      refine ⟨18389611827385165363567931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12259741218256776909045287 18389611827385165363567931)
      ·
        refine ⟨27584417741077748045351897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18389611827385165363567931 27584417741077748045351897)
        ·
          refine ⟨20688313305808311034013923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27584417741077748045351897 20688313305808311034013923)
          ·
            refine ⟨31032469958712466551020885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20688313305808311034013923 31032469958712466551020885)
            ·
              refine ⟨45457719666082714674347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31032469958712466551020885 45457719666082714674347)
              ·
                rfl

theorem cell19_448176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_448176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448176 prefixEnd_448176 := by exact prefixLift 448176
  have htrace : WordTrace (prefixWord ++ tailWord_448176) baseStart_448176 baseEnd_448176 := by
    simpa [prefixWord, tailWord_448176, baseEnd_448176] using wordTrace_append hprefix tailTrace_448176
  have hstable : (prefixWord ++ tailWord_448176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448176).length < 2 ^ (prefixWord ++ tailWord_448176).sum := by decide
  have hdescent : baseEnd_448176 < baseStart_448176 := by decide
  rcases family_descends (prefixWord ++ tailWord_448176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448231 : List Nat := [1, 1, 5, 4, 8]
def baseStart_448231 : Nat := 118140960795 + 448231 * 2 ^ 59
def prefixEnd_448231 : Nat := 4983230072969 + 3 ^ 40 * 448231 * 2
def baseEnd_448231 : Nat := 5051477580149048622247

theorem tailTrace_448231 : CollatzResearch.WordTrace tailWord_448231 prefixEnd_448231 5051477580149048622247 := by
  unfold tailWord_448231
  simp only [CollatzResearch.WordTrace]
  refine ⟨16348327639143113605312547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10898885092762075736875031 16348327639143113605312547)
  ·
    refine ⟨24522491458714670407968821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16348327639143113605312547 24522491458714670407968821)
    ·
      refine ⟨2298983574254500350747077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24522491458714670407968821 2298983574254500350747077)
      ·
        refine ⟨431059420172718815765077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2298983574254500350747077 431059420172718815765077)
        ·
          refine ⟨5051477580149048622247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 431059420172718815765077 5051477580149048622247)
          ·
            rfl

theorem cell19_448231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 8].length) (baseStart_448231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448231 prefixEnd_448231 := by exact prefixLift 448231
  have htrace : WordTrace (prefixWord ++ tailWord_448231) baseStart_448231 baseEnd_448231 := by
    simpa [prefixWord, tailWord_448231, baseEnd_448231] using wordTrace_append hprefix tailTrace_448231
  have hstable : (prefixWord ++ tailWord_448231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448231).length < 2 ^ (prefixWord ++ tailWord_448231).sum := by decide
  have hdescent : baseEnd_448231 < baseStart_448231 := by decide
  rcases family_descends (prefixWord ++ tailWord_448231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448244 : List Nat := [2, 6, 1, 1, 1, 3, 1, 4]
def baseStart_448244 : Nat := 118140960795 + 448244 * 2 ^ 59
def prefixEnd_448244 : Nat := 4983230072969 + 3 ^ 40 * 448244 * 2
def baseEnd_448244 : Nat := 136393850366844134511745

theorem tailTrace_448244 : CollatzResearch.WordTrace tailWord_448244 prefixEnd_448244 136393850366844134511745 := by
  unfold tailWord_448244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8174400894048008412767893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10899201192064011217023857 8174400894048008412767893)
  ·
    refine ⟨383175041908500394348495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8174400894048008412767893 383175041908500394348495)
    ·
      refine ⟨574762562862750591522743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383175041908500394348495 574762562862750591522743)
      ·
        refine ⟨862143844294125887284115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574762562862750591522743 862143844294125887284115)
        ·
          refine ⟨1293215766441188830926173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862143844294125887284115 1293215766441188830926173)
          ·
            refine ⟨484955912415445811597315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1293215766441188830926173 484955912415445811597315)
            ·
              refine ⟨727433868623168717395973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484955912415445811597315 727433868623168717395973)
              ·
                refine ⟨136393850366844134511745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727433868623168717395973 136393850366844134511745)
                ·
                  rfl

theorem cell19_448244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_448244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448244 prefixEnd_448244 := by exact prefixLift 448244
  have htrace : WordTrace (prefixWord ++ tailWord_448244) baseStart_448244 baseEnd_448244 := by
    simpa [prefixWord, tailWord_448244, baseEnd_448244] using wordTrace_append hprefix tailTrace_448244
  have hstable : (prefixWord ++ tailWord_448244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448244).length < 2 ^ (prefixWord ++ tailWord_448244).sum := by decide
  have hdescent : baseEnd_448244 < baseStart_448244 := by decide
  rcases family_descends (prefixWord ++ tailWord_448244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448343 : List Nat := [1, 1, 3, 2, 6, 1, 5]
def baseStart_448343 : Nat := 118140960795 + 448343 * 2 ^ 59
def prefixEnd_448343 : Nat := 4983230072969 + 3 ^ 40 * 448343 * 2
def baseEnd_448343 : Nat := 45474658188413746103825

theorem tailTrace_448343 : CollatzResearch.WordTrace tailWord_448343 prefixEnd_448343 45474658188413746103825 := by
  unfold tailWord_448343
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352412614737356733389683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10901608409824904488926455 16352412614737356733389683)
  ·
    refine ⟨24528618922106035100084525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16352412614737356733389683 24528618922106035100084525)
    ·
      refine ⟨9198232095789763162531697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24528618922106035100084525 9198232095789763162531697)
      ·
        refine ⟨6898674071842322371898773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9198232095789763162531697 6898674071842322371898773)
        ·
          refine ⟨323375347117608861182755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6898674071842322371898773 323375347117608861182755)
          ·
            refine ⟨485063020676413291774133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323375347117608861182755 485063020676413291774133)
            ·
              refine ⟨45474658188413746103825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 485063020676413291774133 45474658188413746103825)
              ·
                rfl

theorem cell19_448343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_448343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448343 prefixEnd_448343 := by exact prefixLift 448343
  have htrace : WordTrace (prefixWord ++ tailWord_448343) baseStart_448343 baseEnd_448343 := by
    simpa [prefixWord, tailWord_448343, baseEnd_448343] using wordTrace_append hprefix tailTrace_448343
  have hstable : (prefixWord ++ tailWord_448343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448343).length < 2 ^ (prefixWord ++ tailWord_448343).sum := by decide
  have hdescent : baseEnd_448343 < baseStart_448343 := by decide
  rcases family_descends (prefixWord ++ tailWord_448343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448364 : List Nat := [2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_448364 : Nat := 118140960795 + 448364 * 2 ^ 59
def prefixEnd_448364 : Nat := 4983230072969 + 3 ^ 40 * 448364 * 2
def baseEnd_448364 : Nat := 136430364546719411844751

theorem tailTrace_448364 : CollatzResearch.WordTrace tailWord_448364 prefixEnd_448364 136430364546719411844751 := by
  unfold tailWord_448364
  simp only [CollatzResearch.WordTrace]
  refine ⟨8176589273830638659952073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10902119031774184879936097 8176589273830638659952073)
  ·
    refine ⟨6132441955372978994964055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8176589273830638659952073 6132441955372978994964055)
    ·
      refine ⟨9198662933059468492446083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6132441955372978994964055 9198662933059468492446083)
      ·
        refine ⟨13797994399589202738669125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9198662933059468492446083 13797994399589202738669125)
        ·
          refine ⟨2587123949922975513500461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13797994399589202738669125 2587123949922975513500461)
          ·
            refine ⟨970171481221115817562673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2587123949922975513500461 970171481221115817562673)
            ·
              refine ⟨727628610915836863172005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970171481221115817562673 727628610915836863172005)
              ·
                refine ⟨136430364546719411844751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727628610915836863172005 136430364546719411844751)
                ·
                  rfl

theorem cell19_448364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_448364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448364 prefixEnd_448364 := by exact prefixLift 448364
  have htrace : WordTrace (prefixWord ++ tailWord_448364) baseStart_448364 baseEnd_448364 := by
    simpa [prefixWord, tailWord_448364, baseEnd_448364] using wordTrace_append hprefix tailTrace_448364
  have hstable : (prefixWord ++ tailWord_448364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448364).length < 2 ^ (prefixWord ++ tailWord_448364).sum := by decide
  have hdescent : baseEnd_448364 < baseStart_448364 := by decide
  rcases family_descends (prefixWord ++ tailWord_448364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448402 : List Nat := [3, 2, 3, 2, 1, 8]
def baseStart_448402 : Nat := 118140960795 + 448402 * 2 ^ 59
def prefixEnd_448402 : Nat := 4983230072969 + 3 ^ 40 * 448402 * 2
def baseEnd_448402 : Nat := 15160214152260731444467

theorem tailTrace_448402 : CollatzResearch.WordTrace tailWord_448402 prefixEnd_448402 15160214152260731444467 := by
  unfold tailWord_448402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088641130380902452446865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10903043014349073206524973 4088641130380902452446865)
  ·
    refine ⟨3066480847785676839335149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4088641130380902452446865 3066480847785676839335149)
    ·
      refine ⟨1149930317919628814750681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3066480847785676839335149 1149930317919628814750681)
      ·
        refine ⟨862447738439721611063011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1149930317919628814750681 862447738439721611063011)
        ·
          refine ⟨1293671607659582416594517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862447738439721611063011 1293671607659582416594517)
          ·
            refine ⟨15160214152260731444467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1293671607659582416594517 15160214152260731444467)
            ·
              rfl

theorem cell19_448402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 8].length) (baseStart_448402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448402 prefixEnd_448402 := by exact prefixLift 448402
  have htrace : WordTrace (prefixWord ++ tailWord_448402) baseStart_448402 baseEnd_448402 := by
    simpa [prefixWord, tailWord_448402, baseEnd_448402] using wordTrace_append hprefix tailTrace_448402
  have hstable : (prefixWord ++ tailWord_448402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448402).length < 2 ^ (prefixWord ++ tailWord_448402).sum := by decide
  have hdescent : baseEnd_448402 < baseStart_448402 := by decide
  rcases family_descends (prefixWord ++ tailWord_448402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448417 : List Nat := [1, 2, 3, 4, 3, 1, 1, 4]
def baseStart_448417 : Nat := 118140960795 + 448417 * 2 ^ 59
def prefixEnd_448417 : Nat := 4983230072969 + 3 ^ 40 * 448417 * 2
def baseEnd_448417 : Nat := 136446491642830992666829

theorem tailTrace_448417 : CollatzResearch.WordTrace tailWord_448417 prefixEnd_448417 136446491642830992666829 := by
  unfold tailWord_448417
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355111616469267371583505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10903407744312844914389003 16355111616469267371583505)
  ·
    refine ⟨12266333712351950528687629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16355111616469267371583505 12266333712351950528687629)
    ·
      refine ⟨4599875142131981448257861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12266333712351950528687629 4599875142131981448257861)
      ·
        refine ⟨862476589149746521548349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4599875142131981448257861 862476589149746521548349)
        ·
          refine ⟨323428720931154945580631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 862476589149746521548349 323428720931154945580631)
          ·
            refine ⟨485143081396732418370947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323428720931154945580631 485143081396732418370947)
            ·
              refine ⟨727714622095098627556421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485143081396732418370947 727714622095098627556421)
              ·
                refine ⟨136446491642830992666829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727714622095098627556421 136446491642830992666829)
                ·
                  rfl

theorem cell19_448417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 4].length) (baseStart_448417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448417 prefixEnd_448417 := by exact prefixLift 448417
  have htrace : WordTrace (prefixWord ++ tailWord_448417) baseStart_448417 baseEnd_448417 := by
    simpa [prefixWord, tailWord_448417, baseEnd_448417] using wordTrace_append hprefix tailTrace_448417
  have hstable : (prefixWord ++ tailWord_448417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448417).length < 2 ^ (prefixWord ++ tailWord_448417).sum := by decide
  have hdescent : baseEnd_448417 < baseStart_448417 := by decide
  rcases family_descends (prefixWord ++ tailWord_448417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448440 : List Nat := [2, 1, 2, 1, 2, 3, 5, 3]
def baseStart_448440 : Nat := 118140960795 + 448440 * 2 ^ 59
def prefixEnd_448440 : Nat := 4983230072969 + 3 ^ 40 * 448440 * 2
def baseEnd_448440 : Nat := 136453490193973754155655

theorem tailTrace_448440 : CollatzResearch.WordTrace tailWord_448440 prefixEnd_448440 136453490193973754155655 := by
  unfold tailWord_448440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177975247692971149835387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10903966996923961533113849 8177975247692971149835387)
  ·
    refine ⟨12266962871539456724753081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8177975247692971149835387 12266962871539456724753081)
    ·
      refine ⟨9200222153654592543564811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12266962871539456724753081 9200222153654592543564811)
      ·
        refine ⟨13800333230481888815347217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9200222153654592543564811 13800333230481888815347217)
        ·
          refine ⟨10350249922861416611510413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13800333230481888815347217 10350249922861416611510413)
          ·
            refine ⟨3881343721073031229316405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10350249922861416611510413 3881343721073031229316405)
            ·
              refine ⟨363875973850596677748413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3881343721073031229316405 363875973850596677748413)
              ·
                refine ⟨136453490193973754155655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363875973850596677748413 136453490193973754155655)
                ·
                  rfl

theorem cell19_448440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_448440 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448440 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448440 prefixEnd_448440 := by exact prefixLift 448440
  have htrace : WordTrace (prefixWord ++ tailWord_448440) baseStart_448440 baseEnd_448440 := by
    simpa [prefixWord, tailWord_448440, baseEnd_448440] using wordTrace_append hprefix tailTrace_448440
  have hstable : (prefixWord ++ tailWord_448440).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448440).length < 2 ^ (prefixWord ++ tailWord_448440).sum := by decide
  have hdescent : baseEnd_448440 < baseStart_448440 := by decide
  rcases family_descends (prefixWord ++ tailWord_448440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448497 : List Nat := [1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_448497 : Nat := 118140960795 + 448497 * 2 ^ 59
def prefixEnd_448497 : Nat := 4983230072969 + 3 ^ 40 * 448497 * 2
def baseEnd_448497 : Nat := 136470834429414510888833

theorem tailTrace_448497 : CollatzResearch.WordTrace tailWord_448497 prefixEnd_448497 136470834429414510888833 := by
  unfold tailWord_448497
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358029456179441034495745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10905352970786294022997163 16358029456179441034495745)
  ·
    refine ⟨12268522092134580775871809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16358029456179441034495745 12268522092134580775871809)
    ·
      refine ⟨9201391569100935581903857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12268522092134580775871809 9201391569100935581903857)
      ·
        refine ⟨6901043676825701686427893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9201391569100935581903857 6901043676825701686427893)
        ·
          refine ⟨646972844702409533102615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6901043676825701686427893 646972844702409533102615)
          ·
            refine ⟨970459267053614299653923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646972844702409533102615 970459267053614299653923)
            ·
              refine ⟨1455688900580421449480885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970459267053614299653923 1455688900580421449480885)
              ·
                refine ⟨136470834429414510888833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1455688900580421449480885 136470834429414510888833)
                ·
                  rfl

theorem cell19_448497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_448497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448497 prefixEnd_448497 := by exact prefixLift 448497
  have htrace : WordTrace (prefixWord ++ tailWord_448497) baseStart_448497 baseEnd_448497 := by
    simpa [prefixWord, tailWord_448497, baseEnd_448497] using wordTrace_append hprefix tailTrace_448497
  have hstable : (prefixWord ++ tailWord_448497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448497).length < 2 ^ (prefixWord ++ tailWord_448497).sum := by decide
  have hdescent : baseEnd_448497 < baseStart_448497 := by decide
  rcases family_descends (prefixWord ++ tailWord_448497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448554 : List Nat := [3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_448554 : Nat := 118140960795 + 448554 * 2 ^ 59
def prefixEnd_448554 : Nat := 4983230072969 + 3 ^ 40 * 448554 * 2
def baseEnd_448554 : Nat := 136488178664855267622011

theorem tailTrace_448554 : CollatzResearch.WordTrace tailWord_448554 prefixEnd_448554 136488178664855267622011 := by
  unfold tailWord_448554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090027104243234942330179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10906738944648626512880477 4090027104243234942330179)
  ·
    refine ⟨6135040656364852413495269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4090027104243234942330179 6135040656364852413495269)
    ·
      refine ⟨1150320123068409827530363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6135040656364852413495269 1150320123068409827530363)
      ·
        refine ⟨1725480184602614741295545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150320123068409827530363 1725480184602614741295545)
        ·
          refine ⟨1294110138451961055971659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1725480184602614741295545 1294110138451961055971659)
          ·
            refine ⟨1941165207677941583957489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294110138451961055971659 1941165207677941583957489)
            ·
              refine ⟨1455873905758456187968117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1941165207677941583957489 1455873905758456187968117)
              ·
                refine ⟨136488178664855267622011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1455873905758456187968117 136488178664855267622011)
                ·
                  rfl

theorem cell19_448554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_448554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448554 prefixEnd_448554 := by exact prefixLift 448554
  have htrace : WordTrace (prefixWord ++ tailWord_448554) baseStart_448554 baseEnd_448554 := by
    simpa [prefixWord, tailWord_448554, baseEnd_448554] using wordTrace_append hprefix tailTrace_448554
  have hstable : (prefixWord ++ tailWord_448554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448554).length < 2 ^ (prefixWord ++ tailWord_448554).sum := by decide
  have hdescent : baseEnd_448554 < baseStart_448554 := by decide
  rcases family_descends (prefixWord ++ tailWord_448554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448630 : List Nat := [5, 1, 1, 2, 1, 3, 6]
def baseStart_448630 : Nat := 118140960795 + 448630 * 2 ^ 59
def prefixEnd_448630 : Nat := 4983230072969 + 3 ^ 40 * 448630 * 2
def baseEnd_448630 : Nat := 45503768104036536644305

theorem tailTrace_448630 : CollatzResearch.WordTrace tailWord_448630 prefixEnd_448630 45503768104036536644305 := by
  unfold tailWord_448630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022680022793600296817959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10908586909798403166058229 1022680022793600296817959)
  ·
    refine ⟨1534020034190400445226939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022680022793600296817959 1534020034190400445226939)
    ·
      refine ⟨2301030051285600667840409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534020034190400445226939 2301030051285600667840409)
      ·
        refine ⟨1725772538464200500880307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2301030051285600667840409 1725772538464200500880307)
        ·
          refine ⟨2588658807696300751320461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725772538464200500880307 2588658807696300751320461)
          ·
            refine ⟨970747052886112781745173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2588658807696300751320461 970747052886112781745173)
            ·
              refine ⟨45503768104036536644305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 970747052886112781745173 45503768104036536644305)
              ·
                rfl

theorem cell19_448630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_448630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448630 prefixEnd_448630 := by exact prefixLift 448630
  have htrace : WordTrace (prefixWord ++ tailWord_448630) baseStart_448630 baseEnd_448630 := by
    simpa [prefixWord, tailWord_448630, baseEnd_448630] using wordTrace_append hprefix tailTrace_448630
  have hstable : (prefixWord ++ tailWord_448630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448630).length < 2 ^ (prefixWord ++ tailWord_448630).sum := by decide
  have hdescent : baseEnd_448630 < baseStart_448630 := by decide
  rcases family_descends (prefixWord ++ tailWord_448630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448664 : List Nat := [2, 1, 2, 4, 4, 1, 2, 3]
def baseStart_448664 : Nat := 118140960795 + 448664 * 2 ^ 59
def prefixEnd_448664 : Nat := 4983230072969 + 3 ^ 40 * 448664 * 2
def baseEnd_448664 : Nat := 136521649996407605177267

theorem tailTrace_448664 : CollatzResearch.WordTrace tailWord_448664 prefixEnd_448664 136521649996407605177267 := by
  unfold tailWord_448664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182060223287214277912523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10909413631049619037216697 8182060223287214277912523)
  ·
    refine ⟨12273090334930821416868785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8182060223287214277912523 12273090334930821416868785)
    ·
      refine ⟨9204817751198116062651589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12273090334930821416868785 9204817751198116062651589)
      ·
        refine ⟨1725903328349646761747173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9204817751198116062651589 1725903328349646761747173)
        ·
          refine ⟨323606874065558767827595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1725903328349646761747173 323606874065558767827595)
          ·
            refine ⟨485410311098338151741393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323606874065558767827595 485410311098338151741393)
            ·
              refine ⟨364057733323753613806045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485410311098338151741393 364057733323753613806045)
              ·
                refine ⟨136521649996407605177267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364057733323753613806045 136521649996407605177267)
                ·
                  rfl

theorem cell19_448664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_448664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448664 prefixEnd_448664 := by exact prefixLift 448664
  have htrace : WordTrace (prefixWord ++ tailWord_448664) baseStart_448664 baseEnd_448664 := by
    simpa [prefixWord, tailWord_448664, baseEnd_448664] using wordTrace_append hprefix tailTrace_448664
  have hstable : (prefixWord ++ tailWord_448664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448664).length < 2 ^ (prefixWord ++ tailWord_448664).sum := by decide
  have hdescent : baseEnd_448664 < baseStart_448664 := by decide
  rcases family_descends (prefixWord ++ tailWord_448664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448782 : List Nat := [4, 1, 1, 2, 1, 2, 5, 3]
def baseStart_448782 : Nat := 118140960795 + 448782 * 2 ^ 59
def prefixEnd_448782 : Nat := 4983230072969 + 3 ^ 40 * 448782 * 2
def baseEnd_448782 : Nat := 136557555606618294554723

theorem tailTrace_448782 : CollatzResearch.WordTrace tailWord_448782 prefixEnd_448782 136557555606618294554723 := by
  unfold tailWord_448782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046053032518366838577575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10912282840097956472413733 2046053032518366838577575)
  ·
    refine ⟨3069079548777550257866363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2046053032518366838577575 3069079548777550257866363)
    ·
      refine ⟨4603619323166325386799545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3069079548777550257866363 4603619323166325386799545)
      ·
        refine ⟨3452714492374744040099659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4603619323166325386799545 3452714492374744040099659)
        ·
          refine ⟨5179071738562116060149489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452714492374744040099659 5179071738562116060149489)
          ·
            refine ⟨3884303803921587045112117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5179071738562116060149489 3884303803921587045112117)
            ·
              refine ⟨364153481617648785479261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3884303803921587045112117 364153481617648785479261)
              ·
                refine ⟨136557555606618294554723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364153481617648785479261 136557555606618294554723)
                ·
                  rfl

theorem cell19_448782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_448782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448782 prefixEnd_448782 := by exact prefixLift 448782
  have htrace : WordTrace (prefixWord ++ tailWord_448782) baseStart_448782 baseEnd_448782 := by
    simpa [prefixWord, tailWord_448782, baseEnd_448782] using wordTrace_append hprefix tailTrace_448782
  have hstable : (prefixWord ++ tailWord_448782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448782).length < 2 ^ (prefixWord ++ tailWord_448782).sum := by decide
  have hdescent : baseEnd_448782 < baseStart_448782 := by decide
  rcases family_descends (prefixWord ++ tailWord_448782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448953 : List Nat := [1, 2, 1, 4, 3, 2, 3, 3]
def baseStart_448953 : Nat := 118140960795 + 448953 * 2 ^ 59
def prefixEnd_448953 : Nat := 4983230072969 + 3 ^ 40 * 448953 * 2
def baseEnd_448953 : Nat := 136609588312940564754257

theorem tailTrace_448953 : CollatzResearch.WordTrace tailWord_448953 prefixEnd_448953 136609588312940564754257 := by
  unfold tailWord_448953
  simp only [CollatzResearch.WordTrace]
  refine ⟨16374661142527430913095513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10916440761684953942063675 16374661142527430913095513)
  ·
    refine ⟨12280995856895573184821635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16374661142527430913095513 12280995856895573184821635)
    ·
      refine ⟨18421493785343359777232453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12280995856895573184821635 18421493785343359777232453)
      ·
        refine ⟨3454030084751879958231085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18421493785343359777232453 3454030084751879958231085)
        ·
          refine ⟨1295261281781954984336657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3454030084751879958231085 1295261281781954984336657)
          ·
            refine ⟨971445961336466238252493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295261281781954984336657 971445961336466238252493)
            ·
              refine ⟨364292235501174839344685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 971445961336466238252493 364292235501174839344685)
              ·
                refine ⟨136609588312940564754257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364292235501174839344685 136609588312940564754257)
                ·
                  rfl

theorem cell19_448953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_448953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_448953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_448953 prefixEnd_448953 := by exact prefixLift 448953
  have htrace : WordTrace (prefixWord ++ tailWord_448953) baseStart_448953 baseEnd_448953 := by
    simpa [prefixWord, tailWord_448953, baseEnd_448953] using wordTrace_append hprefix tailTrace_448953
  have hstable : (prefixWord ++ tailWord_448953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448953).length < 2 ^ (prefixWord ++ tailWord_448953).sum := by decide
  have hdescent : baseEnd_448953 < baseStart_448953 := by decide
  rcases family_descends (prefixWord ++ tailWord_448953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449010 : List Nat := [3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_449010 : Nat := 118140960795 + 449010 * 2 ^ 59
def prefixEnd_449010 : Nat := 4983230072969 + 3 ^ 40 * 449010 * 2
def baseEnd_449010 : Nat := 136626932548381321487435

theorem tailTrace_449010 : CollatzResearch.WordTrace tailWord_449010 prefixEnd_449010 136626932548381321487435 := by
  unfold tailWord_449010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094185025830232411980121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10917826735547286431946989 4094185025830232411980121)
  ·
    refine ⟨3070638769372674308985091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4094185025830232411980121 3070638769372674308985091)
    ·
      refine ⟨4605958154059011463477637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3070638769372674308985091 4605958154059011463477637)
      ·
        refine ⟨863617153886064649402057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4605958154059011463477637 863617153886064649402057)
        ·
          refine ⟨647712865414548487051543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863617153886064649402057 647712865414548487051543)
          ·
            refine ⟨971569298121822730577315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647712865414548487051543 971569298121822730577315)
            ·
              refine ⟨1457353947182734095865973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971569298121822730577315 1457353947182734095865973)
              ·
                refine ⟨136626932548381321487435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1457353947182734095865973 136626932548381321487435)
                ·
                  rfl

theorem cell19_449010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_449010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449010 prefixEnd_449010 := by exact prefixLift 449010
  have htrace : WordTrace (prefixWord ++ tailWord_449010) baseStart_449010 baseEnd_449010 := by
    simpa [prefixWord, tailWord_449010, baseEnd_449010] using wordTrace_append hprefix tailTrace_449010
  have hstable : (prefixWord ++ tailWord_449010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449010).length < 2 ^ (prefixWord ++ tailWord_449010).sum := by decide
  have hdescent : baseEnd_449010 < baseStart_449010 := by decide
  rcases family_descends (prefixWord ++ tailWord_449010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449086 : List Nat := [4, 2, 1, 4, 1, 7]
def baseStart_449086 : Nat := 118140960795 + 449086 * 2 ^ 59
def prefixEnd_449086 : Nat := 4983230072969 + 3 ^ 40 * 449086 * 2
def baseEnd_449086 : Nat := 15183339799515073755371

theorem tailTrace_449086 : CollatzResearch.WordTrace tailWord_449086 prefixEnd_449086 15183339799515073755371 := by
  unfold tailWord_449086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047439006380699328460889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10919674700697063085124741 2047439006380699328460889)
  ·
    refine ⟨1535579254785524496345667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2047439006380699328460889 1535579254785524496345667)
    ·
      refine ⟨2303368882178286744518501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1535579254785524496345667 2303368882178286744518501)
      ·
        refine ⟨431881665408428764597219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2303368882178286744518501 431881665408428764597219)
        ·
          refine ⟨647822498112643146895829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431881665408428764597219 647822498112643146895829)
          ·
            refine ⟨15183339799515073755371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 647822498112643146895829 15183339799515073755371)
            ·
              rfl

theorem cell19_449086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 7].length) (baseStart_449086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449086 prefixEnd_449086 := by exact prefixLift 449086
  have htrace : WordTrace (prefixWord ++ tailWord_449086) baseStart_449086 baseEnd_449086 := by
    simpa [prefixWord, tailWord_449086, baseEnd_449086] using wordTrace_append hprefix tailTrace_449086
  have hstable : (prefixWord ++ tailWord_449086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449086).length < 2 ^ (prefixWord ++ tailWord_449086).sum := by decide
  have hdescent : baseEnd_449086 < baseStart_449086 := by decide
  rcases family_descends (prefixWord ++ tailWord_449086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449118 : List Nat := [4, 4, 1, 2, 1, 1, 3, 3]
def baseStart_449118 : Nat := 118140960795 + 449118 * 2 ^ 59
def prefixEnd_449118 : Nat := 4983230072969 + 3 ^ 40 * 449118 * 2
def baseEnd_449118 : Nat := 136659795310269071087141

theorem tailTrace_449118 : CollatzResearch.WordTrace tailWord_449118 prefixEnd_449118 136659795310269071087141 := by
  unfold tailWord_449118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047584898366208011606501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10920452791286442728568005 2047584898366208011606501)
  ·
    refine ⟨383922168443664002176219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2047584898366208011606501 383922168443664002176219)
    ·
      refine ⟨575883252665496003264329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383922168443664002176219 575883252665496003264329)
      ·
        refine ⟨431912439499122002448247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575883252665496003264329 431912439499122002448247)
        ·
          refine ⟨647868659248683003672371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431912439499122002448247 647868659248683003672371)
          ·
            refine ⟨971802988873024505508557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647868659248683003672371 971802988873024505508557)
            ·
              refine ⟨364426120827384189565709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 971802988873024505508557 364426120827384189565709)
              ·
                refine ⟨136659795310269071087141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364426120827384189565709 136659795310269071087141)
                ·
                  rfl

theorem cell19_449118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_449118 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449118 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449118 prefixEnd_449118 := by exact prefixLift 449118
  have htrace : WordTrace (prefixWord ++ tailWord_449118) baseStart_449118 baseEnd_449118 := by
    simpa [prefixWord, tailWord_449118, baseEnd_449118] using wordTrace_append hprefix tailTrace_449118
  have hstable : (prefixWord ++ tailWord_449118).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449118).length < 2 ^ (prefixWord ++ tailWord_449118).sum := by decide
  have hdescent : baseEnd_449118 < baseStart_449118 := by decide
  rcases family_descends (prefixWord ++ tailWord_449118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449217 : List Nat := [1, 2, 6, 2, 1, 1, 2, 4]
def baseStart_449217 : Nat := 118140960795 + 449217 * 2 ^ 59
def prefixEnd_449217 : Nat := 4983230072969 + 3 ^ 40 * 449217 * 2
def baseEnd_449217 : Nat := 136689919508666174886871

theorem tailTrace_449217 : CollatzResearch.WordTrace tailWord_449217 prefixEnd_449217 136689919508666174886871 := by
  unfold tailWord_449217
  simp only [CollatzResearch.WordTrace]
  refine ⟨16384290013571004000705905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10922860009047336000470603 16384290013571004000705905)
  ·
    refine ⟨12288217510178253000529429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16384290013571004000705905 12288217510178253000529429)
    ·
      refine ⟨576010195789605609399817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12288217510178253000529429 576010195789605609399817)
      ·
        refine ⟨432007646842204207049863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576010195789605609399817 432007646842204207049863)
        ·
          refine ⟨648011470263306310574795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432007646842204207049863 648011470263306310574795)
          ·
            refine ⟨972017205394959465862193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648011470263306310574795 972017205394959465862193)
            ·
              refine ⟨729012904046219599396645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972017205394959465862193 729012904046219599396645)
              ·
                refine ⟨136689919508666174886871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 729012904046219599396645 136689919508666174886871)
                ·
                  rfl

theorem cell19_449217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_449217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449217 prefixEnd_449217 := by exact prefixLift 449217
  have htrace : WordTrace (prefixWord ++ tailWord_449217) baseStart_449217 baseEnd_449217 := by
    simpa [prefixWord, tailWord_449217, baseEnd_449217] using wordTrace_append hprefix tailTrace_449217
  have hstable : (prefixWord ++ tailWord_449217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449217).length < 2 ^ (prefixWord ++ tailWord_449217).sum := by decide
  have hdescent : baseEnd_449217 < baseStart_449217 := by decide
  rcases family_descends (prefixWord ++ tailWord_449217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449242 : List Nat := [3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_449242 : Nat := 118140960795 + 449242 * 2 ^ 59
def prefixEnd_449242 : Nat := 4983230072969 + 3 ^ 40 * 449242 * 2
def baseEnd_449242 : Nat := 136697526629473524331247

theorem tailTrace_449242 : CollatzResearch.WordTrace tailWord_449242 prefixEnd_449242 136697526629473524331247 := by
  unfold tailWord_449242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096300459620108317591495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10923467892320288846910653 4096300459620108317591495)
  ·
    refine ⟨6144450689430162476387243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4096300459620108317591495 6144450689430162476387243)
    ·
      refine ⟨9216676034145243714580865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6144450689430162476387243 9216676034145243714580865)
      ·
        refine ⟨6912507025608932785935649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9216676034145243714580865 6912507025608932785935649)
        ·
          refine ⟨5184380269206699589451737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6912507025608932785935649 5184380269206699589451737)
          ·
            refine ⟨3888285201905024692088803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5184380269206699589451737 3888285201905024692088803)
            ·
              refine ⟨5832427802857537038133205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888285201905024692088803 5832427802857537038133205)
              ·
                refine ⟨136697526629473524331247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5832427802857537038133205 136697526629473524331247)
                ·
                  rfl

theorem cell19_449242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_449242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449242 prefixEnd_449242 := by exact prefixLift 449242
  have htrace : WordTrace (prefixWord ++ tailWord_449242) baseStart_449242 baseEnd_449242 := by
    simpa [prefixWord, tailWord_449242, baseEnd_449242] using wordTrace_append hprefix tailTrace_449242
  have hstable : (prefixWord ++ tailWord_449242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449242).length < 2 ^ (prefixWord ++ tailWord_449242).sum := by decide
  have hdescent : baseEnd_449242 < baseStart_449242 := by decide
  rcases family_descends (prefixWord ++ tailWord_449242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449316 : List Nat := [2, 3, 1, 3, 3, 1, 6]
def baseStart_449316 : Nat := 118140960795 + 449316 * 2 ^ 59
def prefixEnd_449316 : Nat := 4983230072969 + 3 ^ 40 * 449316 * 2
def baseEnd_449316 : Nat := 45573347902354426228867

theorem tailTrace_449316 : CollatzResearch.WordTrace tailWord_449316 prefixEnd_449316 45573347902354426228867 := by
  unfold tailWord_449316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8193950420106171954279901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10925267226808229272373201 8193950420106171954279901)
  ·
    refine ⟨3072731407539814482854963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8193950420106171954279901 3072731407539814482854963)
    ·
      refine ⟨4609097111309721724282445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3072731407539814482854963 4609097111309721724282445)
      ·
        refine ⟨1728411416741145646605917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4609097111309721724282445 1728411416741145646605917)
        ·
          refine ⟨648154281277929617477219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1728411416741145646605917 648154281277929617477219)
          ·
            refine ⟨972231421916894426215829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648154281277929617477219 972231421916894426215829)
            ·
              refine ⟨45573347902354426228867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 972231421916894426215829 45573347902354426228867)
              ·
                rfl

theorem cell19_449316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_449316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449316 prefixEnd_449316 := by exact prefixLift 449316
  have htrace : WordTrace (prefixWord ++ tailWord_449316) baseStart_449316 baseEnd_449316 := by
    simpa [prefixWord, tailWord_449316, baseEnd_449316] using wordTrace_append hprefix tailTrace_449316
  have hstable : (prefixWord ++ tailWord_449316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449316).length < 2 ^ (prefixWord ++ tailWord_449316).sum := by decide
  have hdescent : baseEnd_449316 < baseStart_449316 := by decide
  rcases family_descends (prefixWord ++ tailWord_449316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449348 : List Nat := [2, 3, 4, 2, 1, 2, 2, 3]
def baseStart_449348 : Nat := 118140960795 + 449348 * 2 ^ 59
def prefixEnd_449348 : Nat := 4983230072969 + 3 ^ 40 * 449348 * 2
def baseEnd_449348 : Nat := 136729780821696685975403

theorem tailTrace_449348 : CollatzResearch.WordTrace tailWord_449348 prefixEnd_449348 136729780821696685975403 := by
  unfold tailWord_449348
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194533988048206686862349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10926045317397608915816465 8194533988048206686862349)
  ·
    refine ⟨3072950245518077507573381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8194533988048206686862349 3072950245518077507573381)
    ·
      refine ⟨576178171034639532670009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3072950245518077507573381 576178171034639532670009)
      ·
        refine ⟨432133628275979649502507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576178171034639532670009 432133628275979649502507)
        ·
          refine ⟨648200442413969474253761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432133628275979649502507 648200442413969474253761)
          ·
            refine ⟨486150331810477105690321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648200442413969474253761 486150331810477105690321)
            ·
              refine ⟨364612748857857829267741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486150331810477105690321 364612748857857829267741)
              ·
                refine ⟨136729780821696685975403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364612748857857829267741 136729780821696685975403)
                ·
                  rfl

theorem cell19_449348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_449348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449348 prefixEnd_449348 := by exact prefixLift 449348
  have htrace : WordTrace (prefixWord ++ tailWord_449348) baseStart_449348 baseEnd_449348 := by
    simpa [prefixWord, tailWord_449348, baseEnd_449348] using wordTrace_append hprefix tailTrace_449348
  have hstable : (prefixWord ++ tailWord_449348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449348).length < 2 ^ (prefixWord ++ tailWord_449348).sum := by decide
  have hdescent : baseEnd_449348 < baseStart_449348 := by decide
  rcases family_descends (prefixWord ++ tailWord_449348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449350 : List Nat := [6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_449350 : Nat := 118140960795 + 449350 * 2 ^ 59
def prefixEnd_449350 : Nat := 4983230072969 + 3 ^ 40 * 449350 * 2
def baseEnd_449350 : Nat := 136730389391361273930953

theorem tailTrace_449350 : CollatzResearch.WordTrace tailWord_449350 prefixEnd_449350 136730389391361273930953 := by
  unfold tailWord_449350
  simp only [CollatzResearch.WordTrace]
  refine ⟨512160653815286491103047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10926093948059445143531669 512160653815286491103047)
  ·
    refine ⟨768240980722929736654571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 512160653815286491103047 768240980722929736654571)
    ·
      refine ⟨1152361471084394604981857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768240980722929736654571 1152361471084394604981857)
      ·
        refine ⟨864271103313295953736393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1152361471084394604981857 864271103313295953736393)
        ·
          refine ⟨648203327484971965302295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864271103313295953736393 648203327484971965302295)
          ·
            refine ⟨972304991227457947953443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648203327484971965302295 972304991227457947953443)
            ·
              refine ⟨1458457486841186921930165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972304991227457947953443 1458457486841186921930165)
              ·
                refine ⟨136730389391361273930953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1458457486841186921930165 136730389391361273930953)
                ·
                  rfl

theorem cell19_449350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_449350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449350 prefixEnd_449350 := by exact prefixLift 449350
  have htrace : WordTrace (prefixWord ++ tailWord_449350) baseStart_449350 baseEnd_449350 := by
    simpa [prefixWord, tailWord_449350, baseEnd_449350] using wordTrace_append hprefix tailTrace_449350
  have hstable : (prefixWord ++ tailWord_449350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449350).length < 2 ^ (prefixWord ++ tailWord_449350).sum := by decide
  have hdescent : baseEnd_449350 < baseStart_449350 := by decide
  rcases family_descends (prefixWord ++ tailWord_449350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449390 : List Nat := [4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_449390 : Nat := 118140960795 + 449390 * 2 ^ 59
def prefixEnd_449390 : Nat := 4983230072969 + 3 ^ 40 * 449390 * 2
def baseEnd_449390 : Nat := 136742560784653033041955

theorem tailTrace_449390 : CollatzResearch.WordTrace tailWord_449390 prefixEnd_449390 136742560784653033041955 := by
  unfold tailWord_449390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2048824980243031818344203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10927066561296169697835749 2048824980243031818344203)
  ·
    refine ⟨3073237470364547727516305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2048824980243031818344203 3073237470364547727516305)
    ·
      refine ⟨2304928102773410795637229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3073237470364547727516305 2304928102773410795637229)
      ·
        refine ⟨864348038540029048363961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2304928102773410795637229 864348038540029048363961)
        ·
          refine ⟨648261028905021786272971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864348038540029048363961 648261028905021786272971)
          ·
            refine ⟨972391543357532679409457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648261028905021786272971 972391543357532679409457)
            ·
              refine ⟨729293657518149509557093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972391543357532679409457 729293657518149509557093)
              ·
                refine ⟨136742560784653033041955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 729293657518149509557093 136742560784653033041955)
                ·
                  rfl

theorem cell19_449390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_449390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449390 prefixEnd_449390 := by exact prefixLift 449390
  have htrace : WordTrace (prefixWord ++ tailWord_449390) baseStart_449390 baseEnd_449390 := by
    simpa [prefixWord, tailWord_449390, baseEnd_449390] using wordTrace_append hprefix tailTrace_449390
  have hstable : (prefixWord ++ tailWord_449390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449390).length < 2 ^ (prefixWord ++ tailWord_449390).sum := by decide
  have hdescent : baseEnd_449390 < baseStart_449390 := by decide
  rcases family_descends (prefixWord ++ tailWord_449390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449394 : List Nat := [3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_449394 : Nat := 118140960795 + 449394 * 2 ^ 59
def prefixEnd_449394 : Nat := 4983230072969 + 3 ^ 40 * 449394 * 2
def baseEnd_449394 : Nat := 136743777923982208953055

theorem tailTrace_449394 : CollatzResearch.WordTrace tailWord_449394 prefixEnd_449394 136743777923982208953055 := by
  unfold tailWord_449394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097686433482440807474809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10927163822619842153266157 4097686433482440807474809)
  ·
    refine ⟨3073264825111830605606107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4097686433482440807474809 3073264825111830605606107)
    ·
      refine ⟨4609897237667745908409161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3073264825111830605606107 4609897237667745908409161)
      ·
        refine ⟨3457422928250809431306871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4609897237667745908409161 3457422928250809431306871)
        ·
          refine ⟨5186134392376214146960307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457422928250809431306871 5186134392376214146960307)
          ·
            refine ⟨7779201588564321220440461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186134392376214146960307 7779201588564321220440461)
            ·
              refine ⟨2917200595711620457665173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7779201588564321220440461 2917200595711620457665173)
              ·
                refine ⟨136743777923982208953055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2917200595711620457665173 136743777923982208953055)
                ·
                  rfl

theorem cell19_449394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_449394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449394 prefixEnd_449394 := by exact prefixLift 449394
  have htrace : WordTrace (prefixWord ++ tailWord_449394) baseStart_449394 baseEnd_449394 := by
    simpa [prefixWord, tailWord_449394, baseEnd_449394] using wordTrace_append hprefix tailTrace_449394
  have hstable : (prefixWord ++ tailWord_449394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449394).length < 2 ^ (prefixWord ++ tailWord_449394).sum := by decide
  have hdescent : baseEnd_449394 < baseStart_449394 := by decide
  rcases family_descends (prefixWord ++ tailWord_449394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449413 : List Nat := [1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_449413 : Nat := 118140960795 + 449413 * 2 ^ 59
def prefixEnd_449413 : Nat := 4983230072969 + 3 ^ 40 * 449413 * 2
def baseEnd_449413 : Nat := 136749559335795794530781

theorem tailTrace_449413 : CollatzResearch.WordTrace tailWord_449413 prefixEnd_449413 136749559335795794530781 := by
  unfold tailWord_449413
  simp only [CollatzResearch.WordTrace]
  refine ⟨16391438720860929474840893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10927625813907286316560595 16391438720860929474840893)
  ·
    refine ⟨6146789520322848553065335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16391438720860929474840893 6146789520322848553065335)
    ·
      refine ⟨9220184280484272829598003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146789520322848553065335 9220184280484272829598003)
      ·
        refine ⟨13830276420726409244397005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9220184280484272829598003 13830276420726409244397005)
        ·
          refine ⟨5186353657772403466648877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13830276420726409244397005 5186353657772403466648877)
          ·
            refine ⟨1944882621664651299993329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5186353657772403466648877 1944882621664651299993329)
            ·
              refine ⟨1458661966248488474994997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944882621664651299993329 1458661966248488474994997)
              ·
                refine ⟨136749559335795794530781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1458661966248488474994997 136749559335795794530781)
                ·
                  rfl

theorem cell19_449413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_449413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449413 prefixEnd_449413 := by exact prefixLift 449413
  have htrace : WordTrace (prefixWord ++ tailWord_449413) baseStart_449413 baseEnd_449413 := by
    simpa [prefixWord, tailWord_449413, baseEnd_449413] using wordTrace_append hprefix tailTrace_449413
  have hstable : (prefixWord ++ tailWord_449413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449413).length < 2 ^ (prefixWord ++ tailWord_449413).sum := by decide
  have hdescent : baseEnd_449413 < baseStart_449413 := by decide
  rcases family_descends (prefixWord ++ tailWord_449413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449447 : List Nat := [1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_449447 : Nat := 118140960795 + 449447 * 2 ^ 59
def prefixEnd_449447 : Nat := 4983230072969 + 3 ^ 40 * 449447 * 2
def baseEnd_449447 : Nat := 136759905020093789775133

theorem tailTrace_449447 : CollatzResearch.WordTrace tailWord_449447 prefixEnd_449447 136759905020093789775133 := by
  unfold tailWord_449447
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392678802737753281578595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10928452535158502187719063 16392678802737753281578595)
  ·
    refine ⟨24589018204106629922367893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16392678802737753281578595 24589018204106629922367893)
    ·
      refine ⟨1152610228317498277610995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24589018204106629922367893 1152610228317498277610995)
      ·
        refine ⟨1728915342476247416416493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152610228317498277610995 1728915342476247416416493)
        ·
          refine ⟨648343253428592781156185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1728915342476247416416493 648343253428592781156185)
          ·
            refine ⟨486257440071444585867139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648343253428592781156185 486257440071444585867139)
            ·
              refine ⟨729386160107166878800709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486257440071444585867139 729386160107166878800709)
              ·
                refine ⟨136759905020093789775133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 729386160107166878800709 136759905020093789775133)
                ·
                  rfl

theorem cell19_449447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_449447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449447 prefixEnd_449447 := by exact prefixLift 449447
  have htrace : WordTrace (prefixWord ++ tailWord_449447) baseStart_449447 baseEnd_449447 := by
    simpa [prefixWord, tailWord_449447, baseEnd_449447] using wordTrace_append hprefix tailTrace_449447
  have hstable : (prefixWord ++ tailWord_449447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449447).length < 2 ^ (prefixWord ++ tailWord_449447).sum := by decide
  have hdescent : baseEnd_449447 < baseStart_449447 := by decide
  rcases family_descends (prefixWord ++ tailWord_449447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449546 : List Nat := [3, 1, 2, 2, 3, 1, 7]
def baseStart_449546 : Nat := 118140960795 + 449546 * 2 ^ 59
def prefixEnd_449546 : Nat := 4983230072969 + 3 ^ 40 * 449546 * 2
def baseEnd_449546 : Nat := 45596676406163631191621

theorem tailTrace_449546 : CollatzResearch.WordTrace tailWord_449546 prefixEnd_449546 45596676406163631191621 := by
  unfold tailWord_449546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099072407344773297358123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10930859752919395459621661 4099072407344773297358123)
  ·
    refine ⟨6148608611017159946037185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4099072407344773297358123 6148608611017159946037185)
    ·
      refine ⟨4611456458262869959527889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6148608611017159946037185 4611456458262869959527889)
      ·
        refine ⟨3458592343697152469645917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4611456458262869959527889 3458592343697152469645917)
        ·
          refine ⟨1296972128886432176117219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3458592343697152469645917 1296972128886432176117219)
          ·
            refine ⟨1945458193329648264175829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296972128886432176117219 1945458193329648264175829)
            ·
              refine ⟨45596676406163631191621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1945458193329648264175829 45596676406163631191621)
              ·
                rfl

theorem cell19_449546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_449546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449546 prefixEnd_449546 := by exact prefixLift 449546
  have htrace : WordTrace (prefixWord ++ tailWord_449546) baseStart_449546 baseEnd_449546 := by
    simpa [prefixWord, tailWord_449546, baseEnd_449546] using wordTrace_append hprefix tailTrace_449546
  have hstable : (prefixWord ++ tailWord_449546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449546).length < 2 ^ (prefixWord ++ tailWord_449546).sum := by decide
  have hdescent : baseEnd_449546 < baseStart_449546 := by decide
  rcases family_descends (prefixWord ++ tailWord_449546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449601 : List Nat := [1, 2, 5, 1, 4, 6]
def baseStart_449601 : Nat := 118140960795 + 449601 * 2 ^ 59
def prefixEnd_449601 : Nat := 4983230072969 + 3 ^ 40 * 449601 * 2
def baseEnd_449601 : Nat := 15200751653807451372499

theorem tailTrace_449601 : CollatzResearch.WordTrace tailWord_449601 prefixEnd_449601 15200751653807451372499 := by
  unfold tailWord_449601
  simp only [CollatzResearch.WordTrace]
  refine ⟨16398295644179837582684657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10932197096119891721789771 16398295644179837582684657)
  ·
    refine ⟨12298721733134878187013493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16398295644179837582684657 12298721733134878187013493)
    ·
      refine ⟨1153005162481394830032515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12298721733134878187013493 1153005162481394830032515)
      ·
        refine ⟨1729507743722092245048773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153005162481394830032515 1729507743722092245048773)
        ·
          refine ⟨324282701947892295946645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1729507743722092245048773 324282701947892295946645)
          ·
            refine ⟨15200751653807451372499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324282701947892295946645 15200751653807451372499)
            ·
              rfl

theorem cell19_449601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 6].length) (baseStart_449601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449601 prefixEnd_449601 := by exact prefixLift 449601
  have htrace : WordTrace (prefixWord ++ tailWord_449601) baseStart_449601 baseEnd_449601 := by
    simpa [prefixWord, tailWord_449601, baseEnd_449601] using wordTrace_append hprefix tailTrace_449601
  have hstable : (prefixWord ++ tailWord_449601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449601).length < 2 ^ (prefixWord ++ tailWord_449601).sum := by decide
  have hdescent : baseEnd_449601 < baseStart_449601 := by decide
  rcases family_descends (prefixWord ++ tailWord_449601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449639 : List Nat := [1, 1, 5, 1, 1, 4, 3, 3]
def baseStart_449639 : Nat := 118140960795 + 449639 * 2 ^ 59
def prefixEnd_449639 : Nat := 4983230072969 + 3 ^ 40 * 449639 * 2
def baseEnd_449639 : Nat := 136818327707894233507943

theorem tailTrace_449639 : CollatzResearch.WordTrace tailWord_449639 prefixEnd_449639 136818327707894233507943 := by
  unfold tailWord_449639
  simp only [CollatzResearch.WordTrace]
  refine ⟨16399681618042170072567971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10933121078694780048378647 16399681618042170072567971)
  ·
    refine ⟨24599522427063255108851957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16399681618042170072567971 24599522427063255108851957)
    ·
      refine ⟨2306205227537180166454871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24599522427063255108851957 2306205227537180166454871)
      ·
        refine ⟨3459307841305770249682307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306205227537180166454871 3459307841305770249682307)
        ·
          refine ⟨5188961761958655374523461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3459307841305770249682307 5188961761958655374523461)
          ·
            refine ⟨972930330367247882723149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5188961761958655374523461 972930330367247882723149)
            ·
              refine ⟨364848873887717956021181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 972930330367247882723149 364848873887717956021181)
              ·
                refine ⟨136818327707894233507943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364848873887717956021181 136818327707894233507943)
                ·
                  rfl

theorem cell19_449639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_449639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449639 prefixEnd_449639 := by exact prefixLift 449639
  have htrace : WordTrace (prefixWord ++ tailWord_449639) baseStart_449639 baseEnd_449639 := by
    simpa [prefixWord, tailWord_449639, baseEnd_449639] using wordTrace_append hprefix tailTrace_449639
  have hstable : (prefixWord ++ tailWord_449639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449639).length < 2 ^ (prefixWord ++ tailWord_449639).sum := by decide
  have hdescent : baseEnd_449639 < baseStart_449639 := by decide
  rcases family_descends (prefixWord ++ tailWord_449639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449694 : List Nat := [4, 3, 1, 1, 2, 1, 4, 3]
def baseStart_449694 : Nat := 118140960795 + 449694 * 2 ^ 59
def prefixEnd_449694 : Nat := 4983230072969 + 3 ^ 40 * 449694 * 2
def baseEnd_449694 : Nat := 136835063373670402285571

theorem tailTrace_449694 : CollatzResearch.WordTrace tailWord_449694 prefixEnd_449694 136835063373670402285571 := by
  unfold tailWord_449694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050210954105364308227517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10934458421895276310546757 2050210954105364308227517)
  ·
    refine ⟨768829107789511615585319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2050210954105364308227517 768829107789511615585319)
    ·
      refine ⟨1153243661684267423377979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768829107789511615585319 1153243661684267423377979)
      ·
        refine ⟨1729865492526401135066969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153243661684267423377979 1729865492526401135066969)
        ·
          refine ⟨1297399119394800851300227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1729865492526401135066969 1297399119394800851300227)
          ·
            refine ⟨1946098679092201276950341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297399119394800851300227 1946098679092201276950341)
            ·
              refine ⟨364893502329787739428189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1946098679092201276950341 364893502329787739428189)
              ·
                refine ⟨136835063373670402285571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364893502329787739428189 136835063373670402285571)
                ·
                  rfl

theorem cell19_449694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_449694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449694 prefixEnd_449694 := by exact prefixLift 449694
  have htrace : WordTrace (prefixWord ++ tailWord_449694) baseStart_449694 baseEnd_449694 := by
    simpa [prefixWord, tailWord_449694, baseEnd_449694] using wordTrace_append hprefix tailTrace_449694
  have hstable : (prefixWord ++ tailWord_449694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449694).length < 2 ^ (prefixWord ++ tailWord_449694).sum := by decide
  have hdescent : baseEnd_449694 < baseStart_449694 := by decide
  rcases family_descends (prefixWord ++ tailWord_449694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449730 : List Nat := [3, 5, 1, 1, 2, 1, 2, 4]
def baseStart_449730 : Nat := 118140960795 + 449730 * 2 ^ 59
def prefixEnd_449730 : Nat := 4983230072969 + 3 ^ 40 * 449730 * 2
def baseEnd_449730 : Nat := 136846017627632985485473

theorem tailTrace_449730 : CollatzResearch.WordTrace tailWord_449730 prefixEnd_449730 136846017627632985485473 := by
  unfold tailWord_449730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100750165178123153532661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10935333773808328409420429 4100750165178123153532661)
  ·
    refine ⟨384445327985449045643687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4100750165178123153532661 384445327985449045643687)
    ·
      refine ⟨576667991978173568465531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384445327985449045643687 576667991978173568465531)
      ·
        refine ⟨865001987967260352698297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576667991978173568465531 865001987967260352698297)
        ·
          refine ⟨648751490975445264523723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865001987967260352698297 648751490975445264523723)
          ·
            refine ⟨973127236463167896785585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648751490975445264523723 973127236463167896785585)
            ·
              refine ⟨729845427347375922589189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973127236463167896785585 729845427347375922589189)
              ·
                refine ⟨136846017627632985485473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 729845427347375922589189 136846017627632985485473)
                ·
                  rfl

theorem cell19_449730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_449730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449730 prefixEnd_449730 := by exact prefixLift 449730
  have htrace : WordTrace (prefixWord ++ tailWord_449730) baseStart_449730 baseEnd_449730 := by
    simpa [prefixWord, tailWord_449730, baseEnd_449730] using wordTrace_append hprefix tailTrace_449730
  have hstable : (prefixWord ++ tailWord_449730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449730).length < 2 ^ (prefixWord ++ tailWord_449730).sum := by decide
  have hdescent : baseEnd_449730 < baseStart_449730 := by decide
  rcases family_descends (prefixWord ++ tailWord_449730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449793 : List Nat := [1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_449793 : Nat := 118140960795 + 449793 * 2 ^ 59
def prefixEnd_449793 : Nat := 4983230072969 + 3 ^ 40 * 449793 * 2
def baseEnd_449793 : Nat := 136865187572067506085301

theorem tailTrace_449793 : CollatzResearch.WordTrace tailWord_449793 prefixEnd_449793 136865187572067506085301 := by
  unfold tailWord_449793
  simp only [CollatzResearch.WordTrace]
  refine ⟨16405298459484254373674033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10936865639656169582449355 16405298459484254373674033)
  ·
    refine ⟨12303973844613190780255525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16405298459484254373674033 12303973844613190780255525)
    ·
      refine ⟨2306995095864973271297911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12303973844613190780255525 2306995095864973271297911)
      ·
        refine ⟨3460492643797459906946867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306995095864973271297911 3460492643797459906946867)
        ·
          refine ⟨5190738965696189860420301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460492643797459906946867 5190738965696189860420301)
          ·
            refine ⟨1946527112136071197657613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5190738965696189860420301 1946527112136071197657613)
            ·
              refine ⟨729947667051026699121605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1946527112136071197657613 729947667051026699121605)
              ·
                refine ⟨136865187572067506085301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 729947667051026699121605 136865187572067506085301)
                ·
                  rfl

theorem cell19_449793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_449793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449793 prefixEnd_449793 := by exact prefixLift 449793
  have htrace : WordTrace (prefixWord ++ tailWord_449793) baseStart_449793 baseEnd_449793 := by
    simpa [prefixWord, tailWord_449793, baseEnd_449793] using wordTrace_append hprefix tailTrace_449793
  have hstable : (prefixWord ++ tailWord_449793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449793).length < 2 ^ (prefixWord ++ tailWord_449793).sum := by decide
  have hdescent : baseEnd_449793 < baseStart_449793 := by decide
  rcases family_descends (prefixWord ++ tailWord_449793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449888 : List Nat := [2, 1, 1, 3, 4, 3, 5]
def baseStart_449888 : Nat := 118140960795 + 449888 * 2 ^ 59
def prefixEnd_449888 : Nat := 4983230072969 + 3 ^ 40 * 449888 * 2
def baseEnd_449888 : Nat := 45631364877045144657977

theorem tailTrace_449888 : CollatzResearch.WordTrace tailWord_449888 prefixEnd_449888 45631364877045144657977 := by
  unfold tailWord_449888
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204381697070042799191159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10939175596093390398921545 8204381697070042799191159)
  ·
    refine ⟨12306572545605064198786739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8204381697070042799191159 12306572545605064198786739)
    ·
      refine ⟨18459858818407596298180109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12306572545605064198786739 18459858818407596298180109)
      ·
        refine ⟨6922447056902848611817541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18459858818407596298180109 6922447056902848611817541)
        ·
          refine ⟨1297958823169284114715789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6922447056902848611817541 1297958823169284114715789)
          ·
            refine ⟨486734558688481543018421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1297958823169284114715789 486734558688481543018421)
            ·
              refine ⟨45631364877045144657977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 486734558688481543018421 45631364877045144657977)
              ·
                rfl

theorem cell19_449888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_449888 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449888 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449888 prefixEnd_449888 := by exact prefixLift 449888
  have htrace : WordTrace (prefixWord ++ tailWord_449888) baseStart_449888 baseEnd_449888 := by
    simpa [prefixWord, tailWord_449888, baseEnd_449888] using wordTrace_append hprefix tailTrace_449888
  have hstable : (prefixWord ++ tailWord_449888).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449888).length < 2 ^ (prefixWord ++ tailWord_449888).sum := by decide
  have hdescent : baseEnd_449888 < baseStart_449888 := by decide
  rcases family_descends (prefixWord ++ tailWord_449888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449960 : List Nat := [2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_449960 : Nat := 118140960795 + 449960 * 2 ^ 59
def prefixEnd_449960 : Nat := 4983230072969 + 3 ^ 40 * 449960 * 2
def baseEnd_449960 : Nat := 136916003139060600373735

theorem tailTrace_449960 : CollatzResearch.WordTrace tailWord_449960 prefixEnd_449960 136916003139060600373735 := by
  unfold tailWord_449960
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205694724939620947501667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10940926299919494596668889 8205694724939620947501667)
  ·
    refine ⟨12308542087409431421252501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8205694724939620947501667 12308542087409431421252501)
    ·
      refine ⟨576962910347317097871211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12308542087409431421252501 576962910347317097871211)
      ·
        refine ⟨865444365520975646806817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576962910347317097871211 865444365520975646806817)
        ·
          refine ⟨649083274140731735105113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865444365520975646806817 649083274140731735105113)
          ·
            refine ⟨486812455605548801328835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649083274140731735105113 486812455605548801328835)
            ·
              refine ⟨730218683408323201993253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486812455605548801328835 730218683408323201993253)
              ·
                refine ⟨136916003139060600373735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730218683408323201993253 136916003139060600373735)
                ·
                  rfl

theorem cell19_449960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_449960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_449960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_449960 prefixEnd_449960 := by exact prefixLift 449960
  have htrace : WordTrace (prefixWord ++ tailWord_449960) baseStart_449960 baseEnd_449960 := by
    simpa [prefixWord, tailWord_449960, baseEnd_449960] using wordTrace_append hprefix tailTrace_449960
  have hstable : (prefixWord ++ tailWord_449960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449960).length < 2 ^ (prefixWord ++ tailWord_449960).sum := by decide
  have hdescent : baseEnd_449960 < baseStart_449960 := by decide
  rcases family_descends (prefixWord ++ tailWord_449960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450038 : List Nat := [5, 1, 1, 1, 2, 2, 4, 3]
def baseStart_450038 : Nat := 118140960795 + 450038 * 2 ^ 59
def prefixEnd_450038 : Nat := 4983230072969 + 3 ^ 40 * 450038 * 2
def baseEnd_450038 : Nat := 136939737355979530640189

theorem tailTrace_450038 : CollatzResearch.WordTrace tailWord_450038 prefixEnd_450038 136939737355979530640189 := by
  unfold tailWord_450038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025889646474791326021423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10942822895731107477561845 1025889646474791326021423)
  ·
    refine ⟨1538834469712186989032135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025889646474791326021423 1538834469712186989032135)
    ·
      refine ⟨2308251704568280483548203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538834469712186989032135 2308251704568280483548203)
      ·
        refine ⟨3462377556852420725322305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308251704568280483548203 3462377556852420725322305)
        ·
          refine ⟨2596783167639315543991729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3462377556852420725322305 2596783167639315543991729)
          ·
            refine ⟨1947587375729486657993797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596783167639315543991729 1947587375729486657993797)
            ·
              refine ⟨365172632949278748373837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1947587375729486657993797 365172632949278748373837)
              ·
                refine ⟨136939737355979530640189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365172632949278748373837 136939737355979530640189)
                ·
                  rfl

theorem cell19_450038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_450038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450038 prefixEnd_450038 := by exact prefixLift 450038
  have htrace : WordTrace (prefixWord ++ tailWord_450038) baseStart_450038 baseEnd_450038 := by
    simpa [prefixWord, tailWord_450038, baseEnd_450038] using wordTrace_append hprefix tailTrace_450038
  have hstable : (prefixWord ++ tailWord_450038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450038).length < 2 ^ (prefixWord ++ tailWord_450038).sum := by decide
  have hdescent : baseEnd_450038 < baseStart_450038 := by decide
  rcases family_descends (prefixWord ++ tailWord_450038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450040 : List Nat := [2, 1, 2, 1, 1, 5, 4, 3]
def baseStart_450040 : Nat := 118140960795 + 450040 * 2 ^ 59
def prefixEnd_450040 : Nat := 4983230072969 + 3 ^ 40 * 450040 * 2
def baseEnd_450040 : Nat := 136940345925644118595739

theorem tailTrace_450040 : CollatzResearch.WordTrace tailWord_450040 prefixEnd_450040 136940345925644118595739 := by
  unfold tailWord_450040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8207153644794707778957787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10942871526392943705277049 8207153644794707778957787)
  ·
    refine ⟨12310730467192061668436681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8207153644794707778957787 12310730467192061668436681)
    ·
      refine ⟨9233047850394046251327511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12310730467192061668436681 9233047850394046251327511)
      ·
        refine ⟨13849571775591069376991267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9233047850394046251327511 13849571775591069376991267)
        ·
          refine ⟨20774357663386604065486901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13849571775591069376991267 20774357663386604065486901)
          ·
            refine ⟨1947596030942494131139397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20774357663386604065486901 1947596030942494131139397)
            ·
              refine ⟨365174255801717649588637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1947596030942494131139397 365174255801717649588637)
              ·
                refine ⟨136940345925644118595739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365174255801717649588637 136940345925644118595739)
                ·
                  rfl

theorem cell19_450040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_450040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450040 prefixEnd_450040 := by exact prefixLift 450040
  have htrace : WordTrace (prefixWord ++ tailWord_450040) baseStart_450040 baseEnd_450040 := by
    simpa [prefixWord, tailWord_450040, baseEnd_450040] using wordTrace_append hprefix tailTrace_450040
  have hstable : (prefixWord ++ tailWord_450040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450040).length < 2 ^ (prefixWord ++ tailWord_450040).sum := by decide
  have hdescent : baseEnd_450040 < baseStart_450040 := by decide
  rcases family_descends (prefixWord ++ tailWord_450040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450042 : List Nat := [3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_450042 : Nat := 118140960795 + 450042 * 2 ^ 59
def prefixEnd_450042 : Nat := 4983230072969 + 3 ^ 40 * 450042 * 2
def baseEnd_450042 : Nat := 136940954495308706551289

theorem tailTrace_450042 : CollatzResearch.WordTrace tailWord_450042 prefixEnd_450042 136940954495308706551289 := by
  unfold tailWord_450042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4103595058895542474872095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10942920157054779932992253 4103595058895542474872095)
  ·
    refine ⟨6155392588343313712308143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4103595058895542474872095 6155392588343313712308143)
    ·
      refine ⟨9233088882514970568462215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6155392588343313712308143 9233088882514970568462215)
      ·
        refine ⟨13849633323772455852693323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9233088882514970568462215 13849633323772455852693323)
        ·
          refine ⟨20774449985658683779039985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13849633323772455852693323 20774449985658683779039985)
          ·
            refine ⟨15580837489244012834279989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20774449985658683779039985 15580837489244012834279989)
            ·
              refine ⟨1460703514616626203213749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15580837489244012834279989 1460703514616626203213749)
              ·
                refine ⟨136940954495308706551289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1460703514616626203213749 136940954495308706551289)
                ·
                  rfl

theorem cell19_450042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_450042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450042 prefixEnd_450042 := by exact prefixLift 450042
  have htrace : WordTrace (prefixWord ++ tailWord_450042) baseStart_450042 baseEnd_450042 := by
    simpa [prefixWord, tailWord_450042, baseEnd_450042] using wordTrace_append hprefix tailTrace_450042
  have hstable : (prefixWord ++ tailWord_450042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450042).length < 2 ^ (prefixWord ++ tailWord_450042).sum := by decide
  have hdescent : baseEnd_450042 < baseStart_450042 := by decide
  rcases family_descends (prefixWord ++ tailWord_450042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450059 : List Nat := [1, 1, 1, 1, 8, 2, 5]
def baseStart_450059 : Nat := 118140960795 + 450059 * 2 ^ 59
def prefixEnd_450059 : Nat := 4983230072969 + 3 ^ 40 * 450059 * 2
def baseEnd_450059 : Nat := 45648709112485901391155

theorem tailTrace_450059 : CollatzResearch.WordTrace tailWord_450059 prefixEnd_450059 45648709112485901391155 := by
  unfold tailWord_450059
  simp only [CollatzResearch.WordTrace]
  refine ⟨16415000276520581802857231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10943333517680387868571487 16415000276520581802857231)
  ·
    refine ⟨24622500414780872704285847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16415000276520581802857231 24622500414780872704285847)
    ·
      refine ⟨36933750622171309056428771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24622500414780872704285847 36933750622171309056428771)
      ·
        refine ⟨55400625933256963584643157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36933750622171309056428771 55400625933256963584643157)
        ·
          refine ⟨649226085155355042007537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 55400625933256963584643157 649226085155355042007537)
          ·
            refine ⟨486919563866516281505653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649226085155355042007537 486919563866516281505653)
            ·
              refine ⟨45648709112485901391155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 486919563866516281505653 45648709112485901391155)
              ·
                rfl

theorem cell19_450059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_450059 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450059 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450059 prefixEnd_450059 := by exact prefixLift 450059
  have htrace : WordTrace (prefixWord ++ tailWord_450059) baseStart_450059 baseEnd_450059 := by
    simpa [prefixWord, tailWord_450059, baseEnd_450059] using wordTrace_append hprefix tailTrace_450059
  have hstable : (prefixWord ++ tailWord_450059).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450059).length < 2 ^ (prefixWord ++ tailWord_450059).sum := by decide
  have hdescent : baseEnd_450059 < baseStart_450059 := by decide
  rcases family_descends (prefixWord ++ tailWord_450059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450099 : List Nat := [1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_450099 : Nat := 118140960795 + 450099 * 2 ^ 59
def prefixEnd_450099 : Nat := 4983230072969 + 3 ^ 40 * 450099 * 2
def baseEnd_450099 : Nat := 136958298730749463284467

theorem tailTrace_450099 : CollatzResearch.WordTrace tailWord_450099 prefixEnd_450099 136958298730749463284467 := by
  unfold tailWord_450099
  simp only [CollatzResearch.WordTrace]
  refine ⟨16416459196375668634313351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10944306130917112422875567 16416459196375668634313351)
  ·
    refine ⟨24624688794563502951470027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16416459196375668634313351 24624688794563502951470027)
    ·
      refine ⟨36937033191845254427205041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24624688794563502951470027 36937033191845254427205041)
      ·
        refine ⟨27702774893883940820403781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36937033191845254427205041 27702774893883940820403781)
        ·
          refine ⟨5194270292603238903825709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27702774893883940820403781 5194270292603238903825709)
          ·
            refine ⟨1947851359726214588934641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5194270292603238903825709 1947851359726214588934641)
            ·
              refine ⟨1460888519794660941700981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947851359726214588934641 1460888519794660941700981)
              ·
                refine ⟨136958298730749463284467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1460888519794660941700981 136958298730749463284467)
                ·
                  rfl

theorem cell19_450099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_450099 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450099 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450099 prefixEnd_450099 := by exact prefixLift 450099
  have htrace : WordTrace (prefixWord ++ tailWord_450099) baseStart_450099 baseEnd_450099 := by
    simpa [prefixWord, tailWord_450099, baseEnd_450099] using wordTrace_append hprefix tailTrace_450099
  have hstable : (prefixWord ++ tailWord_450099).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450099).length < 2 ^ (prefixWord ++ tailWord_450099).sum := by decide
  have hdescent : baseEnd_450099 < baseStart_450099 := by decide
  rcases family_descends (prefixWord ++ tailWord_450099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450116 : List Nat := [2, 3, 5, 9]
def baseStart_450116 : Nat := 118140960795 + 450116 * 2 ^ 59
def prefixEnd_450116 : Nat := 4983230072969 + 3 ^ 40 * 450116 * 2
def baseEnd_450116 : Nat := 1690907056455536554403

theorem tailTrace_450116 : CollatzResearch.WordTrace tailWord_450116 prefixEnd_450116 1690907056455536554403 := by
  unfold tailWord_450116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8208539618657040268841101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10944719491542720358454801 8208539618657040268841101)
  ·
    refine ⟨3078202356996390100815413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8208539618657040268841101 3078202356996390100815413)
    ·
      refine ⟨288581470968411571951445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3078202356996390100815413 288581470968411571951445)
      ·
        refine ⟨1690907056455536554403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 288581470968411571951445 1690907056455536554403)
        ·
          rfl

theorem cell19_450116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 9].length) (baseStart_450116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450116 prefixEnd_450116 := by exact prefixLift 450116
  have htrace : WordTrace (prefixWord ++ tailWord_450116) baseStart_450116 baseEnd_450116 := by
    simpa [prefixWord, tailWord_450116, baseEnd_450116] using wordTrace_append hprefix tailTrace_450116
  have hstable : (prefixWord ++ tailWord_450116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450116).length < 2 ^ (prefixWord ++ tailWord_450116).sum := by decide
  have hdescent : baseEnd_450116 < baseStart_450116 := by decide
  rcases family_descends (prefixWord ++ tailWord_450116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450135 : List Nat := [1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_450135 : Nat := 118140960795 + 450135 * 2 ^ 59
def prefixEnd_450135 : Nat := 4983230072969 + 3 ^ 40 * 450135 * 2
def baseEnd_450135 : Nat := 136969252984712046484369

theorem tailTrace_450135 : CollatzResearch.WordTrace tailWord_450135 prefixEnd_450135 136969252984712046484369 := by
  unfold tailWord_450135
  simp only [CollatzResearch.WordTrace]
  refine ⟨16417772224245246782623859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10945181482830164521749239 16417772224245246782623859)
  ·
    refine ⟨24626658336367870173935789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16417772224245246782623859 24626658336367870173935789)
    ·
      refine ⟨9234996876137951315225921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24626658336367870173935789 9234996876137951315225921)
      ·
        refine ⟨6926247657103463486419441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9234996876137951315225921 6926247657103463486419441)
        ·
          refine ⟨5194685742827597614814581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6926247657103463486419441 5194685742827597614814581)
          ·
            refine ⟨487001788390087276388867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5194685742827597614814581 487001788390087276388867)
            ·
              refine ⟨730502682585130914583301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487001788390087276388867 730502682585130914583301)
              ·
                refine ⟨136969252984712046484369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730502682585130914583301 136969252984712046484369)
                ·
                  rfl

theorem cell19_450135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_450135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450135 prefixEnd_450135 := by exact prefixLift 450135
  have htrace : WordTrace (prefixWord ++ tailWord_450135) baseStart_450135 baseEnd_450135 := by
    simpa [prefixWord, tailWord_450135, baseEnd_450135] using wordTrace_append hprefix tailTrace_450135
  have hstable : (prefixWord ++ tailWord_450135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450135).length < 2 ^ (prefixWord ++ tailWord_450135).sum := by decide
  have hdescent : baseEnd_450135 < baseStart_450135 := by decide
  rcases family_descends (prefixWord ++ tailWord_450135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450152 : List Nat := [2, 1, 4, 3, 1, 2, 3, 3]
def baseStart_450152 : Nat := 118140960795 + 450152 * 2 ^ 59
def prefixEnd_450152 : Nat := 4983230072969 + 3 ^ 40 * 450152 * 2
def baseEnd_450152 : Nat := 136974425826861044106545

theorem tailTrace_450152 : CollatzResearch.WordTrace tailWord_450152 prefixEnd_450152 136974425826861044106545 := by
  unfold tailWord_450152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8209196132591829342996355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10945594843455772457328473 8209196132591829342996355)
  ·
    refine ⟨12313794198887744014494533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8209196132591829342996355 12313794198887744014494533)
    ·
      refine ⟨2308836412291452002717725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12313794198887744014494533 2308836412291452002717725)
      ·
        refine ⟨865813654609294501019147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2308836412291452002717725 865813654609294501019147)
        ·
          refine ⟨1298720481913941751528721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865813654609294501019147 1298720481913941751528721)
          ·
            refine ⟨974040361435456313646541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298720481913941751528721 974040361435456313646541)
            ·
              refine ⟨365265135538296117617453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974040361435456313646541 365265135538296117617453)
              ·
                refine ⟨136974425826861044106545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365265135538296117617453 136974425826861044106545)
                ·
                  rfl

theorem cell19_450152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_450152 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450152 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450152 prefixEnd_450152 := by exact prefixLift 450152
  have htrace : WordTrace (prefixWord ++ tailWord_450152) baseStart_450152 baseEnd_450152 := by
    simpa [prefixWord, tailWord_450152, baseEnd_450152] using wordTrace_append hprefix tailTrace_450152
  have hstable : (prefixWord ++ tailWord_450152).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450152).length < 2 ^ (prefixWord ++ tailWord_450152).sum := by decide
  have hdescent : baseEnd_450152 < baseStart_450152 := by decide
  rcases family_descends (prefixWord ++ tailWord_450152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450207 : List Nat := [1, 1, 2, 7, 1, 2, 2, 3]
def baseStart_450207 : Nat := 118140960795 + 450207 * 2 ^ 59
def prefixEnd_450207 : Nat := 4983230072969 + 3 ^ 40 * 450207 * 2
def baseEnd_450207 : Nat := 136991161492637212884173

theorem tailTrace_450207 : CollatzResearch.WordTrace tailWord_450207 prefixEnd_450207 136991161492637212884173 := by
  unfold tailWord_450207
  simp only [CollatzResearch.WordTrace]
  refine ⟨16420398279984403079244875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10946932186656268719496583 16420398279984403079244875)
  ·
    refine ⟨24630597419976604618867313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16420398279984403079244875 24630597419976604618867313)
    ·
      refine ⟨18472948064982453464150485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24630597419976604618867313 18472948064982453464150485)
      ·
        refine ⟨432959720273026253066027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18472948064982453464150485 432959720273026253066027)
        ·
          refine ⟨649439580409539379599041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432959720273026253066027 649439580409539379599041)
          ·
            refine ⟨487079685307154534699281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649439580409539379599041 487079685307154534699281)
            ·
              refine ⟨365309763980365901024461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487079685307154534699281 365309763980365901024461)
              ·
                refine ⟨136991161492637212884173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365309763980365901024461 136991161492637212884173)
                ·
                  rfl

theorem cell19_450207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_450207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450207 prefixEnd_450207 := by exact prefixLift 450207
  have htrace : WordTrace (prefixWord ++ tailWord_450207) baseStart_450207 baseEnd_450207 := by
    simpa [prefixWord, tailWord_450207, baseEnd_450207] using wordTrace_append hprefix tailTrace_450207
  have hstable : (prefixWord ++ tailWord_450207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450207).length < 2 ^ (prefixWord ++ tailWord_450207).sum := by decide
  have hdescent : baseEnd_450207 < baseStart_450207 := by decide
  rcases family_descends (prefixWord ++ tailWord_450207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450209 : List Nat := [1, 2, 3, 3, 2, 3, 2, 3]
def baseStart_450209 : Nat := 118140960795 + 450209 * 2 ^ 59
def prefixEnd_450209 : Nat := 4983230072969 + 3 ^ 40 * 450209 * 2
def baseEnd_450209 : Nat := 136991770062301800839723

theorem tailTrace_450209 : CollatzResearch.WordTrace tailWord_450209 prefixEnd_450209 136991770062301800839723 := by
  unfold tailWord_450209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16420471225977157420817681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10946980817318104947211787 16420471225977157420817681)
  ·
    refine ⟨12315353419482868065613261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16420471225977157420817681 12315353419482868065613261)
    ·
      refine ⟨4618257532306075524604973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12315353419482868065613261 4618257532306075524604973)
      ·
        refine ⟨1731846574614778321726865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4618257532306075524604973 1731846574614778321726865)
        ·
          refine ⟨1298884930961083741295149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1731846574614778321726865 1298884930961083741295149)
          ·
            refine ⟨487081849110406402985681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1298884930961083741295149 487081849110406402985681)
            ·
              refine ⟨365311386832804802239261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487081849110406402985681 365311386832804802239261)
              ·
                refine ⟨136991770062301800839723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365311386832804802239261 136991770062301800839723)
                ·
                  rfl

theorem cell19_450209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_450209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450209 prefixEnd_450209 := by exact prefixLift 450209
  have htrace : WordTrace (prefixWord ++ tailWord_450209) baseStart_450209 baseEnd_450209 := by
    simpa [prefixWord, tailWord_450209, baseEnd_450209] using wordTrace_append hprefix tailTrace_450209
  have hstable : (prefixWord ++ tailWord_450209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450209).length < 2 ^ (prefixWord ++ tailWord_450209).sum := by decide
  have hdescent : baseEnd_450209 < baseStart_450209 := by decide
  rcases family_descends (prefixWord ++ tailWord_450209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450302 : List Nat := [4, 2, 2, 1, 4, 1, 1, 4]
def baseStart_450302 : Nat := 118140960795 + 450302 * 2 ^ 59
def prefixEnd_450302 : Nat := 4983230072969 + 3 ^ 40 * 450302 * 2
def baseEnd_450302 : Nat := 137020068551705140772803

theorem tailTrace_450302 : CollatzResearch.WordTrace tailWord_450302 prefixEnd_450302 137020068551705140772803 := by
  unfold tailWord_450302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2052982901830029287994145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10949242143093489535968773 2052982901830029287994145)
  ·
    refine ⟨1539737176372521965995609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2052982901830029287994145 1539737176372521965995609)
    ·
      refine ⟨1154802882279391474496707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1539737176372521965995609 1154802882279391474496707)
      ·
        refine ⟨1732204323419087211745061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154802882279391474496707 1732204323419087211745061)
        ·
          refine ⟨324788310641078852202199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1732204323419087211745061 324788310641078852202199)
          ·
            refine ⟨487182465961618278303299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324788310641078852202199 487182465961618278303299)
            ·
              refine ⟨730773698942427417454949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487182465961618278303299 730773698942427417454949)
              ·
                refine ⟨137020068551705140772803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730773698942427417454949 137020068551705140772803)
                ·
                  rfl

theorem cell19_450302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_450302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450302 prefixEnd_450302 := by exact prefixLift 450302
  have htrace : WordTrace (prefixWord ++ tailWord_450302) baseStart_450302 baseEnd_450302 := by
    simpa [prefixWord, tailWord_450302, baseEnd_450302] using wordTrace_append hprefix tailTrace_450302
  have hstable : (prefixWord ++ tailWord_450302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450302).length < 2 ^ (prefixWord ++ tailWord_450302).sum := by decide
  have hdescent : baseEnd_450302 < baseStart_450302 := by decide
  rcases family_descends (prefixWord ++ tailWord_450302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450317 : List Nat := [1, 7, 2, 1, 1, 1, 3, 3]
def baseStart_450317 : Nat := 118140960795 + 450317 * 2 ^ 59
def prefixEnd_450317 : Nat := 4983230072969 + 3 ^ 40 * 450317 * 2
def baseEnd_450317 : Nat := 137024632824189550439429

theorem tailTrace_450317 : CollatzResearch.WordTrace tailWord_450317 prefixEnd_450317 137024632824189550439429 := by
  unfold tailWord_450317
  simp only [CollatzResearch.WordTrace]
  refine ⟨16424410309585891865749205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10949606873057261243832803 16424410309585891865749205)
  ·
    refine ⟨384947116630919340603497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16424410309585891865749205 384947116630919340603497)
    ·
      refine ⟨288710337473189505452623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384947116630919340603497 288710337473189505452623)
      ·
        refine ⟨433065506209784258178935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288710337473189505452623 433065506209784258178935)
        ·
          refine ⟨649598259314676387268403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433065506209784258178935 649598259314676387268403)
          ·
            refine ⟨974397388972014580902605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649598259314676387268403 974397388972014580902605)
            ·
              refine ⟨365399020864505467838477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974397388972014580902605 365399020864505467838477)
              ·
                refine ⟨137024632824189550439429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365399020864505467838477 137024632824189550439429)
                ·
                  rfl

theorem cell19_450317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 3].length) (baseStart_450317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450317 prefixEnd_450317 := by exact prefixLift 450317
  have htrace : WordTrace (prefixWord ++ tailWord_450317) baseStart_450317 baseEnd_450317 := by
    simpa [prefixWord, tailWord_450317, baseEnd_450317] using wordTrace_append hprefix tailTrace_450317
  have hstable : (prefixWord ++ tailWord_450317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450317).length < 2 ^ (prefixWord ++ tailWord_450317).sum := by decide
  have hdescent : baseEnd_450317 < baseStart_450317 := by decide
  rcases family_descends (prefixWord ++ tailWord_450317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450325 : List Nat := [1, 3, 2, 1, 2, 4, 3, 3]
def baseStart_450325 : Nat := 118140960795 + 450325 * 2 ^ 59
def prefixEnd_450325 : Nat := 4983230072969 + 3 ^ 40 * 450325 * 2
def baseEnd_450325 : Nat := 137027067102847902261629

theorem tailTrace_450325 : CollatzResearch.WordTrace tailWord_450325 prefixEnd_450325 137027067102847902261629 := by
  unfold tailWord_450325
  simp only [CollatzResearch.WordTrace]
  refine ⟨16424702093556909232040429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10949801395704606154693619 16424702093556909232040429)
  ·
    refine ⟨6159263285083840962015161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16424702093556909232040429 6159263285083840962015161)
    ·
      refine ⟨4619447463812880721511371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6159263285083840962015161 4619447463812880721511371)
      ·
        refine ⟨6929171195719321082267057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619447463812880721511371 6929171195719321082267057)
        ·
          refine ⟨5196878396789490811700293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6929171195719321082267057 5196878396789490811700293)
          ·
            refine ⟨974414699398029527193805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5196878396789490811700293 974414699398029527193805)
            ·
              refine ⟨365405512274261072697677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974414699398029527193805 365405512274261072697677)
              ·
                refine ⟨137027067102847902261629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365405512274261072697677 137027067102847902261629)
                ·
                  rfl

theorem cell19_450325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_450325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450325 prefixEnd_450325 := by exact prefixLift 450325
  have htrace : WordTrace (prefixWord ++ tailWord_450325) baseStart_450325 baseEnd_450325 := by
    simpa [prefixWord, tailWord_450325, baseEnd_450325] using wordTrace_append hprefix tailTrace_450325
  have hstable : (prefixWord ++ tailWord_450325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450325).length < 2 ^ (prefixWord ++ tailWord_450325).sum := by decide
  have hdescent : baseEnd_450325 < baseStart_450325 := by decide
  rcases family_descends (prefixWord ++ tailWord_450325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450380 : List Nat := [2, 2, 1, 3, 4, 2, 2, 3]
def baseStart_450380 : Nat := 118140960795 + 450380 * 2 ^ 59
def prefixEnd_450380 : Nat := 4983230072969 + 3 ^ 40 * 450380 * 2
def baseEnd_450380 : Nat := 137043802768624071039257

theorem tailTrace_450380 : CollatzResearch.WordTrace tailWord_450380 prefixEnd_450380 137043802768624071039257 := by
  unfold tailWord_450380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8213354054178826812646297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10951138738905102416861729 8213354054178826812646297)
  ·
    refine ⟨6160015540634120109484723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8213354054178826812646297 6160015540634120109484723)
    ·
      refine ⟨9240023310951180164227085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6160015540634120109484723 9240023310951180164227085)
      ·
        refine ⟨3465008741606692561585157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9240023310951180164227085 3465008741606692561585157)
        ·
          refine ⟨649689139051254855297217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3465008741606692561585157 649689139051254855297217)
          ·
            refine ⟨487266854288441141472913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649689139051254855297217 487266854288441141472913)
            ·
              refine ⟨365450140716330856104685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487266854288441141472913 365450140716330856104685)
              ·
                refine ⟨137043802768624071039257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365450140716330856104685 137043802768624071039257)
                ·
                  rfl

theorem cell19_450380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_450380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450380 prefixEnd_450380 := by exact prefixLift 450380
  have htrace : WordTrace (prefixWord ++ tailWord_450380) baseStart_450380 baseEnd_450380 := by
    simpa [prefixWord, tailWord_450380, baseEnd_450380] using wordTrace_append hprefix tailTrace_450380
  have hstable : (prefixWord ++ tailWord_450380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450380).length < 2 ^ (prefixWord ++ tailWord_450380).sum := by decide
  have hdescent : baseEnd_450380 < baseStart_450380 := by decide
  rcases family_descends (prefixWord ++ tailWord_450380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450454 : List Nat := [5, 3, 1, 1, 3, 6]
def baseStart_450454 : Nat := 118140960795 + 450454 * 2 ^ 59
def prefixEnd_450454 : Nat := 4983230072969 + 3 ^ 40 * 450454 * 2
def baseEnd_450454 : Nat := 15229591094023758377179

theorem tailTrace_450454 : CollatzResearch.WordTrace tailWord_450454 prefixEnd_450454 15229591094023758377179 := by
  unfold tailWord_450454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026837944380597766467901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10952938073393042842324277 1026837944380597766467901)
  ·
    refine ⟨385064229142724162425463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1026837944380597766467901 385064229142724162425463)
    ·
      refine ⟨577596343714086243638195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385064229142724162425463 577596343714086243638195)
      ·
        refine ⟨866394515571129365457293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577596343714086243638195 866394515571129365457293)
        ·
          refine ⟨324897943339173512046485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 866394515571129365457293 324897943339173512046485)
          ·
            refine ⟨15229591094023758377179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324897943339173512046485 15229591094023758377179)
            ·
              rfl

theorem cell19_450454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 6].length) (baseStart_450454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450454 prefixEnd_450454 := by exact prefixLift 450454
  have htrace : WordTrace (prefixWord ++ tailWord_450454) baseStart_450454 baseEnd_450454 := by
    simpa [prefixWord, tailWord_450454, baseEnd_450454] using wordTrace_append hprefix tailTrace_450454
  have hstable : (prefixWord ++ tailWord_450454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450454).length < 2 ^ (prefixWord ++ tailWord_450454).sum := by decide
  have hdescent : baseEnd_450454 < baseStart_450454 := by decide
  rcases family_descends (prefixWord ++ tailWord_450454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450460 : List Nat := [2, 2, 3, 3, 1, 8]
def baseStart_450460 : Nat := 118140960795 + 450460 * 2 ^ 59
def prefixEnd_450460 : Nat := 4983230072969 + 3 ^ 40 * 450460 * 2
def baseEnd_450460 : Nat := 15229793950578621029029

theorem tailTrace_450460 : CollatzResearch.WordTrace tailWord_450460 prefixEnd_450460 15229793950578621029029 := by
  unfold tailWord_450460
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214812974033913644102417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10953083965378551525469889 8214812974033913644102417)
  ·
    refine ⟨6161109730525435233076813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8214812974033913644102417 6161109730525435233076813)
    ·
      refine ⟨2310416148947038212403805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6161109730525435233076813 2310416148947038212403805)
      ·
        refine ⟨866406055855139329651427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2310416148947038212403805 866406055855139329651427)
        ·
          refine ⟨1299609083782708994477141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866406055855139329651427 1299609083782708994477141)
          ·
            refine ⟨15229793950578621029029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1299609083782708994477141 15229793950578621029029)
            ·
              rfl

theorem cell19_450460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 8].length) (baseStart_450460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450460 prefixEnd_450460 := by exact prefixLift 450460
  have htrace : WordTrace (prefixWord ++ tailWord_450460) baseStart_450460 baseEnd_450460 := by
    simpa [prefixWord, tailWord_450460, baseEnd_450460] using wordTrace_append hprefix tailTrace_450460
  have hstable : (prefixWord ++ tailWord_450460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450460).length < 2 ^ (prefixWord ++ tailWord_450460).sum := by decide
  have hdescent : baseEnd_450460 < baseStart_450460 := by decide
  rcases family_descends (prefixWord ++ tailWord_450460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450517 : List Nat := [1, 3, 2, 3, 2, 2, 6]
def baseStart_450517 : Nat := 118140960795 + 450517 * 2 ^ 59
def prefixEnd_450517 : Nat := 4983230072969 + 3 ^ 40 * 450517 * 2
def baseEnd_450517 : Nat := 45695163263549448664813

theorem tailTrace_450517 : CollatzResearch.WordTrace tailWord_450517 prefixEnd_450517 45695163263549448664813 := by
  unfold tailWord_450517
  simp only [CollatzResearch.WordTrace]
  refine ⟨16431704908861326023029805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10954469939240884015353203 16431704908861326023029805)
  ·
    refine ⟨6161889340822997258636177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16431704908861326023029805 6161889340822997258636177)
    ·
      refine ⟨4621417005617247943977133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6161889340822997258636177 4621417005617247943977133)
      ·
        refine ⟨1733031377106467978991425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4621417005617247943977133 1733031377106467978991425)
        ·
          refine ⟨1299773532829850984243569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733031377106467978991425 1299773532829850984243569)
          ·
            refine ⟨974830149622388238182677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299773532829850984243569 974830149622388238182677)
            ·
              refine ⟨45695163263549448664813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 974830149622388238182677 45695163263549448664813)
              ·
                rfl

theorem cell19_450517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_450517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450517 prefixEnd_450517 := by exact prefixLift 450517
  have htrace : WordTrace (prefixWord ++ tailWord_450517) baseStart_450517 baseEnd_450517 := by
    simpa [prefixWord, tailWord_450517, baseEnd_450517] using wordTrace_append hprefix tailTrace_450517
  have hstable : (prefixWord ++ tailWord_450517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450517).length < 2 ^ (prefixWord ++ tailWord_450517).sum := by decide
  have hdescent : baseEnd_450517 < baseStart_450517 := by decide
  rcases family_descends (prefixWord ++ tailWord_450517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450519 : List Nat := [1, 1, 3, 2, 1, 1, 10]
def baseStart_450519 : Nat := 118140960795 + 450519 * 2 ^ 59
def prefixEnd_450519 : Nat := 4983230072969 + 3 ^ 40 * 450519 * 2
def baseEnd_450519 : Nat := 45695366120104311316663

theorem tailTrace_450519 : CollatzResearch.WordTrace tailWord_450519 prefixEnd_450519 45695366120104311316663 := by
  unfold tailWord_450519
  simp only [CollatzResearch.WordTrace]
  refine ⟨16431777854854080364602611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10954518569902720243068407 16431777854854080364602611)
  ·
    refine ⟨24647666782281120546903917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16431777854854080364602611 24647666782281120546903917)
    ·
      refine ⟨9242875043355420205088969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24647666782281120546903917 9242875043355420205088969)
      ·
        refine ⟨6932156282516565153816727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9242875043355420205088969 6932156282516565153816727)
        ·
          refine ⟨10398234423774847730725091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6932156282516565153816727 10398234423774847730725091)
          ·
            refine ⟨15597351635662271596087637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10398234423774847730725091 15597351635662271596087637)
            ·
              refine ⟨45695366120104311316663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15597351635662271596087637 45695366120104311316663)
              ·
                rfl

theorem cell19_450519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_450519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450519 prefixEnd_450519 := by exact prefixLift 450519
  have htrace : WordTrace (prefixWord ++ tailWord_450519) baseStart_450519 baseEnd_450519 := by
    simpa [prefixWord, tailWord_450519, baseEnd_450519] using wordTrace_append hprefix tailTrace_450519
  have hstable : (prefixWord ++ tailWord_450519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450519).length < 2 ^ (prefixWord ++ tailWord_450519).sum := by decide
  have hdescent : baseEnd_450519 < baseStart_450519 := by decide
  rcases family_descends (prefixWord ++ tailWord_450519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450553 : List Nat := [1, 2, 1, 3, 1, 6, 2, 3]
def baseStart_450553 : Nat := 118140960795 + 450553 * 2 ^ 59
def prefixEnd_450553 : Nat := 4983230072969 + 3 ^ 40 * 450553 * 2
def baseEnd_450553 : Nat := 137096444044610929194341

theorem tailTrace_450553 : CollatzResearch.WordTrace tailWord_450553 prefixEnd_450553 137096444044610929194341 := by
  unfold tailWord_450553
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433017936730904171340313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10955345291153936114226875 16433017936730904171340313)
  ·
    refine ⟨12324763452548178128505235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16433017936730904171340313 12324763452548178128505235)
    ·
      refine ⟨18487145178822267192757853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12324763452548178128505235 18487145178822267192757853)
      ·
        refine ⟨6932679442058350197284195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18487145178822267192757853 6932679442058350197284195)
        ·
          refine ⟨10399019163087525295926293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6932679442058350197284195 10399019163087525295926293)
          ·
            refine ⟨487454023269727748246545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10399019163087525295926293 487454023269727748246545)
            ·
              refine ⟨365590517452295811184909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487454023269727748246545 365590517452295811184909)
              ·
                refine ⟨137096444044610929194341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365590517452295811184909 137096444044610929194341)
                ·
                  rfl

theorem cell19_450553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_450553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450553 prefixEnd_450553 := by exact prefixLift 450553
  have htrace : WordTrace (prefixWord ++ tailWord_450553) baseStart_450553 baseEnd_450553 := by
    simpa [prefixWord, tailWord_450553, baseEnd_450553] using wordTrace_append hprefix tailTrace_450553
  have hstable : (prefixWord ++ tailWord_450553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450553).length < 2 ^ (prefixWord ++ tailWord_450553).sum := by decide
  have hdescent : baseEnd_450553 < baseStart_450553 := by decide
  rcases family_descends (prefixWord ++ tailWord_450553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450555 : List Nat := [1, 1, 1, 1, 1, 3, 8, 3]
def baseStart_450555 : Nat := 118140960795 + 450555 * 2 ^ 59
def prefixEnd_450555 : Nat := 4983230072969 + 3 ^ 40 * 450555 * 2
def baseEnd_450555 : Nat := 137097052614275517149891

theorem tailTrace_450555 : CollatzResearch.WordTrace tailWord_450555 prefixEnd_450555 137097052614275517149891 := by
  unfold tailWord_450555
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433090882723658512913119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10955393921815772341942079 16433090882723658512913119)
  ·
    refine ⟨24649636324085487769369679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16433090882723658512913119 24649636324085487769369679)
    ·
      refine ⟨36974454486128231654054519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24649636324085487769369679 36974454486128231654054519)
      ·
        refine ⟨55461681729192347481081779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36974454486128231654054519 55461681729192347481081779)
        ·
          refine ⟨83192522593788521221622669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55461681729192347481081779 83192522593788521221622669)
          ·
            refine ⟨31197195972670695458108501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83192522593788521221622669 31197195972670695458108501)
            ·
              refine ⟨365592140304734712399709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 31197195972670695458108501 365592140304734712399709)
              ·
                refine ⟨137097052614275517149891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365592140304734712399709 137097052614275517149891)
                ·
                  rfl

theorem cell19_450555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_450555 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450555 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450555 prefixEnd_450555 := by exact prefixLift 450555
  have htrace : WordTrace (prefixWord ++ tailWord_450555) baseStart_450555 baseEnd_450555 := by
    simpa [prefixWord, tailWord_450555, baseEnd_450555] using wordTrace_append hprefix tailTrace_450555
  have hstable : (prefixWord ++ tailWord_450555).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450555).length < 2 ^ (prefixWord ++ tailWord_450555).sum := by decide
  have hdescent : baseEnd_450555 < baseStart_450555 := by decide
  rcases family_descends (prefixWord ++ tailWord_450555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450566 : List Nat := [6, 2, 1, 2, 1, 2, 5]
def baseStart_450566 : Nat := 118140960795 + 450566 * 2 ^ 59
def prefixEnd_450566 : Nat := 4983230072969 + 3 ^ 40 * 450566 * 2
def baseEnd_450566 : Nat := 45700133249143583635139

theorem tailTrace_450566 : CollatzResearch.WordTrace tailWord_450566 prefixEnd_450566 45700133249143583635139 := by
  unfold tailWord_450566
  simp only [CollatzResearch.WordTrace]
  refine ⟨513546627677618980986361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10955661390455871594375701 513546627677618980986361)
  ·
    refine ⟨385159970758214235739771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 513546627677618980986361 385159970758214235739771)
    ·
      refine ⟨577739956137321353609657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385159970758214235739771 577739956137321353609657)
      ·
        refine ⟨433304967102991015207243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577739956137321353609657 433304967102991015207243)
        ·
          refine ⟨649957450654486522810865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433304967102991015207243 649957450654486522810865)
          ·
            refine ⟨487468087990864892108149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649957450654486522810865 487468087990864892108149)
            ·
              refine ⟨45700133249143583635139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 487468087990864892108149 45700133249143583635139)
              ·
                rfl

theorem cell19_450566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_450566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450566 prefixEnd_450566 := by exact prefixLift 450566
  have htrace : WordTrace (prefixWord ++ tailWord_450566) baseStart_450566 baseEnd_450566 := by
    simpa [prefixWord, tailWord_450566, baseEnd_450566] using wordTrace_append hprefix tailTrace_450566
  have hstable : (prefixWord ++ tailWord_450566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450566).length < 2 ^ (prefixWord ++ tailWord_450566).sum := by decide
  have hdescent : baseEnd_450566 < baseStart_450566 := by decide
  rcases family_descends (prefixWord ++ tailWord_450566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450646 : List Nat := [5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_450646 : Nat := 118140960795 + 450646 * 2 ^ 59
def prefixEnd_450646 : Nat := 4983230072969 + 3 ^ 40 * 450646 * 2
def baseEnd_450646 : Nat := 137124742534014269127421

theorem tailTrace_450646 : CollatzResearch.WordTrace tailWord_450646 prefixEnd_450646 137124742534014269127421 := by
  unfold tailWord_450646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027275620337123815904737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10957606616929320702983861 1027275620337123815904737)
  ·
    refine ⟨770456715252842861928553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1027275620337123815904737 770456715252842861928553)
    ·
      refine ⟨577842536439632146446415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 770456715252842861928553 577842536439632146446415)
      ·
        refine ⟨866763804659448219669623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577842536439632146446415 866763804659448219669623)
        ·
          refine ⟨1300145706989172329504435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866763804659448219669623 1300145706989172329504435)
          ·
            refine ⟨1950218560483758494256653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300145706989172329504435 1950218560483758494256653)
            ·
              refine ⟨731331960181409435346245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950218560483758494256653 731331960181409435346245)
              ·
                refine ⟨137124742534014269127421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 731331960181409435346245 137124742534014269127421)
                ·
                  rfl

theorem cell19_450646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_450646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450646 prefixEnd_450646 := by exact prefixLift 450646
  have htrace : WordTrace (prefixWord ++ tailWord_450646) baseStart_450646 baseEnd_450646 := by
    simpa [prefixWord, tailWord_450646, baseEnd_450646] using wordTrace_append hprefix tailTrace_450646
  have hstable : (prefixWord ++ tailWord_450646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450646).length < 2 ^ (prefixWord ++ tailWord_450646).sum := by decide
  have hdescent : baseEnd_450646 < baseStart_450646 := by decide
  rcases family_descends (prefixWord ++ tailWord_450646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450709 : List Nat := [1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_450709 : Nat := 118140960795 + 450709 * 2 ^ 59
def prefixEnd_450709 : Nat := 4983230072969 + 3 ^ 40 * 450709 * 2
def baseEnd_450709 : Nat := 137143912478448789727249

theorem tailTrace_450709 : CollatzResearch.WordTrace tailWord_450709 prefixEnd_450709 137143912478448789727249 := by
  unfold tailWord_450709
  simp only [CollatzResearch.WordTrace]
  refine ⟨16438707724165742814019181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10959138482777161876012787 16438707724165742814019181)
  ·
    refine ⟨6164515396562153555257193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16438707724165742814019181 6164515396562153555257193)
    ·
      refine ⟨4623386547421615166442895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6164515396562153555257193 4623386547421615166442895)
      ·
        refine ⟨6935079821132422749664343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623386547421615166442895 6935079821132422749664343)
        ·
          refine ⟨10402619731698634124496515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6935079821132422749664343 10402619731698634124496515)
          ·
            refine ⟨15603929597547951186744773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402619731698634124496515 15603929597547951186744773)
            ·
              refine ⟨2925736799540240847514645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15603929597547951186744773 2925736799540240847514645)
              ·
                refine ⟨137143912478448789727249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2925736799540240847514645 137143912478448789727249)
                ·
                  rfl

theorem cell19_450709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_450709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450709 prefixEnd_450709 := by exact prefixLift 450709
  have htrace : WordTrace (prefixWord ++ tailWord_450709) baseStart_450709 baseEnd_450709 := by
    simpa [prefixWord, tailWord_450709, baseEnd_450709] using wordTrace_append hprefix tailTrace_450709
  have hstable : (prefixWord ++ tailWord_450709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450709).length < 2 ^ (prefixWord ++ tailWord_450709).sum := by decide
  have hdescent : baseEnd_450709 < baseStart_450709 := by decide
  rcases family_descends (prefixWord ++ tailWord_450709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450722 : List Nat := [3, 3, 1, 3, 1, 3, 2, 3]
def baseStart_450722 : Nat := 118140960795 + 450722 * 2 ^ 59
def prefixEnd_450722 : Nat := 4983230072969 + 3 ^ 40 * 450722 * 2
def baseEnd_450722 : Nat := 137147868181268611438325

theorem tailTrace_450722 : CollatzResearch.WordTrace tailWord_450722 prefixEnd_450722 137147868181268611438325 := by
  unfold tailWord_450722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109795468279661508560605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10959454582079097356161613 4109795468279661508560605)
  ·
    refine ⟨1541173300604873065710227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4109795468279661508560605 1541173300604873065710227)
    ·
      refine ⟨2311759950907309598565341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541173300604873065710227 2311759950907309598565341)
      ·
        refine ⟨866909981590241099462003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2311759950907309598565341 866909981590241099462003)
        ·
          refine ⟨1300364972385361649193005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866909981590241099462003 1300364972385361649193005)
          ·
            refine ⟨487636864644510618447377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1300364972385361649193005 487636864644510618447377)
            ·
              refine ⟨365727648483382963835533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487636864644510618447377 365727648483382963835533)
              ·
                refine ⟨137147868181268611438325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365727648483382963835533 137147868181268611438325)
                ·
                  rfl

theorem cell19_450722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_450722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450722 prefixEnd_450722 := by exact prefixLift 450722
  have htrace : WordTrace (prefixWord ++ tailWord_450722) baseStart_450722 baseEnd_450722 := by
    simpa [prefixWord, tailWord_450722, baseEnd_450722] using wordTrace_append hprefix tailTrace_450722
  have hstable : (prefixWord ++ tailWord_450722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450722).length < 2 ^ (prefixWord ++ tailWord_450722).sum := by decide
  have hdescent : baseEnd_450722 < baseStart_450722 := by decide
  rcases family_descends (prefixWord ++ tailWord_450722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450741 : List Nat := [1, 3, 3, 4, 2, 1, 5]
def baseStart_450741 : Nat := 118140960795 + 450741 * 2 ^ 59
def prefixEnd_450741 : Nat := 4983230072969 + 3 ^ 40 * 450741 * 2
def baseEnd_450741 : Nat := 45717883197694065672017

theorem tailTrace_450741 : CollatzResearch.WordTrace tailWord_450741 prefixEnd_450741 45717883197694065672017 := by
  unfold tailWord_450741
  simp only [CollatzResearch.WordTrace]
  refine ⟨16439874860049812279184077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10959916573366541519456051 16439874860049812279184077)
  ·
    refine ⟨6164953072518679604694029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16439874860049812279184077 6164953072518679604694029)
    ·
      refine ⟨2311857402194504851760261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6164953072518679604694029 2311857402194504851760261)
      ·
        refine ⟨433473262911469659705049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2311857402194504851760261 433473262911469659705049)
        ·
          refine ⟨325104947183602244778787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433473262911469659705049 325104947183602244778787)
          ·
            refine ⟨487657420775403367168181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325104947183602244778787 487657420775403367168181)
            ·
              refine ⟨45717883197694065672017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 487657420775403367168181 45717883197694065672017)
              ·
                rfl

theorem cell19_450741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_450741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450741 prefixEnd_450741 := by exact prefixLift 450741
  have htrace : WordTrace (prefixWord ++ tailWord_450741) baseStart_450741 baseEnd_450741 := by
    simpa [prefixWord, tailWord_450741, baseEnd_450741] using wordTrace_append hprefix tailTrace_450741
  have hstable : (prefixWord ++ tailWord_450741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450741).length < 2 ^ (prefixWord ++ tailWord_450741).sum := by decide
  have hdescent : baseEnd_450741 < baseStart_450741 := by decide
  rcases family_descends (prefixWord ++ tailWord_450741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450785 : List Nat := [1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_450785 : Nat := 118140960795 + 450785 * 2 ^ 59
def prefixEnd_450785 : Nat := 4983230072969 + 3 ^ 40 * 450785 * 2
def baseEnd_450785 : Nat := 137167038125703132038153

theorem tailTrace_450785 : CollatzResearch.WordTrace tailWord_450785 prefixEnd_450785 137167038125703132038153 := by
  unfold tailWord_450785
  simp only [CollatzResearch.WordTrace]
  refine ⟨16441479671890407793785809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10960986447926938529190539 16441479671890407793785809)
  ·
    refine ⟨12331109753917805845339357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16441479671890407793785809 12331109753917805845339357)
    ·
      refine ⟨4624166157719177192002259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12331109753917805845339357 4624166157719177192002259)
      ·
        refine ⟨6936249236578765788003389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4624166157719177192002259 6936249236578765788003389)
        ·
          refine ⟨2601093463717037170501271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6936249236578765788003389 2601093463717037170501271)
          ·
            refine ⟨3901640195575555755751907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601093463717037170501271 3901640195575555755751907)
            ·
              refine ⟨5852460293363333633627861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901640195575555755751907 5852460293363333633627861)
              ·
                refine ⟨137167038125703132038153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5852460293363333633627861 137167038125703132038153)
                ·
                  rfl

theorem cell19_450785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_450785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450785 prefixEnd_450785 := by exact prefixLift 450785
  have htrace : WordTrace (prefixWord ++ tailWord_450785) baseStart_450785 baseEnd_450785 := by
    simpa [prefixWord, tailWord_450785, baseEnd_450785] using wordTrace_append hprefix tailTrace_450785
  have hstable : (prefixWord ++ tailWord_450785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450785).length < 2 ^ (prefixWord ++ tailWord_450785).sum := by decide
  have hdescent : baseEnd_450785 < baseStart_450785 := by decide
  rcases family_descends (prefixWord ++ tailWord_450785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450840 : List Nat := [2, 1, 2, 3, 1, 2, 5, 3]
def baseStart_450840 : Nat := 118140960795 + 450840 * 2 ^ 59
def prefixEnd_450840 : Nat := 4983230072969 + 3 ^ 40 * 450840 * 2
def baseEnd_450840 : Nat := 137183773791479300815781

theorem tailTrace_450840 : CollatzResearch.WordTrace tailWord_450840 prefixEnd_450840 137183773791479300815781 := by
  unfold tailWord_450840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8221742843345576093518987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10962323791127434791358649 8221742843345576093518987)
  ·
    refine ⟨12332614265018364140278481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8221742843345576093518987 12332614265018364140278481)
    ·
      refine ⟨9249460698763773105208861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12332614265018364140278481 9249460698763773105208861)
      ·
        refine ⟨3468547762036414914453323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9249460698763773105208861 3468547762036414914453323)
        ·
          refine ⟨5202821643054622371679985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468547762036414914453323 5202821643054622371679985)
          ·
            refine ⟨3902116232290966778759989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5202821643054622371679985 3902116232290966778759989)
            ·
              refine ⟨365823396777278135508749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3902116232290966778759989 365823396777278135508749)
              ·
                refine ⟨137183773791479300815781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365823396777278135508749 137183773791479300815781)
                ·
                  rfl

theorem cell19_450840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_450840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450840 prefixEnd_450840 := by exact prefixLift 450840
  have htrace : WordTrace (prefixWord ++ tailWord_450840) baseStart_450840 baseEnd_450840 := by
    simpa [prefixWord, tailWord_450840, baseEnd_450840] using wordTrace_append hprefix tailTrace_450840
  have hstable : (prefixWord ++ tailWord_450840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450840).length < 2 ^ (prefixWord ++ tailWord_450840).sum := by decide
  have hdescent : baseEnd_450840 < baseStart_450840 := by decide
  rcases family_descends (prefixWord ++ tailWord_450840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450855 : List Nat := [1, 1, 8, 1, 1, 1, 6]
def baseStart_450855 : Nat := 118140960795 + 450855 * 2 ^ 59
def prefixEnd_450855 : Nat := 4983230072969 + 3 ^ 40 * 450855 * 2
def baseEnd_450855 : Nat := 45729446021321236827469

theorem tailTrace_450855 : CollatzResearch.WordTrace tailWord_450855 prefixEnd_450855 45729446021321236827469 := by
  unfold tailWord_450855
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444032781636809748834019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10962688521091206499222679 16444032781636809748834019)
  ·
    refine ⟨24666049172455214623251029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16444032781636809748834019 24666049172455214623251029)
    ·
      refine ⟨289055263739709546366223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 24666049172455214623251029 289055263739709546366223)
      ·
        refine ⟨433582895609564319549335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289055263739709546366223 433582895609564319549335)
        ·
          refine ⟨650374343414346479324003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433582895609564319549335 650374343414346479324003)
          ·
            refine ⟨975561515121519718986005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650374343414346479324003 975561515121519718986005)
            ·
              refine ⟨45729446021321236827469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 975561515121519718986005 45729446021321236827469)
              ·
                rfl

theorem cell19_450855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_450855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450855 prefixEnd_450855 := by exact prefixLift 450855
  have htrace : WordTrace (prefixWord ++ tailWord_450855) baseStart_450855 baseEnd_450855 := by
    simpa [prefixWord, tailWord_450855, baseEnd_450855] using wordTrace_append hprefix tailTrace_450855
  have hstable : (prefixWord ++ tailWord_450855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450855).length < 2 ^ (prefixWord ++ tailWord_450855).sum := by decide
  have hdescent : baseEnd_450855 < baseStart_450855 := by decide
  rcases family_descends (prefixWord ++ tailWord_450855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450897 : List Nat := [1, 2, 2, 1, 4, 2, 4, 3]
def baseStart_450897 : Nat := 118140960795 + 450897 * 2 ^ 59
def prefixEnd_450897 : Nat := 4983230072969 + 3 ^ 40 * 450897 * 2
def baseEnd_450897 : Nat := 137201118026920057548959

theorem tailTrace_450897 : CollatzResearch.WordTrace tailWord_450897 prefixEnd_450897 137201118026920057548959 := by
  unfold tailWord_450897
  simp only [CollatzResearch.WordTrace]
  refine ⟨16445564647484650921862945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10963709764989767281241963 16445564647484650921862945)
  ·
    refine ⟨12334173485613488191397209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16445564647484650921862945 12334173485613488191397209)
    ·
      refine ⟨9250630114210116143547907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12334173485613488191397209 9250630114210116143547907)
      ·
        refine ⟨13875945171315174215321861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9250630114210116143547907 13875945171315174215321861)
        ·
          refine ⟨2601739719621595165372849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13875945171315174215321861 2601739719621595165372849)
          ·
            refine ⟨1951304789716196374029637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2601739719621595165372849 1951304789716196374029637)
            ·
              refine ⟨365869648071786820130557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1951304789716196374029637 365869648071786820130557)
              ·
                refine ⟨137201118026920057548959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365869648071786820130557 137201118026920057548959)
                ·
                  rfl

theorem cell19_450897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_450897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450897 prefixEnd_450897 := by exact prefixLift 450897
  have htrace : WordTrace (prefixWord ++ tailWord_450897) baseStart_450897 baseEnd_450897 := by
    simpa [prefixWord, tailWord_450897, baseEnd_450897] using wordTrace_append hprefix tailTrace_450897
  have hstable : (prefixWord ++ tailWord_450897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450897).length < 2 ^ (prefixWord ++ tailWord_450897).sum := by decide
  have hdescent : baseEnd_450897 < baseStart_450897 := by decide
  rcases family_descends (prefixWord ++ tailWord_450897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450956 : List Nat := [2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_450956 : Nat := 118140960795 + 450956 * 2 ^ 59
def prefixEnd_450956 : Nat := 4983230072969 + 3 ^ 40 * 450956 * 2
def baseEnd_450956 : Nat := 137219070832025402237687

theorem tailTrace_450956 : CollatzResearch.WordTrace tailWord_450956 prefixEnd_450956 137219070832025402237687 := by
  unfold tailWord_450956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223858277135451999130361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10965144369513935998840481 8223858277135451999130361)
  ·
    refine ⟨6167893707851588999347771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8223858277135451999130361 6167893707851588999347771)
    ·
      refine ⟨9251840561777383499021657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6167893707851588999347771 9251840561777383499021657)
      ·
        refine ⟨6938880421333037624266243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9251840561777383499021657 6938880421333037624266243)
        ·
          refine ⟨10408320631999556436399365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6938880421333037624266243 10408320631999556436399365)
          ·
            refine ⟨1951560118499916831824881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10408320631999556436399365 1951560118499916831824881)
            ·
              refine ⟨1463670088874937623868661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951560118499916831824881 1463670088874937623868661)
              ·
                refine ⟨137219070832025402237687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1463670088874937623868661 137219070832025402237687)
                ·
                  rfl

theorem cell19_450956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_450956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450956 prefixEnd_450956 := by exact prefixLift 450956
  have htrace : WordTrace (prefixWord ++ tailWord_450956) baseStart_450956 baseEnd_450956 := by
    simpa [prefixWord, tailWord_450956, baseEnd_450956] using wordTrace_append hprefix tailTrace_450956
  have hstable : (prefixWord ++ tailWord_450956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450956).length < 2 ^ (prefixWord ++ tailWord_450956).sum := by decide
  have hdescent : baseEnd_450956 < baseStart_450956 := by decide
  rcases family_descends (prefixWord ++ tailWord_450956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450973 : List Nat := [1, 4, 2, 1, 5, 6]
def baseStart_450973 : Nat := 118140960795 + 450973 * 2 ^ 59
def prefixEnd_450973 : Nat := 4983230072969 + 3 ^ 40 * 450973 * 2
def baseEnd_450973 : Nat := 15247138186019377762207

theorem tailTrace_450973 : CollatzResearch.WordTrace tailWord_450973 prefixEnd_450973 15247138186019377762207 := by
  unfold tailWord_450973
  simp only [CollatzResearch.WordTrace]
  refine ⟨16448336595209315901629573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10965557730139543934419715 16448336595209315901629573)
  ·
    refine ⟨3084063111601746731555545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16448336595209315901629573 3084063111601746731555545)
    ·
      refine ⟨2313047333701310048666659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3084063111601746731555545 2313047333701310048666659)
      ·
        refine ⟨3469571000551965072999989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313047333701310048666659 3469571000551965072999989)
        ·
          refine ⟨325272281301746725593749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3469571000551965072999989 325272281301746725593749)
          ·
            refine ⟨15247138186019377762207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325272281301746725593749 15247138186019377762207)
            ·
              rfl

theorem cell19_450973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 6].length) (baseStart_450973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450973 prefixEnd_450973 := by exact prefixLift 450973
  have htrace : WordTrace (prefixWord ++ tailWord_450973) baseStart_450973 baseEnd_450973 := by
    simpa [prefixWord, tailWord_450973, baseEnd_450973] using wordTrace_append hprefix tailTrace_450973
  have hstable : (prefixWord ++ tailWord_450973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450973).length < 2 ^ (prefixWord ++ tailWord_450973).sum := by decide
  have hdescent : baseEnd_450973 < baseStart_450973 := by decide
  rcases family_descends (prefixWord ++ tailWord_450973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450986 : List Nat := [3, 1, 6, 1, 1, 2, 1, 4]
def baseStart_450986 : Nat := 118140960795 + 450986 * 2 ^ 59
def prefixEnd_450986 : Nat := 4983230072969 + 3 ^ 40 * 450986 * 2
def baseEnd_450986 : Nat := 137228199376994221570939

theorem tailTrace_450986 : CollatzResearch.WordTrace tailWord_450986 prefixEnd_450986 137228199376994221570939 := by
  unfold tailWord_450986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112202686040554780463203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10965873829441479414568541 4112202686040554780463203)
  ·
    refine ⟨6168304029060832170694805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4112202686040554780463203 6168304029060832170694805)
    ·
      refine ⟨289139251362226508001319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6168304029060832170694805 289139251362226508001319)
      ·
        refine ⟨433708877043339762001979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289139251362226508001319 433708877043339762001979)
        ·
          refine ⟨650563315565009643002969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433708877043339762001979 650563315565009643002969)
          ·
            refine ⟨487922486673757232252227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650563315565009643002969 487922486673757232252227)
            ·
              refine ⟨731883730010635848378341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487922486673757232252227 731883730010635848378341)
              ·
                refine ⟨137228199376994221570939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 731883730010635848378341 137228199376994221570939)
                ·
                  rfl

theorem cell19_450986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_450986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_450986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_450986 prefixEnd_450986 := by exact prefixLift 450986
  have htrace : WordTrace (prefixWord ++ tailWord_450986) baseStart_450986 baseEnd_450986 := by
    simpa [prefixWord, tailWord_450986, baseEnd_450986] using wordTrace_append hprefix tailTrace_450986
  have hstable : (prefixWord ++ tailWord_450986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450986).length < 2 ^ (prefixWord ++ tailWord_450986).sum := by decide
  have hdescent : baseEnd_450986 < baseStart_450986 := by decide
  rcases family_descends (prefixWord ++ tailWord_450986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451030 : List Nat := [5, 2, 1, 1, 1, 1, 8]
def baseStart_451030 : Nat := 118140960795 + 451030 * 2 ^ 59
def prefixEnd_451030 : Nat := 4983230072969 + 3 ^ 40 * 451030 * 2
def baseEnd_451030 : Nat := 45747195969871718864347

theorem tailTrace_451030 : CollatzResearch.WordTrace tailWord_451030 prefixEnd_451030 45747195969871718864347 := by
  unfold tailWord_451030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028150972250175914778409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10966943704001876424303029 1028150972250175914778409)
  ·
    refine ⟨771113229187631936083807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1028150972250175914778409 771113229187631936083807)
    ·
      refine ⟨1156669843781447904125711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771113229187631936083807 1156669843781447904125711)
      ·
        refine ⟨1735004765672171856188567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156669843781447904125711 1735004765672171856188567)
        ·
          refine ⟨2602507148508257784282851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735004765672171856188567 2602507148508257784282851)
          ·
            refine ⟨3903760722762386676424277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602507148508257784282851 3903760722762386676424277)
            ·
              refine ⟨45747195969871718864347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3903760722762386676424277 45747195969871718864347)
              ·
                rfl

theorem cell19_451030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_451030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451030 prefixEnd_451030 := by exact prefixLift 451030
  have htrace : WordTrace (prefixWord ++ tailWord_451030) baseStart_451030 baseEnd_451030 := by
    simpa [prefixWord, tailWord_451030, baseEnd_451030] using wordTrace_append hprefix tailTrace_451030
  have hstable : (prefixWord ++ tailWord_451030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451030).length < 2 ^ (prefixWord ++ tailWord_451030).sum := by decide
  have hdescent : baseEnd_451030 < baseStart_451030 := by decide
  rcases family_descends (prefixWord ++ tailWord_451030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451085 : List Nat := [1, 7, 1, 1, 1, 1, 7]
def baseStart_451085 : Nat := 118140960795 + 451085 * 2 ^ 59
def prefixEnd_451085 : Nat := 4983230072969 + 3 ^ 40 * 451085 * 2
def baseEnd_451085 : Nat := 45752774525130441790223

theorem tailTrace_451085 : CollatzResearch.WordTrace tailWord_451085 prefixEnd_451085 45752774525130441790223 := by
  unfold tailWord_451085
  simp only [CollatzResearch.WordTrace]
  refine ⟨16452421570803559029706709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10968281047202372686471139 16452421570803559029706709)
  ·
    refine ⟨385603630565708414758751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16452421570803559029706709 385603630565708414758751)
    ·
      refine ⟨578405445848562622138127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385603630565708414758751 578405445848562622138127)
      ·
        refine ⟨867608168772843933207191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578405445848562622138127 867608168772843933207191)
        ·
          refine ⟨1301412253159265899810787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867608168772843933207191 1301412253159265899810787)
          ·
            refine ⟨1952118379738898849716181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301412253159265899810787 1952118379738898849716181)
            ·
              refine ⟨45752774525130441790223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1952118379738898849716181 45752774525130441790223)
              ·
                rfl

theorem cell19_451085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_451085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451085 prefixEnd_451085 := by exact prefixLift 451085
  have htrace : WordTrace (prefixWord ++ tailWord_451085) baseStart_451085 baseEnd_451085 := by
    simpa [prefixWord, tailWord_451085, baseEnd_451085] using wordTrace_append hprefix tailTrace_451085
  have hstable : (prefixWord ++ tailWord_451085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451085).length < 2 ^ (prefixWord ++ tailWord_451085).sum := by decide
  have hdescent : baseEnd_451085 < baseStart_451085 := by decide
  rcases family_descends (prefixWord ++ tailWord_451085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451140 : List Nat := [2, 3, 5, 1, 2, 6]
def baseStart_451140 : Nat := 118140960795 + 451140 * 2 ^ 59
def prefixEnd_451140 : Nat := 4983230072969 + 3 ^ 40 * 451140 * 2
def baseEnd_451140 : Nat := 15252784360129721572033

theorem tailTrace_451140 : CollatzResearch.WordTrace tailWord_451140 prefixEnd_451140 15252784360129721572033 := by
  unfold tailWord_451140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8227213792802151711479437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10969618390402868948639249 8227213792802151711479437)
  ·
    refine ⟨3085205172300806891804789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8227213792802151711479437 3085205172300806891804789)
    ·
      refine ⟨289237984903200646106699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3085205172300806891804789 289237984903200646106699)
      ·
        refine ⟨433856977354800969160049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289237984903200646106699 433856977354800969160049)
        ·
          refine ⟨325392733016100726870037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433856977354800969160049 325392733016100726870037)
          ·
            refine ⟨15252784360129721572033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325392733016100726870037 15252784360129721572033)
            ·
              rfl

theorem cell19_451140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 6].length) (baseStart_451140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451140 prefixEnd_451140 := by exact prefixLift 451140
  have htrace : WordTrace (prefixWord ++ tailWord_451140) baseStart_451140 baseEnd_451140 := by
    simpa [prefixWord, tailWord_451140, baseEnd_451140] using wordTrace_append hprefix tailTrace_451140
  have hstable : (prefixWord ++ tailWord_451140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451140).length < 2 ^ (prefixWord ++ tailWord_451140).sum := by decide
  have hdescent : baseEnd_451140 < baseStart_451140 := by decide
  rcases family_descends (prefixWord ++ tailWord_451140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451254 : List Nat := [5, 1, 3, 1, 3, 1, 5]
def baseStart_451254 : Nat := 118140960795 + 451254 * 2 ^ 59
def prefixEnd_451254 : Nat := 4983230072969 + 3 ^ 40 * 451254 * 2
def baseEnd_451254 : Nat := 45769915904016335871551

theorem tailTrace_451254 : CollatzResearch.WordTrace tailWord_451254 prefixEnd_451254 45769915904016335871551 := by
  unfold tailWord_451254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028661594199456305788051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10972390338127533928405877 1028661594199456305788051)
  ·
    refine ⟨1542992391299184458682077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1028661594199456305788051 1542992391299184458682077)
    ·
      refine ⟨578622146737194172005779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1542992391299184458682077 578622146737194172005779)
      ·
        refine ⟨867933220105791258008669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578622146737194172005779 867933220105791258008669)
        ·
          refine ⟨325474957539671721753251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 867933220105791258008669 325474957539671721753251)
          ·
            refine ⟨488212436309507582629877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325474957539671721753251 488212436309507582629877)
            ·
              refine ⟨45769915904016335871551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 488212436309507582629877 45769915904016335871551)
              ·
                rfl

theorem cell19_451254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 5].length) (baseStart_451254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451254 prefixEnd_451254 := by exact prefixLift 451254
  have htrace : WordTrace (prefixWord ++ tailWord_451254) baseStart_451254 baseEnd_451254 := by
    simpa [prefixWord, tailWord_451254, baseEnd_451254] using wordTrace_append hprefix tailTrace_451254
  have hstable : (prefixWord ++ tailWord_451254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451254).length < 2 ^ (prefixWord ++ tailWord_451254).sum := by decide
  have hdescent : baseEnd_451254 < baseStart_451254 := by decide
  rcases family_descends (prefixWord ++ tailWord_451254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451336 : List Nat := [2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_451336 : Nat := 118140960795 + 451336 * 2 ^ 59
def prefixEnd_451336 : Nat := 4983230072969 + 3 ^ 40 * 451336 * 2
def baseEnd_451336 : Nat := 137334699068297113792207

theorem tailTrace_451336 : CollatzResearch.WordTrace tailWord_451336 prefixEnd_451336 137334699068297113792207 := by
  unfold tailWord_451336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8230788146447114448546931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10974384195262819264729241 8230788146447114448546931)
  ·
    refine ⟨12346182219670671672820397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8230788146447114448546931 12346182219670671672820397)
    ·
      refine ⟨4629818332376501877307649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12346182219670671672820397 4629818332376501877307649)
      ·
        refine ⟨3472363749282376407980737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4629818332376501877307649 3472363749282376407980737)
        ·
          refine ⟨2604272811961782305985553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472363749282376407980737 2604272811961782305985553)
          ·
            refine ⟨1953204608971336729489165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2604272811961782305985553 1953204608971336729489165)
            ·
              refine ⟨732451728364251273558437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1953204608971336729489165 732451728364251273558437)
              ·
                refine ⟨137334699068297113792207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732451728364251273558437 137334699068297113792207)
                ·
                  rfl

theorem cell19_451336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_451336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451336 prefixEnd_451336 := by exact prefixLift 451336
  have htrace : WordTrace (prefixWord ++ tailWord_451336) baseStart_451336 baseEnd_451336 := by
    simpa [prefixWord, tailWord_451336, baseEnd_451336] using wordTrace_append hprefix tailTrace_451336
  have hstable : (prefixWord ++ tailWord_451336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451336).length < 2 ^ (prefixWord ++ tailWord_451336).sum := by decide
  have hdescent : baseEnd_451336 < baseStart_451336 := by decide
  rcases family_descends (prefixWord ++ tailWord_451336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451395 : List Nat := [1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_451395 : Nat := 118140960795 + 451395 * 2 ^ 59
def prefixEnd_451395 : Nat := 4983230072969 + 3 ^ 40 * 451395 * 2
def baseEnd_451395 : Nat := 137352651873402458480935

theorem tailTrace_451395 : CollatzResearch.WordTrace tailWord_451395 prefixEnd_451395 137352651873402458480935 := by
  unfold tailWord_451395
  simp only [CollatzResearch.WordTrace]
  refine ⟨16463728199680481973491639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10975818799786987982327759 16463728199680481973491639)
  ·
    refine ⟨24695592299520722960237459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16463728199680481973491639 24695592299520722960237459)
    ·
      refine ⟨37043388449281084440356189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24695592299520722960237459 37043388449281084440356189)
      ·
        refine ⟨13891270668480406665133571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37043388449281084440356189 13891270668480406665133571)
        ·
          refine ⟨20836906002720609997700357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13891270668480406665133571 20836906002720609997700357)
          ·
            refine ⟨3906919875510114374568817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20836906002720609997700357 3906919875510114374568817)
            ·
              refine ⟨2930189906632585780926613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3906919875510114374568817 2930189906632585780926613)
              ·
                refine ⟨137352651873402458480935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2930189906632585780926613 137352651873402458480935)
                ·
                  rfl

theorem cell19_451395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_451395 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451395 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451395 prefixEnd_451395 := by exact prefixLift 451395
  have htrace : WordTrace (prefixWord ++ tailWord_451395) baseStart_451395 baseEnd_451395 := by
    simpa [prefixWord, tailWord_451395, baseEnd_451395] using wordTrace_append hprefix tailTrace_451395
  have hstable : (prefixWord ++ tailWord_451395).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451395).length < 2 ^ (prefixWord ++ tailWord_451395).sum := by decide
  have hdescent : baseEnd_451395 < baseStart_451395 := by decide
  rcases family_descends (prefixWord ++ tailWord_451395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451431 : List Nat := [1, 1, 5, 1, 2, 4, 5]
def baseStart_451431 : Nat := 118140960795 + 451431 * 2 ^ 59
def prefixEnd_451431 : Nat := 4983230072969 + 3 ^ 40 * 451431 * 2
def baseEnd_451431 : Nat := 45787868709121680560279

theorem tailTrace_451431 : CollatzResearch.WordTrace tailWord_451431 prefixEnd_451431 45787868709121680560279 := by
  unfold tailWord_451431
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465041227550060121802147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10976694151700040081201431 16465041227550060121802147)
  ·
    refine ⟨24697561841325090182703221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16465041227550060121802147 24697561841325090182703221)
    ·
      refine ⟨2315396422624227204628427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24697561841325090182703221 2315396422624227204628427)
      ·
        refine ⟨3473094633936340806942641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2315396422624227204628427 3473094633936340806942641)
        ·
          refine ⟨2604820975452255605206981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3473094633936340806942641 2604820975452255605206981)
          ·
            refine ⟨488403932897297925976309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2604820975452255605206981 488403932897297925976309)
            ·
              refine ⟨45787868709121680560279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 488403932897297925976309 45787868709121680560279)
              ·
                rfl

theorem cell19_451431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_451431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451431 prefixEnd_451431 := by exact prefixLift 451431
  have htrace : WordTrace (prefixWord ++ tailWord_451431) baseStart_451431 baseEnd_451431 := by
    simpa [prefixWord, tailWord_451431, baseEnd_451431] using wordTrace_append hprefix tailTrace_451431
  have hstable : (prefixWord ++ tailWord_451431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451431).length < 2 ^ (prefixWord ++ tailWord_451431).sum := by decide
  have hdescent : baseEnd_451431 < baseStart_451431 := by decide
  rcases family_descends (prefixWord ++ tailWord_451431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451501 : List Nat := [1, 5, 2, 3, 2, 1, 1, 4]
def baseStart_451501 : Nat := 118140960795 + 451501 * 2 ^ 59
def prefixEnd_451501 : Nat := 4983230072969 + 3 ^ 40 * 451501 * 2
def baseEnd_451501 : Nat := 137384906065625620125091

theorem tailTrace_451501 : CollatzResearch.WordTrace tailWord_451501 prefixEnd_451501 137384906065625620125091 := by
  unfold tailWord_451501
  simp only [CollatzResearch.WordTrace]
  refine ⟨16467594337296462076850357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10978396224864308051233571 16467594337296462076850357)
  ·
    refine ⟨1543836969121543319704721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16467594337296462076850357 1543836969121543319704721)
    ·
      refine ⟨1157877726841157489778541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1543836969121543319704721 1157877726841157489778541)
      ·
        refine ⟨434204147565434058666953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1157877726841157489778541 434204147565434058666953)
        ·
          refine ⟨325653110674075544000215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434204147565434058666953 325653110674075544000215)
          ·
            refine ⟨488479666011113316000323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325653110674075544000215 488479666011113316000323)
            ·
              refine ⟨732719499016669974000485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488479666011113316000323 732719499016669974000485)
              ·
                refine ⟨137384906065625620125091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732719499016669974000485 137384906065625620125091)
                ·
                  rfl

theorem cell19_451501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 4].length) (baseStart_451501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451501 prefixEnd_451501 := by exact prefixLift 451501
  have htrace : WordTrace (prefixWord ++ tailWord_451501) baseStart_451501 baseEnd_451501 := by
    simpa [prefixWord, tailWord_451501, baseEnd_451501] using wordTrace_append hprefix tailTrace_451501
  have hstable : (prefixWord ++ tailWord_451501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451501).length < 2 ^ (prefixWord ++ tailWord_451501).sum := by decide
  have hdescent : baseEnd_451501 < baseStart_451501 := by decide
  rcases family_descends (prefixWord ++ tailWord_451501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
