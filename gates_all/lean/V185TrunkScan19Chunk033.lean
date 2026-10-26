import V185TrunkScan19Chunk032

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_331248 : List Nat := [2, 1, 1, 1, 3, 4, 7]
def baseStart_331248 : Nat := 118140960795 + 331248 * 2 ^ 59
def prefixEnd_331248 : Nat := 4983230072969 + 3 ^ 40 * 331248 * 2
def baseEnd_331248 : Nat := 33597914042592636913901

theorem tailTrace_331248 : CollatzResearch.WordTrace tailWord_331248 prefixEnd_331248 33597914042592636913901 := by
  unfold tailWord_331248
  simp only [CollatzResearch.WordTrace]
  refine ⟨6040803551976271749765199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8054404735968362333020265 6040803551976271749765199)
  ·
    refine ⟨9061205327964407624647799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6040803551976271749765199 9061205327964407624647799)
    ·
      refine ⟨13591807991946611436971699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9061205327964407624647799 13591807991946611436971699)
      ·
        refine ⟨20387711987919917155457549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13591807991946611436971699 20387711987919917155457549)
        ·
          refine ⟨7645391995469968933296581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20387711987919917155457549 7645391995469968933296581)
          ·
            refine ⟨1433510999150619174993109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7645391995469968933296581 1433510999150619174993109)
            ·
              refine ⟨33597914042592636913901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1433510999150619174993109 33597914042592636913901)
              ·
                rfl

theorem cell19_331248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_331248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331248 prefixEnd_331248 := by exact prefixLift 331248
  have htrace : WordTrace (prefixWord ++ tailWord_331248) baseStart_331248 baseEnd_331248 := by
    simpa [prefixWord, tailWord_331248, baseEnd_331248] using wordTrace_append hprefix tailTrace_331248
  have hstable : (prefixWord ++ tailWord_331248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331248).length < 2 ^ (prefixWord ++ tailWord_331248).sum := by decide
  have hdescent : baseEnd_331248 < baseStart_331248 := by decide
  rcases family_descends (prefixWord ++ tailWord_331248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331318 : List Nat := [5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_331318 : Nat := 118140960795 + 331318 * 2 ^ 59
def prefixEnd_331318 : Nat := 4983230072969 + 3 ^ 40 * 331318 * 2
def baseEnd_331318 : Nat := 100815042066038489185957

theorem tailTrace_331318 : CollatzResearch.WordTrace tailWord_331318 prefixEnd_331318 100815042066038489185957 := by
  unfold tailWord_331318
  simp only [CollatzResearch.WordTrace]
  refine ⟨755260013356184090911163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8056106809132630303052405 755260013356184090911163)
  ·
    refine ⟨1132890020034276136366745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 755260013356184090911163 1132890020034276136366745)
    ·
      refine ⟨849667515025707102275059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1132890020034276136366745 849667515025707102275059)
      ·
        refine ⟨1274501272538560653412589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849667515025707102275059 1274501272538560653412589)
        ·
          refine ⟨477937977201960245029721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1274501272538560653412589 477937977201960245029721)
          ·
            refine ⟨358453482901470183772291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477937977201960245029721 358453482901470183772291)
            ·
              refine ⟨537680224352205275658437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358453482901470183772291 537680224352205275658437)
              ·
                refine ⟨100815042066038489185957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537680224352205275658437 100815042066038489185957)
                ·
                  rfl

theorem cell19_331318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_331318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331318 prefixEnd_331318 := by exact prefixLift 331318
  have htrace : WordTrace (prefixWord ++ tailWord_331318) baseStart_331318 baseEnd_331318 := by
    simpa [prefixWord, tailWord_331318, baseEnd_331318] using wordTrace_append hprefix tailTrace_331318
  have hstable : (prefixWord ++ tailWord_331318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331318).length < 2 ^ (prefixWord ++ tailWord_331318).sum := by decide
  have hdescent : baseEnd_331318 < baseStart_331318 := by decide
  rcases family_descends (prefixWord ++ tailWord_331318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331491 : List Nat := [1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_331491 : Nat := 118140960795 + 331491 * 2 ^ 59
def prefixEnd_331491 : Nat := 4983230072969 + 3 ^ 40 * 331491 * 2
def baseEnd_331491 : Nat := 100867683342025347341041

theorem tailTrace_331491 : CollatzResearch.WordTrace tailWord_331491 prefixEnd_331491 100867683342025347341041 := by
  unfold tailWord_331491
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090470042072196000626327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8060313361381464000417551 12090470042072196000626327)
  ·
    refine ⟨18135705063108294000939491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12090470042072196000626327 18135705063108294000939491)
    ·
      refine ⟨27203557594662441001409237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18135705063108294000939491 27203557594662441001409237)
      ·
        refine ⟨637583381124900960970529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 27203557594662441001409237 637583381124900960970529)
        ·
          refine ⟨478187535843675720727897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637583381124900960970529 478187535843675720727897)
          ·
            refine ⟨358640651882756790545923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478187535843675720727897 358640651882756790545923)
            ·
              refine ⟨537960977824135185818885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358640651882756790545923 537960977824135185818885)
              ·
                refine ⟨100867683342025347341041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 537960977824135185818885 100867683342025347341041)
                ·
                  rfl

theorem cell19_331491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_331491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331491 prefixEnd_331491 := by exact prefixLift 331491
  have htrace : WordTrace (prefixWord ++ tailWord_331491) baseStart_331491 baseEnd_331491 := by
    simpa [prefixWord, tailWord_331491, baseEnd_331491] using wordTrace_append hprefix tailTrace_331491
  have hstable : (prefixWord ++ tailWord_331491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331491).length < 2 ^ (prefixWord ++ tailWord_331491).sum := by decide
  have hdescent : baseEnd_331491 < baseStart_331491 := by decide
  rcases family_descends (prefixWord ++ tailWord_331491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331510 : List Nat := [5, 1, 1, 1, 1, 4, 3, 3]
def baseStart_331510 : Nat := 118140960795 + 331510 * 2 ^ 59
def prefixEnd_331510 : Nat := 4983230072969 + 3 ^ 40 * 331510 * 2
def baseEnd_331510 : Nat := 100873464753838932918767

theorem tailTrace_331510 : CollatzResearch.WordTrace tailWord_331510 prefixEnd_331510 100873464753838932918767 := by
  unfold tailWord_331510
  simp only [CollatzResearch.WordTrace]
  refine ⟨755697689312710140347999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8060775352668908163711989 755697689312710140347999)
  ·
    refine ⟨1133546533969065210521999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 755697689312710140347999 1133546533969065210521999)
    ·
      refine ⟨1700319800953597815782999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1133546533969065210521999 1700319800953597815782999)
      ·
        refine ⟨2550479701430396723674499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700319800953597815782999 2550479701430396723674499)
        ·
          refine ⟨3825719552145595085511749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550479701430396723674499 3825719552145595085511749)
          ·
            refine ⟨717322416027299078533453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3825719552145595085511749 717322416027299078533453)
            ·
              refine ⟨268995906010237154450045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 717322416027299078533453 268995906010237154450045)
              ·
                refine ⟨100873464753838932918767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268995906010237154450045 100873464753838932918767)
                ·
                  rfl

theorem cell19_331510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_331510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331510 prefixEnd_331510 := by exact prefixLift 331510
  have htrace : WordTrace (prefixWord ++ tailWord_331510) baseStart_331510 baseEnd_331510 := by
    simpa [prefixWord, tailWord_331510, baseEnd_331510] using wordTrace_append hprefix tailTrace_331510
  have hstable : (prefixWord ++ tailWord_331510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331510).length < 2 ^ (prefixWord ++ tailWord_331510).sum := by decide
  have hdescent : baseEnd_331510 < baseStart_331510 := by decide
  rcases family_descends (prefixWord ++ tailWord_331510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331552 : List Nat := [2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_331552 : Nat := 118140960795 + 331552 * 2 ^ 59
def prefixEnd_331552 : Nat := 4983230072969 + 3 ^ 40 * 331552 * 2
def baseEnd_331552 : Nat := 100886244716795279985319

theorem tailTrace_331552 : CollatzResearch.WordTrace tailWord_331552 prefixEnd_331552 100886244716795279985319 := by
  unfold tailWord_331552
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046347447425601709298455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8061796596567468945731273 6046347447425601709298455)
  ·
    refine ⟨9069521171138402563947683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6046347447425601709298455 9069521171138402563947683)
    ·
      refine ⟨13604281756707603845921525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9069521171138402563947683 13604281756707603845921525)
      ·
        refine ⟨1275401414691337860555143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13604281756707603845921525 1275401414691337860555143)
        ·
          refine ⟨1913102122037006790832715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275401414691337860555143 1913102122037006790832715)
          ·
            refine ⟨2869653183055510186249073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913102122037006790832715 2869653183055510186249073)
            ·
              refine ⟨2152239887291632639686805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2869653183055510186249073 2152239887291632639686805)
              ·
                refine ⟨100886244716795279985319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2152239887291632639686805 100886244716795279985319)
                ·
                  rfl

theorem cell19_331552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_331552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331552 prefixEnd_331552 := by exact prefixLift 331552
  have htrace : WordTrace (prefixWord ++ tailWord_331552) baseStart_331552 baseEnd_331552 := by
    simpa [prefixWord, tailWord_331552, baseEnd_331552] using wordTrace_append hprefix tailTrace_331552
  have hstable : (prefixWord ++ tailWord_331552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331552).length < 2 ^ (prefixWord ++ tailWord_331552).sum := by decide
  have hdescent : baseEnd_331552 < baseStart_331552 := by decide
  rcases family_descends (prefixWord ++ tailWord_331552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331569 : List Nat := [1, 2, 2, 3, 2, 2, 4, 3]
def baseStart_331569 : Nat := 118140960795 + 331569 * 2 ^ 59
def prefixEnd_331569 : Nat := 4983230072969 + 3 ^ 40 * 331569 * 2
def baseEnd_331569 : Nat := 100891417558944277607495

theorem tailTrace_331569 : CollatzResearch.WordTrace tailWord_331569 prefixEnd_331569 100891417558944277607495 := by
  unfold tailWord_331569
  simp only [CollatzResearch.WordTrace]
  refine ⟨12093314935789615321965761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8062209957193076881310507 12093314935789615321965761)
  ·
    refine ⟨9069986201842211491474321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12093314935789615321965761 9069986201842211491474321)
    ·
      refine ⟨6802489651381658618605741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9069986201842211491474321 6802489651381658618605741)
      ·
        refine ⟨2550933619268121981977153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6802489651381658618605741 2550933619268121981977153)
        ·
          refine ⟨1913200214451091486482865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2550933619268121981977153 1913200214451091486482865)
          ·
            refine ⟨1434900160838318614862149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1913200214451091486482865 1434900160838318614862149)
            ·
              refine ⟨269043780157184740286653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1434900160838318614862149 269043780157184740286653)
              ·
                refine ⟨100891417558944277607495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269043780157184740286653 100891417558944277607495)
                ·
                  rfl

theorem cell19_331569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_331569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331569 prefixEnd_331569 := by exact prefixLift 331569
  have htrace : WordTrace (prefixWord ++ tailWord_331569) baseStart_331569 baseEnd_331569 := by
    simpa [prefixWord, tailWord_331569, baseEnd_331569] using wordTrace_append hprefix tailTrace_331569
  have hstable : (prefixWord ++ tailWord_331569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331569).length < 2 ^ (prefixWord ++ tailWord_331569).sum := by decide
  have hdescent : baseEnd_331569 < baseStart_331569 := by decide
  rcases family_descends (prefixWord ++ tailWord_331569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331607 : List Nat := [1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_331607 : Nat := 118140960795 + 331607 * 2 ^ 59
def prefixEnd_331607 : Nat := 4983230072969 + 3 ^ 40 * 331607 * 2
def baseEnd_331607 : Nat := 100902980382571448762947

theorem tailTrace_331607 : CollatzResearch.WordTrace tailWord_331607 prefixEnd_331607 100902980382571448762947 := by
  unfold tailWord_331607
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094700909651947811849075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8063133939767965207899383 12094700909651947811849075)
  ·
    refine ⟨18142051364477921717773613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12094700909651947811849075 18142051364477921717773613)
    ·
      refine ⟨6803269261679220644165105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18142051364477921717773613 6803269261679220644165105)
      ·
        refine ⟨5102451946259415483123829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6803269261679220644165105 5102451946259415483123829)
        ·
          refine ⟨478354869961820201542859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5102451946259415483123829 478354869961820201542859)
          ·
            refine ⟨717532304942730302314289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478354869961820201542859 717532304942730302314289)
            ·
              refine ⟨538149228707047726735717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717532304942730302314289 538149228707047726735717)
              ·
                refine ⟨100902980382571448762947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538149228707047726735717 100902980382571448762947)
                ·
                  rfl

theorem cell19_331607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_331607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331607 prefixEnd_331607 := by exact prefixLift 331607
  have htrace : WordTrace (prefixWord ++ tailWord_331607) baseStart_331607 baseEnd_331607 := by
    simpa [prefixWord, tailWord_331607, baseEnd_331607] using wordTrace_append hprefix tailTrace_331607
  have hstable : (prefixWord ++ tailWord_331607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331607).length < 2 ^ (prefixWord ++ tailWord_331607).sum := by decide
  have hdescent : baseEnd_331607 < baseStart_331607 := by decide
  rcases family_descends (prefixWord ++ tailWord_331607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331609 : List Nat := [1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_331609 : Nat := 118140960795 + 331609 * 2 ^ 59
def prefixEnd_331609 : Nat := 4983230072969 + 3 ^ 40 * 331609 * 2
def baseEnd_331609 : Nat := 100903588952236036718497

theorem tailTrace_331609 : CollatzResearch.WordTrace tailWord_331609 prefixEnd_331609 100903588952236036718497 := by
  unfold tailWord_331609
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094773855644702153421881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8063182570429801435614587 12094773855644702153421881)
  ·
    refine ⟨9071080391733526615066411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12094773855644702153421881 9071080391733526615066411)
    ·
      refine ⟨13606620587600289922599617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9071080391733526615066411 13606620587600289922599617)
      ·
        refine ⟨10204965440700217441949713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13606620587600289922599617 10204965440700217441949713)
        ·
          refine ⟨7653724080525163081462285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10204965440700217441949713 7653724080525163081462285)
          ·
            refine ⟨2870146530196936155548357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7653724080525163081462285 2870146530196936155548357)
            ·
              refine ⟨538152474411925529165317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2870146530196936155548357 538152474411925529165317)
              ·
                refine ⟨100903588952236036718497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538152474411925529165317 100903588952236036718497)
                ·
                  rfl

theorem cell19_331609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_331609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331609 prefixEnd_331609 := by exact prefixLift 331609
  have htrace : WordTrace (prefixWord ++ tailWord_331609) baseStart_331609 baseEnd_331609 := by
    simpa [prefixWord, tailWord_331609, baseEnd_331609] using wordTrace_append hprefix tailTrace_331609
  have hstable : (prefixWord ++ tailWord_331609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331609).length < 2 ^ (prefixWord ++ tailWord_331609).sum := by decide
  have hdescent : baseEnd_331609 < baseStart_331609 := by decide
  rcases family_descends (prefixWord ++ tailWord_331609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331628 : List Nat := [2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_331628 : Nat := 118140960795 + 331628 * 2 ^ 59
def prefixEnd_331628 : Nat := 4983230072969 + 3 ^ 40 * 331628 * 2
def baseEnd_331628 : Nat := 100909370364049622296223

theorem tailTrace_331628 : CollatzResearch.WordTrace tailWord_331628 prefixEnd_331628 100909370364049622296223 := by
  unfold tailWord_331628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047733421287934199181769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8063644561717245598909025 6047733421287934199181769)
  ·
    refine ⟨4535800065965950649386327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6047733421287934199181769 4535800065965950649386327)
    ·
      refine ⟨6803700098948925974079491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4535800065965950649386327 6803700098948925974079491)
      ·
        refine ⟨10205550148423388961119237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6803700098948925974079491 10205550148423388961119237)
        ·
          refine ⟨1913540652829385430209857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10205550148423388961119237 1913540652829385430209857)
          ·
            refine ⟨1435155489622039072657393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1913540652829385430209857 1435155489622039072657393)
            ·
              refine ⟨1076366617216529304493045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435155489622039072657393 1076366617216529304493045)
              ·
                refine ⟨100909370364049622296223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1076366617216529304493045 100909370364049622296223)
                ·
                  rfl

theorem cell19_331628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_331628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331628 prefixEnd_331628 := by exact prefixLift 331628
  have htrace : WordTrace (prefixWord ++ tailWord_331628) baseStart_331628 baseEnd_331628 := by
    simpa [prefixWord, tailWord_331628, baseEnd_331628] using wordTrace_append hprefix tailTrace_331628
  have hstable : (prefixWord ++ tailWord_331628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331628).length < 2 ^ (prefixWord ++ tailWord_331628).sum := by decide
  have hdescent : baseEnd_331628 < baseStart_331628 := by decide
  rcases family_descends (prefixWord ++ tailWord_331628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331681 : List Nat := [1, 2, 3, 4, 2, 1, 3, 3]
def baseStart_331681 : Nat := 118140960795 + 331681 * 2 ^ 59
def prefixEnd_331681 : Nat := 4983230072969 + 3 ^ 40 * 331681 * 2
def baseEnd_331681 : Nat := 100925497460161203118301

theorem tailTrace_331681 : CollatzResearch.WordTrace tailWord_331681 prefixEnd_331681 100925497460161203118301 := by
  unfold tailWord_331681
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097399911383858450042897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8064933274255905633361931 12097399911383858450042897)
  ·
    refine ⟨9073049933537893837532173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12097399911383858450042897 9073049933537893837532173)
    ·
      refine ⟨3402393725076710189074565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9073049933537893837532173 3402393725076710189074565)
      ·
        refine ⟨637948823451883160451481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3402393725076710189074565 637948823451883160451481)
        ·
          refine ⟨478461617588912370338611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637948823451883160451481 478461617588912370338611)
          ·
            refine ⟨717692426383368555507917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478461617588912370338611 717692426383368555507917)
            ·
              refine ⟨269134659893763208315469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 717692426383368555507917 269134659893763208315469)
              ·
                refine ⟨100925497460161203118301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269134659893763208315469 100925497460161203118301)
                ·
                  rfl

theorem cell19_331681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_331681 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331681 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331681 prefixEnd_331681 := by exact prefixLift 331681
  have htrace : WordTrace (prefixWord ++ tailWord_331681) baseStart_331681 baseEnd_331681 := by
    simpa [prefixWord, tailWord_331681, baseEnd_331681] using wordTrace_append hprefix tailTrace_331681
  have hstable : (prefixWord ++ tailWord_331681).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331681).length < 2 ^ (prefixWord ++ tailWord_331681).sum := by decide
  have hdescent : baseEnd_331681 < baseStart_331681 := by decide
  rcases family_descends (prefixWord ++ tailWord_331681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331700 : List Nat := [2, 5, 2, 1, 2, 1, 6]
def baseStart_331700 : Nat := 118140960795 + 331700 * 2 ^ 59
def prefixEnd_331700 : Nat := 4983230072969 + 3 ^ 40 * 331700 * 2
def baseEnd_331700 : Nat := 33643759623991596232009

theorem tailTrace_331700 : CollatzResearch.WordTrace tailWord_331700 prefixEnd_331700 33643759623991596232009 := by
  unfold tailWord_331700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049046449157512347492277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8065395265543349796656369 6049046449157512347492277)
  ·
    refine ⟨567098104608516782577401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6049046449157512347492277 567098104608516782577401)
    ·
      refine ⟨425323578456387586933051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 567098104608516782577401 425323578456387586933051)
      ·
        refine ⟨637985367684581380399577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425323578456387586933051 637985367684581380399577)
        ·
          refine ⟨478489025763436035299683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637985367684581380399577 478489025763436035299683)
          ·
            refine ⟨717733538645154052949525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478489025763436035299683 717733538645154052949525)
            ·
              refine ⟨33643759623991596232009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 717733538645154052949525 33643759623991596232009)
              ·
                rfl

theorem cell19_331700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_331700 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331700 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331700 prefixEnd_331700 := by exact prefixLift 331700
  have htrace : WordTrace (prefixWord ++ tailWord_331700) baseStart_331700 baseEnd_331700 := by
    simpa [prefixWord, tailWord_331700, baseEnd_331700] using wordTrace_append hprefix tailTrace_331700
  have hstable : (prefixWord ++ tailWord_331700).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331700).length < 2 ^ (prefixWord ++ tailWord_331700).sum := by decide
  have hdescent : baseEnd_331700 < baseStart_331700 := by decide
  rcases family_descends (prefixWord ++ tailWord_331700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331734 : List Nat := [5, 2, 1, 1, 4, 1, 2, 3]
def baseStart_331734 : Nat := 118140960795 + 331734 * 2 ^ 59
def prefixEnd_331734 : Nat := 4983230072969 + 3 ^ 40 * 331734 * 2
def baseEnd_331734 : Nat := 100941624556272783940379

theorem tailTrace_331734 : CollatzResearch.WordTrace tailWord_331734 prefixEnd_331734 100941624556272783940379 := by
  unfold tailWord_331734
  simp only [CollatzResearch.WordTrace]
  refine ⟨756208311261990531357641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8066221986794565667814837 756208311261990531357641)
  ·
    refine ⟨567156233446492898518231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 756208311261990531357641 567156233446492898518231)
    ·
      refine ⟨850734350169739347777347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567156233446492898518231 850734350169739347777347)
      ·
        refine ⟨1276101525254609021666021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850734350169739347777347 1276101525254609021666021)
        ·
          refine ⟨239269035985239191562379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1276101525254609021666021 239269035985239191562379)
          ·
            refine ⟨358903553977858787343569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239269035985239191562379 358903553977858787343569)
            ·
              refine ⟨269177665483394090507677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358903553977858787343569 269177665483394090507677)
              ·
                refine ⟨100941624556272783940379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269177665483394090507677 100941624556272783940379)
                ·
                  rfl

theorem cell19_331734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_331734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331734 prefixEnd_331734 := by exact prefixLift 331734
  have htrace : WordTrace (prefixWord ++ tailWord_331734) baseStart_331734 baseEnd_331734 := by
    simpa [prefixWord, tailWord_331734, baseEnd_331734] using wordTrace_append hprefix tailTrace_331734
  have hstable : (prefixWord ++ tailWord_331734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331734).length < 2 ^ (prefixWord ++ tailWord_331734).sum := by decide
  have hdescent : baseEnd_331734 < baseStart_331734 := by decide
  rcases family_descends (prefixWord ++ tailWord_331734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331738 : List Nat := [3, 1, 1, 2, 5, 2, 2, 3]
def baseStart_331738 : Nat := 118140960795 + 331738 * 2 ^ 59
def prefixEnd_331738 : Nat := 4983230072969 + 3 ^ 40 * 331738 * 2
def baseEnd_331738 : Nat := 100942841695601959851479

theorem tailTrace_331738 : CollatzResearch.WordTrace tailWord_331738 prefixEnd_331738 100942841695601959851479 := by
  unfold tailWord_331738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3024869718044339296216967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8066319248118238123245245 3024869718044339296216967)
  ·
    refine ⟨4537304577066508944325451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3024869718044339296216967 4537304577066508944325451)
    ·
      refine ⟨6805956865599763416488177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4537304577066508944325451 6805956865599763416488177)
      ·
        refine ⟨5104467649199822562366133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6805956865599763416488177 5104467649199822562366133)
        ·
          refine ⟨478543842112483365221825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5104467649199822562366133 478543842112483365221825)
          ·
            refine ⟨358907881584362523916369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478543842112483365221825 358907881584362523916369)
            ·
              refine ⟨269180911188271892937277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358907881584362523916369 269180911188271892937277)
              ·
                refine ⟨100942841695601959851479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269180911188271892937277 100942841695601959851479)
                ·
                  rfl

theorem cell19_331738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_331738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331738 prefixEnd_331738 := by exact prefixLift 331738
  have htrace : WordTrace (prefixWord ++ tailWord_331738) baseStart_331738 baseEnd_331738 := by
    simpa [prefixWord, tailWord_331738, baseEnd_331738] using wordTrace_append hprefix tailTrace_331738
  have hstable : (prefixWord ++ tailWord_331738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331738).length < 2 ^ (prefixWord ++ tailWord_331738).sum := by decide
  have hdescent : baseEnd_331738 < baseStart_331738 := by decide
  rcases family_descends (prefixWord ++ tailWord_331738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331757 : List Nat := [1, 5, 1, 4, 1, 2, 5]
def baseStart_331757 : Nat := 118140960795 + 331757 * 2 ^ 59
def prefixEnd_331757 : Nat := 4983230072969 + 3 ^ 40 * 331757 * 2
def baseEnd_331757 : Nat := 33649541035805181809735

theorem tailTrace_331757 : CollatzResearch.WordTrace tailWord_331757 prefixEnd_331757 33649541035805181809735 := by
  unfold tailWord_331757
  simp only [CollatzResearch.WordTrace]
  refine ⟨12100171859108523429809525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8066781239405682286539683 12100171859108523429809525)
  ·
    refine ⟨1134391111791424071544643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12100171859108523429809525 1134391111791424071544643)
    ·
      refine ⟨1701586667687136107316965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1134391111791424071544643 1701586667687136107316965)
      ·
        refine ⟨319047500191338020121931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1701586667687136107316965 319047500191338020121931)
        ·
          refine ⟨478571250287007030182897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319047500191338020121931 478571250287007030182897)
          ·
            refine ⟨358928437715255272637173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478571250287007030182897 358928437715255272637173)
            ·
              refine ⟨33649541035805181809735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 358928437715255272637173 33649541035805181809735)
              ·
                rfl

theorem cell19_331757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_331757 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331757 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331757 prefixEnd_331757 := by exact prefixLift 331757
  have htrace : WordTrace (prefixWord ++ tailWord_331757) baseStart_331757 baseEnd_331757 := by
    simpa [prefixWord, tailWord_331757, baseEnd_331757] using wordTrace_append hprefix tailTrace_331757
  have hstable : (prefixWord ++ tailWord_331757).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331757).length < 2 ^ (prefixWord ++ tailWord_331757).sum := by decide
  have hdescent : baseEnd_331757 < baseStart_331757 := by decide
  rcases family_descends (prefixWord ++ tailWord_331757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331816 : List Nat := [2, 1, 5, 3, 1, 7]
def baseStart_331816 : Nat := 118140960795 + 331816 * 2 ^ 59
def prefixEnd_331816 : Nat := 4983230072969 + 3 ^ 40 * 331816 * 2
def baseEnd_331816 : Nat := 11218508434724543346437

theorem tailTrace_331816 : CollatzResearch.WordTrace tailWord_331816 prefixEnd_331816 11218508434724543346437 := by
  unfold tailWord_331816
  simp only [CollatzResearch.WordTrace]
  refine ⟨6051161882947388253103651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8068215843929851004138201 6051161882947388253103651)
  ·
    refine ⟨9076742824421082379655477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6051161882947388253103651 9076742824421082379655477)
    ·
      refine ⟨850944639789476473092701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9076742824421082379655477 850944639789476473092701)
      ·
        refine ⟨319104239921053677409763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 850944639789476473092701 319104239921053677409763)
        ·
          refine ⟨478656359881580516114645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319104239921053677409763 478656359881580516114645)
          ·
            refine ⟨11218508434724543346437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 478656359881580516114645 11218508434724543346437)
            ·
              rfl

theorem cell19_331816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 7].length) (baseStart_331816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331816 prefixEnd_331816 := by exact prefixLift 331816
  have htrace : WordTrace (prefixWord ++ tailWord_331816) baseStart_331816 baseEnd_331816 := by
    simpa [prefixWord, tailWord_331816, baseEnd_331816] using wordTrace_append hprefix tailTrace_331816
  have hstable : (prefixWord ++ tailWord_331816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331816).length < 2 ^ (prefixWord ++ tailWord_331816).sum := by decide
  have hdescent : baseEnd_331816 < baseStart_331816 := by decide
  rcases family_descends (prefixWord ++ tailWord_331816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331818 : List Nat := [3, 1, 4, 1, 2, 8]
def baseStart_331818 : Nat := 118140960795 + 331818 * 2 ^ 59
def prefixEnd_331818 : Nat := 4983230072969 + 3 ^ 40 * 331818 * 2
def baseEnd_331818 : Nat := 11218576053576164230387

theorem tailTrace_331818 : CollatzResearch.WordTrace tailWord_331818 prefixEnd_331818 11218576053576164230387 := by
  unfold tailWord_331818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025599177971882711945027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8068264474591687231853405 3025599177971882711945027)
  ·
    refine ⟨4538398766957824067917541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3025599177971882711945027 4538398766957824067917541)
    ·
      refine ⟨850949768804592012734539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4538398766957824067917541 850949768804592012734539)
      ·
        refine ⟨1276424653206888019101809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850949768804592012734539 1276424653206888019101809)
        ·
          refine ⟨957318489905166014326357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276424653206888019101809 957318489905166014326357)
          ·
            refine ⟨11218576053576164230387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 957318489905166014326357 11218576053576164230387)
            ·
              rfl

theorem cell19_331818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 8].length) (baseStart_331818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331818 prefixEnd_331818 := by exact prefixLift 331818
  have htrace : WordTrace (prefixWord ++ tailWord_331818) baseStart_331818 baseEnd_331818 := by
    simpa [prefixWord, tailWord_331818, baseEnd_331818] using wordTrace_append hprefix tailTrace_331818
  have hstable : (prefixWord ++ tailWord_331818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331818).length < 2 ^ (prefixWord ++ tailWord_331818).sum := by decide
  have hdescent : baseEnd_331818 < baseStart_331818 := by decide
  rcases family_descends (prefixWord ++ tailWord_331818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331833 : List Nat := [1, 2, 1, 5, 4, 1, 1, 4]
def baseStart_331833 : Nat := 118140960795 + 331833 * 2 ^ 59
def prefixEnd_331833 : Nat := 4983230072969 + 3 ^ 40 * 331833 * 2
def baseEnd_331833 : Nat := 100971748754669887740109

theorem tailTrace_331833 : CollatzResearch.WordTrace tailWord_331833 prefixEnd_331833 100971748754669887740109 := by
  unfold tailWord_331833
  simp only [CollatzResearch.WordTrace]
  refine ⟨12102943806833188409576153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8068629204555458939717435 12102943806833188409576153)
  ·
    refine ⟨9077207855124891307182115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12102943806833188409576153 9077207855124891307182115)
    ·
      refine ⟨13615811782687336960773173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9077207855124891307182115 13615811782687336960773173)
      ·
        refine ⟨1276482354626937840072485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13615811782687336960773173 1276482354626937840072485)
        ·
          refine ⟨239340441492550845013591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1276482354626937840072485 239340441492550845013591)
          ·
            refine ⟨359010662238826267520387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239340441492550845013591 359010662238826267520387)
            ·
              refine ⟨538515993358239401280581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359010662238826267520387 538515993358239401280581)
              ·
                refine ⟨100971748754669887740109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538515993358239401280581 100971748754669887740109)
                ·
                  rfl

theorem cell19_331833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 4].length) (baseStart_331833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331833 prefixEnd_331833 := by exact prefixLift 331833
  have htrace : WordTrace (prefixWord ++ tailWord_331833) baseStart_331833 baseEnd_331833 := by
    simpa [prefixWord, tailWord_331833, baseEnd_331833] using wordTrace_append hprefix tailTrace_331833
  have hstable : (prefixWord ++ tailWord_331833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331833).length < 2 ^ (prefixWord ++ tailWord_331833).sum := by decide
  have hdescent : baseEnd_331833 < baseStart_331833 := by decide
  rcases family_descends (prefixWord ++ tailWord_331833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331854 : List Nat := [4, 1, 1, 1, 1, 5, 3, 3]
def baseStart_331854 : Nat := 118140960795 + 331854 * 2 ^ 59
def prefixEnd_331854 : Nat := 4983230072969 + 3 ^ 40 * 331854 * 2
def baseEnd_331854 : Nat := 100978138736148061273385

theorem tailTrace_331854 : CollatzResearch.WordTrace tailWord_331854 prefixEnd_331854 100978138736148061273385 := by
  unfold tailWord_331854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512963717469638624511327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8069139826504739330727077 1512963717469638624511327)
  ·
    refine ⟨2269445576204457936766991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512963717469638624511327 2269445576204457936766991)
    ·
      refine ⟨3404168364306686905150487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269445576204457936766991 3404168364306686905150487)
      ·
        refine ⟨5106252546460030357725731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404168364306686905150487 5106252546460030357725731)
        ·
          refine ⟨7659378819690045536588597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106252546460030357725731 7659378819690045536588597)
          ·
            refine ⟨718066764345941769055181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7659378819690045536588597 718066764345941769055181)
            ·
              refine ⟨269275036629728163395693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 718066764345941769055181 269275036629728163395693)
              ·
                refine ⟨100978138736148061273385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269275036629728163395693 100978138736148061273385)
                ·
                  rfl

theorem cell19_331854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_331854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331854 prefixEnd_331854 := by exact prefixLift 331854
  have htrace : WordTrace (prefixWord ++ tailWord_331854) baseStart_331854 baseEnd_331854 := by
    simpa [prefixWord, tailWord_331854, baseEnd_331854] using wordTrace_append hprefix tailTrace_331854
  have hstable : (prefixWord ++ tailWord_331854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331854).length < 2 ^ (prefixWord ++ tailWord_331854).sum := by decide
  have hdescent : baseEnd_331854 < baseStart_331854 := by decide
  rcases family_descends (prefixWord ++ tailWord_331854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331896 : List Nat := [2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_331896 : Nat := 118140960795 + 331896 * 2 ^ 59
def prefixEnd_331896 : Nat := 4983230072969 + 3 ^ 40 * 331896 * 2
def baseEnd_331896 : Nat := 100990918699104408339937

theorem tailTrace_331896 : CollatzResearch.WordTrace tailWord_331896 prefixEnd_331896 100990918699104408339937 := by
  unfold tailWord_331896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052620802802475084559771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8070161070403300112746361 6052620802802475084559771)
  ·
    refine ⟨9078931204203712626839657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6052620802802475084559771 9078931204203712626839657)
    ·
      refine ⟨6809198403152784470129743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9078931204203712626839657 6809198403152784470129743)
      ·
        refine ⟨10213797604729176705194615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809198403152784470129743 10213797604729176705194615)
        ·
          refine ⟨15320696407093765057791923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10213797604729176705194615 15320696407093765057791923)
          ·
            refine ⟨22981044610640647586687885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15320696407093765057791923 22981044610640647586687885)
            ·
              refine ⟨8617891728990242845007957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22981044610640647586687885 8617891728990242845007957)
              ·
                refine ⟨100990918699104408339937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8617891728990242845007957 100990918699104408339937)
                ·
                  rfl

theorem cell19_331896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_331896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331896 prefixEnd_331896 := by exact prefixLift 331896
  have htrace : WordTrace (prefixWord ++ tailWord_331896) baseStart_331896 baseEnd_331896 := by
    simpa [prefixWord, tailWord_331896, baseEnd_331896] using wordTrace_append hprefix tailTrace_331896
  have hstable : (prefixWord ++ tailWord_331896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331896).length < 2 ^ (prefixWord ++ tailWord_331896).sum := by decide
  have hdescent : baseEnd_331896 < baseStart_331896 := by decide
  rcases family_descends (prefixWord ++ tailWord_331896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331930 : List Nat := [3, 1, 1, 5, 2, 2, 5]
def baseStart_331930 : Nat := 118140960795 + 331930 * 2 ^ 59
def prefixEnd_331930 : Nat := 4983230072969 + 3 ^ 40 * 331930 * 2
def baseEnd_331930 : Nat := 33667088127800801194763

theorem tailTrace_331930 : CollatzResearch.WordTrace tailWord_331930 prefixEnd_331930 33667088127800801194763 := by
  unfold tailWord_331930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026620421870443493964311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8070987791654515983904829 3026620421870443493964311)
  ·
    refine ⟨4539930632805665240946467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3026620421870443493964311 4539930632805665240946467)
    ·
      refine ⟨6809895949208497861419701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4539930632805665240946467 6809895949208497861419701)
      ·
        refine ⟨638427745238296674508097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6809895949208497861419701 638427745238296674508097)
        ·
          refine ⟨478820808928722505881073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638427745238296674508097 478820808928722505881073)
          ·
            refine ⟨359115606696541879410805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478820808928722505881073 359115606696541879410805)
            ·
              refine ⟨33667088127800801194763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 359115606696541879410805 33667088127800801194763)
              ·
                rfl

theorem cell19_331930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_331930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331930 prefixEnd_331930 := by exact prefixLift 331930
  have htrace : WordTrace (prefixWord ++ tailWord_331930) baseStart_331930 baseEnd_331930 := by
    simpa [prefixWord, tailWord_331930, baseEnd_331930] using wordTrace_append hprefix tailTrace_331930
  have hstable : (prefixWord ++ tailWord_331930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331930).length < 2 ^ (prefixWord ++ tailWord_331930).sum := by decide
  have hdescent : baseEnd_331930 < baseStart_331930 := by decide
  rcases family_descends (prefixWord ++ tailWord_331930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331949 : List Nat := [1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_331949 : Nat := 118140960795 + 331949 * 2 ^ 59
def prefixEnd_331949 : Nat := 4983230072969 + 3 ^ 40 * 331949 * 2
def baseEnd_331949 : Nat := 101007045795215989162015

theorem tailTrace_331949 : CollatzResearch.WordTrace tailWord_331949 prefixEnd_331949 101007045795215989162015 := by
  unfold tailWord_331949
  simp only [CollatzResearch.WordTrace]
  refine ⟨12107174674412940220798901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8071449782941960147199267 12107174674412940220798901)
  ·
    refine ⟨1135047625726213145699897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12107174674412940220798901 1135047625726213145699897)
    ·
      refine ⟨851285719294659859274923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1135047625726213145699897 851285719294659859274923)
      ·
        refine ⟨1276928578941989788912385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851285719294659859274923 1276928578941989788912385)
        ·
          refine ⟨957696434206492341684289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276928578941989788912385 957696434206492341684289)
          ·
            refine ⟨718272325654869256263217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957696434206492341684289 718272325654869256263217)
            ·
              refine ⟨538704244241151942197413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718272325654869256263217 538704244241151942197413)
              ·
                refine ⟨101007045795215989162015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538704244241151942197413 101007045795215989162015)
                ·
                  rfl

theorem cell19_331949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_331949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331949 prefixEnd_331949 := by exact prefixLift 331949
  have htrace : WordTrace (prefixWord ++ tailWord_331949) baseStart_331949 baseEnd_331949 := by
    simpa [prefixWord, tailWord_331949, baseEnd_331949] using wordTrace_append hprefix tailTrace_331949
  have hstable : (prefixWord ++ tailWord_331949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331949).length < 2 ^ (prefixWord ++ tailWord_331949).sum := by decide
  have hdescent : baseEnd_331949 < baseStart_331949 := by decide
  rcases family_descends (prefixWord ++ tailWord_331949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331989 : List Nat := [1, 3, 2, 4, 2, 7]
def baseStart_331989 : Nat := 118140960795 + 331989 * 2 ^ 59
def prefixEnd_331989 : Nat := 4983230072969 + 3 ^ 40 * 331989 * 2
def baseEnd_331989 : Nat := 11224357465389749808113

theorem tailTrace_331989 : CollatzResearch.WordTrace tailWord_331989 prefixEnd_331989 11224357465389749808113 := by
  unfold tailWord_331989
  simp only [CollatzResearch.WordTrace]
  refine ⟨12108633594268027052255021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8072422396178684701503347 12108633594268027052255021)
  ·
    refine ⟨4540737597850510144595633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12108633594268027052255021 4540737597850510144595633)
    ·
      refine ⟨3405553198387882608446725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4540737597850510144595633 3405553198387882608446725)
      ·
        refine ⟨638541224697727989083761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3405553198387882608446725 638541224697727989083761)
        ·
          refine ⟨478905918523295991812821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638541224697727989083761 478905918523295991812821)
          ·
            refine ⟨11224357465389749808113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 478905918523295991812821 11224357465389749808113)
            ·
              rfl

theorem cell19_331989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 7].length) (baseStart_331989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_331989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_331989 prefixEnd_331989 := by exact prefixLift 331989
  have htrace : WordTrace (prefixWord ++ tailWord_331989) baseStart_331989 baseEnd_331989 := by
    simpa [prefixWord, tailWord_331989, baseEnd_331989] using wordTrace_append hprefix tailTrace_331989
  have hstable : (prefixWord ++ tailWord_331989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331989).length < 2 ^ (prefixWord ++ tailWord_331989).sum := by decide
  have hdescent : baseEnd_331989 < baseStart_331989 := by decide
  rcases family_descends (prefixWord ++ tailWord_331989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332008 : List Nat := [2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_332008 : Nat := 118140960795 + 332008 * 2 ^ 59
def prefixEnd_332008 : Nat := 4983230072969 + 3 ^ 40 * 332008 * 2
def baseEnd_332008 : Nat := 101024998600321333850743

theorem tailTrace_332008 : CollatzResearch.WordTrace tailWord_332008 prefixEnd_332008 101024998600321333850743 := by
  unfold tailWord_332008
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054663290599596648598339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8072884387466128864797785 6054663290599596648598339)
  ·
    refine ⟨9081994935899394972897509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6054663290599596648598339 9081994935899394972897509)
    ·
      refine ⟨1702874050481136557418283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9081994935899394972897509 1702874050481136557418283)
      ·
        refine ⟨2554311075721704836127425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702874050481136557418283 2554311075721704836127425)
        ·
          refine ⟨1915733306791278627095569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2554311075721704836127425 1915733306791278627095569)
          ·
            refine ⟨1436799980093458970321677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1915733306791278627095569 1436799980093458970321677)
            ·
              refine ⟨538799992535047113870629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1436799980093458970321677 538799992535047113870629)
              ·
                refine ⟨101024998600321333850743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538799992535047113870629 101024998600321333850743)
                ·
                  rfl

theorem cell19_332008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_332008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332008 prefixEnd_332008 := by exact prefixLift 332008
  have htrace : WordTrace (prefixWord ++ tailWord_332008) baseStart_332008 baseEnd_332008 := by
    simpa [prefixWord, tailWord_332008, baseEnd_332008] using wordTrace_append hprefix tailTrace_332008
  have hstable : (prefixWord ++ tailWord_332008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332008).length < 2 ^ (prefixWord ++ tailWord_332008).sum := by decide
  have hdescent : baseEnd_332008 < baseStart_332008 := by decide
  rcases family_descends (prefixWord ++ tailWord_332008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332029 : List Nat := [1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_332029 : Nat := 118140960795 + 332029 * 2 ^ 59
def prefixEnd_332029 : Nat := 4983230072969 + 3 ^ 40 * 332029 * 2
def baseEnd_332029 : Nat := 101031388581799507384019

theorem tailTrace_332029 : CollatzResearch.WordTrace tailWord_332029 prefixEnd_332029 101031388581799507384019 := by
  unfold tailWord_332029
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110092514123113883711141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8073395009415409255807427 12110092514123113883711141)
  ·
    refine ⟨2270642346398083853195839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12110092514123113883711141 2270642346398083853195839)
    ·
      refine ⟨3405963519597125779793759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270642346398083853195839 3405963519597125779793759)
      ·
        refine ⟨5108945279395688669690639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405963519597125779793759 5108945279395688669690639)
        ·
          refine ⟨7663417919093533004535959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5108945279395688669690639 7663417919093533004535959)
          ·
            refine ⟨11495126878640299506803939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663417919093533004535959 11495126878640299506803939)
            ·
              refine ⟨17242690317960449260205909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11495126878640299506803939 17242690317960449260205909)
              ·
                refine ⟨101031388581799507384019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17242690317960449260205909 101031388581799507384019)
                ·
                  rfl

theorem cell19_332029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_332029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332029 prefixEnd_332029 := by exact prefixLift 332029
  have htrace : WordTrace (prefixWord ++ tailWord_332029) baseStart_332029 baseEnd_332029 := by
    simpa [prefixWord, tailWord_332029, baseEnd_332029] using wordTrace_append hprefix tailTrace_332029
  have hstable : (prefixWord ++ tailWord_332029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332029).length < 2 ^ (prefixWord ++ tailWord_332029).sum := by decide
  have hdescent : baseEnd_332029 < baseStart_332029 := by decide
  rcases family_descends (prefixWord ++ tailWord_332029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332067 : List Nat := [1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_332067 : Nat := 118140960795 + 332067 * 2 ^ 59
def prefixEnd_332067 : Nat := 4983230072969 + 3 ^ 40 * 332067 * 2
def baseEnd_332067 : Nat := 101042951405426678539471

theorem tailTrace_332067 : CollatzResearch.WordTrace tailWord_332067 prefixEnd_332067 101042951405426678539471 := by
  unfold tailWord_332067
  simp only [CollatzResearch.WordTrace]
  refine ⟨12111478487985446373594455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8074318991990297582396303 12111478487985446373594455)
  ·
    refine ⟨18167217731978169560391683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12111478487985446373594455 18167217731978169560391683)
    ·
      refine ⟨27250826597967254340587525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18167217731978169560391683 27250826597967254340587525)
      ·
        refine ⟨5109529987118860188860161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27250826597967254340587525 5109529987118860188860161)
        ·
          refine ⟨3832147490339145141645121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5109529987118860188860161 3832147490339145141645121)
          ·
            refine ⟨2874110617754358856233841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3832147490339145141645121 2874110617754358856233841)
            ·
              refine ⟨2155582963315769142175381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874110617754358856233841 2155582963315769142175381)
              ·
                refine ⟨101042951405426678539471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2155582963315769142175381 101042951405426678539471)
                ·
                  rfl

theorem cell19_332067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_332067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332067 prefixEnd_332067 := by exact prefixLift 332067
  have htrace : WordTrace (prefixWord ++ tailWord_332067) baseStart_332067 baseEnd_332067 := by
    simpa [prefixWord, tailWord_332067, baseEnd_332067] using wordTrace_append hprefix tailTrace_332067
  have hstable : (prefixWord ++ tailWord_332067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332067).length < 2 ^ (prefixWord ++ tailWord_332067).sum := by decide
  have hdescent : baseEnd_332067 < baseStart_332067 := by decide
  rcases family_descends (prefixWord ++ tailWord_332067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332078 : List Nat := [4, 1, 3, 3, 1, 2, 2, 3]
def baseStart_332078 : Nat := 118140960795 + 332078 * 2 ^ 59
def prefixEnd_332078 : Nat := 4983230072969 + 3 ^ 40 * 332078 * 2
def baseEnd_332078 : Nat := 101046298538581912294997

theorem tailTrace_332078 : CollatzResearch.WordTrace tailWord_332078 prefixEnd_332078 101046298538581912294997 := by
  unfold tailWord_332078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513984961368199406530611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8074586460630396834829925 1513984961368199406530611)
  ·
    refine ⟨2270977442052299109795917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1513984961368199406530611 2270977442052299109795917)
    ·
      refine ⟨851616540769612166173469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2270977442052299109795917 851616540769612166173469)
      ·
        refine ⟨319356202788604562315051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 851616540769612166173469 319356202788604562315051)
        ·
          refine ⟨479034304182906843472577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319356202788604562315051 479034304182906843472577)
          ·
            refine ⟨359275728137180132604433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479034304182906843472577 359275728137180132604433)
            ·
              refine ⟨269456796102885099453325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359275728137180132604433 269456796102885099453325)
              ·
                refine ⟨101046298538581912294997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269456796102885099453325 101046298538581912294997)
                ·
                  rfl

theorem cell19_332078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_332078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332078 prefixEnd_332078 := by exact prefixLift 332078
  have htrace : WordTrace (prefixWord ++ tailWord_332078) baseStart_332078 baseEnd_332078 := by
    simpa [prefixWord, tailWord_332078, baseEnd_332078] using wordTrace_append hprefix tailTrace_332078
  have hstable : (prefixWord ++ tailWord_332078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332078).length < 2 ^ (prefixWord ++ tailWord_332078).sum := by decide
  have hdescent : baseEnd_332078 < baseStart_332078 := by decide
  rcases family_descends (prefixWord ++ tailWord_332078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332238 : List Nat := [4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_332238 : Nat := 118140960795 + 332238 * 2 ^ 59
def prefixEnd_332238 : Nat := 4983230072969 + 3 ^ 40 * 332238 * 2
def baseEnd_332238 : Nat := 101094984111748948739005

theorem tailTrace_332238 : CollatzResearch.WordTrace tailWord_332238 prefixEnd_332238 101094984111748948739005 := by
  unfold tailWord_332238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514714421295742822258671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8078476913577295052046245 1514714421295742822258671)
  ·
    refine ⟨2272071631943614233388007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1514714421295742822258671 2272071631943614233388007)
    ·
      refine ⟨3408107447915421350082011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272071631943614233388007 3408107447915421350082011)
      ·
        refine ⟨5112161171873132025123017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408107447915421350082011 5112161171873132025123017)
        ·
          refine ⟨3834120878904849018842263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5112161171873132025123017 3834120878904849018842263)
          ·
            refine ⟨5751181318357273528263395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834120878904849018842263 5751181318357273528263395)
            ·
              refine ⟨8626771977535910292395093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751181318357273528263395 8626771977535910292395093)
              ·
                refine ⟨101094984111748948739005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8626771977535910292395093 101094984111748948739005)
                ·
                  rfl

theorem cell19_332238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_332238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332238 prefixEnd_332238 := by exact prefixLift 332238
  have htrace : WordTrace (prefixWord ++ tailWord_332238) baseStart_332238 baseEnd_332238 := by
    simpa [prefixWord, tailWord_332238, baseEnd_332238] using wordTrace_append hprefix tailTrace_332238
  have hstable : (prefixWord ++ tailWord_332238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332238).length < 2 ^ (prefixWord ++ tailWord_332238).sum := by decide
  have hdescent : baseEnd_332238 < baseStart_332238 := by decide
  rcases family_descends (prefixWord ++ tailWord_332238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332255 : List Nat := [1, 1, 2, 3, 3, 2, 4, 3]
def baseStart_332255 : Nat := 118140960795 + 332255 * 2 ^ 59
def prefixEnd_332255 : Nat := 4983230072969 + 3 ^ 40 * 332255 * 2
def baseEnd_332255 : Nat := 101100156953897946361181

theorem tailTrace_332255 : CollatzResearch.WordTrace tailWord_332255 prefixEnd_332255 101100156953897946361181 := by
  unfold tailWord_332255
  simp only [CollatzResearch.WordTrace]
  refine ⟨12118335411304354481438219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8078890274202902987625479 12118335411304354481438219)
  ·
    refine ⟨18177503116956531722157329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12118335411304354481438219 18177503116956531722157329)
    ·
      refine ⟨13633127337717398791617997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18177503116956531722157329 13633127337717398791617997)
      ·
        refine ⟨5112422751644024546856749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13633127337717398791617997 5112422751644024546856749)
        ·
          refine ⟨1917158531866509205071281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5112422751644024546856749 1917158531866509205071281)
          ·
            refine ⟨1437868898899881903803461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1917158531866509205071281 1437868898899881903803461)
            ·
              refine ⟨269600418543727856963149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1437868898899881903803461 269600418543727856963149)
              ·
                refine ⟨101100156953897946361181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269600418543727856963149 101100156953897946361181)
                ·
                  rfl

theorem cell19_332255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_332255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332255 prefixEnd_332255 := by exact prefixLift 332255
  have htrace : WordTrace (prefixWord ++ tailWord_332255) baseStart_332255 baseEnd_332255 := by
    simpa [prefixWord, tailWord_332255, baseEnd_332255] using wordTrace_append hprefix tailTrace_332255
  have hstable : (prefixWord ++ tailWord_332255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332255).length < 2 ^ (prefixWord ++ tailWord_332255).sum := by decide
  have hdescent : baseEnd_332255 < baseStart_332255 := by decide
  rcases family_descends (prefixWord ++ tailWord_332255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332257 : List Nat := [1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_332257 : Nat := 118140960795 + 332257 * 2 ^ 59
def prefixEnd_332257 : Nat := 4983230072969 + 3 ^ 40 * 332257 * 2
def baseEnd_332257 : Nat := 101100765523562534316731

theorem tailTrace_332257 : CollatzResearch.WordTrace tailWord_332257 prefixEnd_332257 101100765523562534316731 := by
  unfold tailWord_332257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12118408357297108823011025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8078938904864739215340683 12118408357297108823011025)
  ·
    refine ⟨9088806267972831617258269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12118408357297108823011025 9088806267972831617258269)
    ·
      refine ⟨3408302350489811856471851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9088806267972831617258269 3408302350489811856471851)
      ·
        refine ⟨5112453525734717784707777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408302350489811856471851 5112453525734717784707777)
        ·
          refine ⟨3834340144301038338530833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5112453525734717784707777 3834340144301038338530833)
          ·
            refine ⟨2875755108225778753898125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3834340144301038338530833 2875755108225778753898125)
            ·
              refine ⟨1078408165584667032711797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2875755108225778753898125 1078408165584667032711797)
              ·
                refine ⟨101100765523562534316731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1078408165584667032711797 101100765523562534316731)
                ·
                  rfl

theorem cell19_332257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_332257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332257 prefixEnd_332257 := by exact prefixLift 332257
  have htrace : WordTrace (prefixWord ++ tailWord_332257) baseStart_332257 baseEnd_332257 := by
    simpa [prefixWord, tailWord_332257, baseEnd_332257] using wordTrace_append hprefix tailTrace_332257
  have hstable : (prefixWord ++ tailWord_332257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332257).length < 2 ^ (prefixWord ++ tailWord_332257).sum := by decide
  have hdescent : baseEnd_332257 < baseStart_332257 := by decide
  rcases family_descends (prefixWord ++ tailWord_332257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332314 : List Nat := [3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_332314 : Nat := 118140960795 + 332314 * 2 ^ 59
def prefixEnd_332314 : Nat := 4983230072969 + 3 ^ 40 * 332314 * 2
def baseEnd_332314 : Nat := 101118109759003291049909

theorem tailTrace_332314 : CollatzResearch.WordTrace tailWord_332314 prefixEnd_332314 101118109759003291049909 := by
  unfold tailWord_332314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030121829522651889458999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8080324878727071705223997 3030121829522651889458999)
  ·
    refine ⟨4545182744283977834188499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3030121829522651889458999 4545182744283977834188499)
    ·
      refine ⟨6817774116425966751282749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4545182744283977834188499 6817774116425966751282749)
      ·
        refine ⟨2556665293659737531731031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6817774116425966751282749 2556665293659737531731031)
        ·
          refine ⟨3834997940489606297596547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556665293659737531731031 3834997940489606297596547)
          ·
            refine ⟨5752496910734409446394821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834997940489606297596547 5752496910734409446394821)
            ·
              refine ⟨1078593170762701771199029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5752496910734409446394821 1078593170762701771199029)
              ·
                refine ⟨101118109759003291049909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1078593170762701771199029 101118109759003291049909)
                ·
                  rfl

theorem cell19_332314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_332314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332314 prefixEnd_332314 := by exact prefixLift 332314
  have htrace : WordTrace (prefixWord ++ tailWord_332314) baseStart_332314 baseEnd_332314 := by
    simpa [prefixWord, tailWord_332314, baseEnd_332314] using wordTrace_append hprefix tailTrace_332314
  have hstable : (prefixWord ++ tailWord_332314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332314).length < 2 ^ (prefixWord ++ tailWord_332314).sum := by decide
  have hdescent : baseEnd_332314 < baseStart_332314 := by decide
  rcases family_descends (prefixWord ++ tailWord_332314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332352 : List Nat := [2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_332352 : Nat := 118140960795 + 332352 * 2 ^ 59
def prefixEnd_332352 : Nat := 4983230072969 + 3 ^ 40 * 332352 * 2
def baseEnd_332352 : Nat := 101129672582630462205361

theorem tailTrace_332352 : CollatzResearch.WordTrace tailWord_332352 prefixEnd_332352 101129672582630462205361 := by
  unfold tailWord_332352
  simp only [CollatzResearch.WordTrace]
  refine ⟨6060936645976470023859655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8081248861301960031812873 6060936645976470023859655)
  ·
    refine ⟨9091404968964705035789483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6060936645976470023859655 9091404968964705035789483)
    ·
      refine ⟨13637107453447057553684225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9091404968964705035789483 13637107453447057553684225)
      ·
        refine ⟨10227830590085293165263169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13637107453447057553684225 10227830590085293165263169)
        ·
          refine ⟨7670872942563969873947377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10227830590085293165263169 7670872942563969873947377)
          ·
            refine ⟨5753154706922977405460533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7670872942563969873947377 5753154706922977405460533)
            ·
              refine ⟨539358253774029131761925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5753154706922977405460533 539358253774029131761925)
              ·
                refine ⟨101129672582630462205361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 539358253774029131761925 101129672582630462205361)
                ·
                  rfl

theorem cell19_332352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_332352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332352 prefixEnd_332352 := by exact prefixLift 332352
  have htrace : WordTrace (prefixWord ++ tailWord_332352) baseStart_332352 baseEnd_332352 := by
    simpa [prefixWord, tailWord_332352, baseEnd_332352] using wordTrace_append hprefix tailTrace_332352
  have hstable : (prefixWord ++ tailWord_332352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332352).length < 2 ^ (prefixWord ++ tailWord_332352).sum := by decide
  have hdescent : baseEnd_332352 < baseStart_332352 := by decide
  rcases family_descends (prefixWord ++ tailWord_332352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332369 : List Nat := [1, 2, 2, 1, 3, 4, 3, 3]
def baseStart_332369 : Nat := 118140960795 + 332369 * 2 ^ 59
def prefixEnd_332369 : Nat := 4983230072969 + 3 ^ 40 * 332369 * 2
def baseEnd_332369 : Nat := 101134845424779459827537

theorem tailTrace_332369 : CollatzResearch.WordTrace tailWord_332369 prefixEnd_332369 101134845424779459827537 := by
  unfold tailWord_332369
  simp only [CollatzResearch.WordTrace]
  refine ⟨12122493332891351951088161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8081662221927567967392107 12122493332891351951088161)
  ·
    refine ⟨9091869999668513963316121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12122493332891351951088161 9091869999668513963316121)
    ·
      refine ⟨6818902499751385472487091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9091869999668513963316121 6818902499751385472487091)
      ·
        refine ⟨10228353749627078208730637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6818902499751385472487091 10228353749627078208730637)
        ·
          refine ⟨3835632656110154328273989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10228353749627078208730637 3835632656110154328273989)
          ·
            refine ⟨719181123020653936551373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3835632656110154328273989 719181123020653936551373)
            ·
              refine ⟨269692921132745226206765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 719181123020653936551373 269692921132745226206765)
              ·
                refine ⟨101134845424779459827537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269692921132745226206765 101134845424779459827537)
                ·
                  rfl

theorem cell19_332369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_332369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332369 prefixEnd_332369 := by exact prefixLift 332369
  have htrace : WordTrace (prefixWord ++ tailWord_332369) baseStart_332369 baseEnd_332369 := by
    simpa [prefixWord, tailWord_332369, baseEnd_332369] using wordTrace_append hprefix tailTrace_332369
  have hstable : (prefixWord ++ tailWord_332369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332369).length < 2 ^ (prefixWord ++ tailWord_332369).sum := by decide
  have hdescent : baseEnd_332369 < baseStart_332369 := by decide
  rcases family_descends (prefixWord ++ tailWord_332369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332386 : List Nat := [3, 3, 2, 3, 1, 1, 6]
def baseStart_332386 : Nat := 118140960795 + 332386 * 2 ^ 59
def prefixEnd_332386 : Nat := 4983230072969 + 3 ^ 40 * 332386 * 2
def baseEnd_332386 : Nat := 33713339422309485816571

theorem tailTrace_332386 : CollatzResearch.WordTrace tailWord_332386 prefixEnd_332386 33713339422309485816571 := by
  unfold tailWord_332386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030778343457440963614253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8082075582553175902971341 3030778343457440963614253)
  ·
    refine ⟨1136541878796540361355345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3030778343457440963614253 1136541878796540361355345)
    ·
      refine ⟨852406409097405271016509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1136541878796540361355345 852406409097405271016509)
      ·
        refine ⟨319652403411526976631191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 852406409097405271016509 319652403411526976631191)
        ·
          refine ⟨479478605117290464946787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319652403411526976631191 479478605117290464946787)
          ·
            refine ⟨719217907675935697420181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479478605117290464946787 719217907675935697420181)
            ·
              refine ⟨33713339422309485816571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 719217907675935697420181 33713339422309485816571)
              ·
                rfl

theorem cell19_332386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_332386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332386 prefixEnd_332386 := by exact prefixLift 332386
  have htrace : WordTrace (prefixWord ++ tailWord_332386) baseStart_332386 baseEnd_332386 := by
    simpa [prefixWord, tailWord_332386, baseEnd_332386] using wordTrace_append hprefix tailTrace_332386
  have hstable : (prefixWord ++ tailWord_332386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332386).length < 2 ^ (prefixWord ++ tailWord_332386).sum := by decide
  have hdescent : baseEnd_332386 < baseStart_332386 := by decide
  rcases family_descends (prefixWord ++ tailWord_332386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332418 : List Nat := [3, 4, 3, 1, 1, 2, 2, 3]
def baseStart_332418 : Nat := 118140960795 + 332418 * 2 ^ 59
def prefixEnd_332418 : Nat := 4983230072969 + 3 ^ 40 * 332418 * 2
def baseEnd_332418 : Nat := 101149755381561864738515

theorem tailTrace_332418 : CollatzResearch.WordTrace tailWord_332418 prefixEnd_332418 101149755381561864738515 := by
  unfold tailWord_332418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031070127428458329905477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8082853673142555546414605 3031070127428458329905477)
  ·
    refine ⟨568325648892835936857277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3031070127428458329905477 568325648892835936857277)
    ·
      refine ⟨213122118334813476321479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 568325648892835936857277 213122118334813476321479)
      ·
        refine ⟨319683177502220214482219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213122118334813476321479 319683177502220214482219)
        ·
          refine ⟨479524766253330321723329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319683177502220214482219 479524766253330321723329)
          ·
            refine ⟨359643574689997741292497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479524766253330321723329 359643574689997741292497)
            ·
              refine ⟨269732681017498305969373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359643574689997741292497 269732681017498305969373)
              ·
                refine ⟨101149755381561864738515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269732681017498305969373 101149755381561864738515)
                ·
                  rfl

theorem cell19_332418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_332418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332418 prefixEnd_332418 := by exact prefixLift 332418
  have htrace : WordTrace (prefixWord ++ tailWord_332418) baseStart_332418 baseEnd_332418 := by
    simpa [prefixWord, tailWord_332418, baseEnd_332418] using wordTrace_append hprefix tailTrace_332418
  have hstable : (prefixWord ++ tailWord_332418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332418).length < 2 ^ (prefixWord ++ tailWord_332418).sum := by decide
  have hdescent : baseEnd_332418 < baseStart_332418 := by decide
  rcases family_descends (prefixWord ++ tailWord_332418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332426 : List Nat := [3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_332426 : Nat := 118140960795 + 332426 * 2 ^ 59
def prefixEnd_332426 : Nat := 4983230072969 + 3 ^ 40 * 332426 * 2
def baseEnd_332426 : Nat := 101152189660220216560715

theorem tailTrace_332426 : CollatzResearch.WordTrace tailWord_332426 prefixEnd_332426 101152189660220216560715 := by
  unfold tailWord_332426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031143073421212671478283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8083048195789900457275421 3031143073421212671478283)
  ·
    refine ⟨4546714610131819007217425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3031143073421212671478283 4546714610131819007217425)
    ·
      refine ⟨3410035957598864255413069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4546714610131819007217425 3410035957598864255413069)
      ·
        refine ⟨1278763484099574095779901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3410035957598864255413069 1278763484099574095779901)
        ·
          refine ⟨479536306537340285917463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1278763484099574095779901 479536306537340285917463)
          ·
            refine ⟨719304459806010428876195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479536306537340285917463 719304459806010428876195)
            ·
              refine ⟨1078956689709015643314293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719304459806010428876195 1078956689709015643314293)
              ·
                refine ⟨101152189660220216560715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1078956689709015643314293 101152189660220216560715)
                ·
                  rfl

theorem cell19_332426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_332426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332426 prefixEnd_332426 := by exact prefixLift 332426
  have htrace : WordTrace (prefixWord ++ tailWord_332426) baseStart_332426 baseEnd_332426 := by
    simpa [prefixWord, tailWord_332426, baseEnd_332426] using wordTrace_append hprefix tailTrace_332426
  have hstable : (prefixWord ++ tailWord_332426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332426).length < 2 ^ (prefixWord ++ tailWord_332426).sum := by decide
  have hdescent : baseEnd_332426 < baseStart_332426 := by decide
  rcases family_descends (prefixWord ++ tailWord_332426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332462 : List Nat := [4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_332462 : Nat := 118140960795 + 332462 * 2 ^ 59
def prefixEnd_332462 : Nat := 4983230072969 + 3 ^ 40 * 332462 * 2
def baseEnd_332462 : Nat := 101163143914182799760617

theorem tailTrace_332462 : CollatzResearch.WordTrace tailWord_332462 prefixEnd_332462 101163143914182799760617 := by
  unfold tailWord_332462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1515735665194303604277955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8083923547702952556149093 1515735665194303604277955)
  ·
    refine ⟨2273603497791455406416933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1515735665194303604277955 2273603497791455406416933)
    ·
      refine ⟨426300655835897888703175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2273603497791455406416933 426300655835897888703175)
      ·
        refine ⟨639450983753846833054763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426300655835897888703175 639450983753846833054763)
        ·
          refine ⟨959176475630770249582145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639450983753846833054763 959176475630770249582145)
          ·
            refine ⟨719382356723077687186609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959176475630770249582145 719382356723077687186609)
            ·
              refine ⟨539536767542308265389957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719382356723077687186609 539536767542308265389957)
              ·
                refine ⟨101163143914182799760617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 539536767542308265389957 101163143914182799760617)
                ·
                  rfl

theorem cell19_332462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_332462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332462 prefixEnd_332462 := by exact prefixLift 332462
  have htrace : WordTrace (prefixWord ++ tailWord_332462) baseStart_332462 baseEnd_332462 := by
    simpa [prefixWord, tailWord_332462, baseEnd_332462] using wordTrace_append hprefix tailTrace_332462
  have hstable : (prefixWord ++ tailWord_332462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332462).length < 2 ^ (prefixWord ++ tailWord_332462).sum := by decide
  have hdescent : baseEnd_332462 < baseStart_332462 := by decide
  rcases family_descends (prefixWord ++ tailWord_332462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332540 : List Nat := [2, 2, 2, 1, 3, 3, 3, 3]
def baseStart_332540 : Nat := 118140960795 + 332540 * 2 ^ 59
def prefixEnd_332540 : Nat := 4983230072969 + 3 ^ 40 * 332540 * 2
def baseEnd_332540 : Nat := 101186878131101730027071

theorem tailTrace_332540 : CollatzResearch.WordTrace tailWord_332540 prefixEnd_332540 101186878131101730027071 := by
  unfold tailWord_332540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064365107635924077781537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8085820143514565437042049 6064365107635924077781537)
  ·
    refine ⟨4548273830726943058336153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6064365107635924077781537 4548273830726943058336153)
    ·
      refine ⟨3411205373045207293752115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4548273830726943058336153 3411205373045207293752115)
      ·
        refine ⟨5116808059567810940628173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411205373045207293752115 5116808059567810940628173)
        ·
          refine ⟨1918803022337929102735565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5116808059567810940628173 1918803022337929102735565)
          ·
            refine ⟨719551133376723413525837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1918803022337929102735565 719551133376723413525837)
            ·
              refine ⟨269831675016271280072189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 719551133376723413525837 269831675016271280072189)
              ·
                refine ⟨101186878131101730027071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269831675016271280072189 101186878131101730027071)
                ·
                  rfl

theorem cell19_332540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_332540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332540 prefixEnd_332540 := by exact prefixLift 332540
  have htrace : WordTrace (prefixWord ++ tailWord_332540) baseStart_332540 baseEnd_332540 := by
    simpa [prefixWord, tailWord_332540, baseEnd_332540] using wordTrace_append hprefix tailTrace_332540
  have hstable : (prefixWord ++ tailWord_332540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332540).length < 2 ^ (prefixWord ++ tailWord_332540).sum := by decide
  have hdescent : baseEnd_332540 < baseStart_332540 := by decide
  rcases family_descends (prefixWord ++ tailWord_332540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332563 : List Nat := [1, 1, 1, 2, 1, 3, 10]
def baseStart_332563 : Nat := 118140960795 + 332563 * 2 ^ 59
def prefixEnd_332563 : Nat := 4983230072969 + 3 ^ 40 * 332563 * 2
def baseEnd_332563 : Nat := 33731292227414830505299

theorem tailTrace_332563 : CollatzResearch.WordTrace tailWord_332563 prefixEnd_332563 33731292227414830505299 := by
  unfold tailWord_332563
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129569094188523083650343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8086379396125682055766895 12129569094188523083650343)
  ·
    refine ⟨18194353641282784625475515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12129569094188523083650343 18194353641282784625475515)
    ·
      refine ⟨27291530461924176938213273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18194353641282784625475515 27291530461924176938213273)
      ·
        refine ⟨20468647846443132703659955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27291530461924176938213273 20468647846443132703659955)
        ·
          refine ⟨30702971769664699055489933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20468647846443132703659955 30702971769664699055489933)
          ·
            refine ⟨11513614413624262145808725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30702971769664699055489933 11513614413624262145808725)
            ·
              refine ⟨33731292227414830505299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11513614413624262145808725 33731292227414830505299)
              ·
                rfl

theorem cell19_332563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_332563 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332563 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332563 prefixEnd_332563 := by exact prefixLift 332563
  have htrace : WordTrace (prefixWord ++ tailWord_332563) baseStart_332563 baseEnd_332563 := by
    simpa [prefixWord, tailWord_332563, baseEnd_332563] using wordTrace_append hprefix tailTrace_332563
  have hstable : (prefixWord ++ tailWord_332563).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332563).length < 2 ^ (prefixWord ++ tailWord_332563).sum := by decide
  have hdescent : baseEnd_332563 < baseStart_332563 := by decide
  rcases family_descends (prefixWord ++ tailWord_332563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332597 : List Nat := [1, 3, 3, 1, 3, 1, 4, 3]
def baseStart_332597 : Nat := 118140960795 + 332597 * 2 ^ 59
def prefixEnd_332597 : Nat := 4983230072969 + 3 ^ 40 * 332597 * 2
def baseEnd_332597 : Nat := 101204222366542486760249

theorem tailTrace_332597 : CollatzResearch.WordTrace tailWord_332597 prefixEnd_332597 101204222366542486760249 := by
  unfold tailWord_332597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130809176065346890388045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8087206117376897926925363 12130809176065346890388045)
  ·
    refine ⟨4549053441024505083895517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12130809176065346890388045 4549053441024505083895517)
    ·
      refine ⟨1705895040384189406460819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4549053441024505083895517 1705895040384189406460819)
      ·
        refine ⟨2558842560576284109691229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705895040384189406460819 2558842560576284109691229)
        ·
          refine ⟨959565960216106541134211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2558842560576284109691229 959565960216106541134211)
          ·
            refine ⟨1439348940324159811701317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959565960216106541134211 1439348940324159811701317)
            ·
              refine ⟨269877926310779964693997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1439348940324159811701317 269877926310779964693997)
              ·
                refine ⟨101204222366542486760249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269877926310779964693997 101204222366542486760249)
                ·
                  rfl

theorem cell19_332597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_332597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332597 prefixEnd_332597 := by exact prefixLift 332597
  have htrace : WordTrace (prefixWord ++ tailWord_332597) baseStart_332597 baseEnd_332597 := by
    simpa [prefixWord, tailWord_332597, baseEnd_332597] using wordTrace_append hprefix tailTrace_332597
  have hstable : (prefixWord ++ tailWord_332597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332597).length < 2 ^ (prefixWord ++ tailWord_332597).sum := by decide
  have hdescent : baseEnd_332597 < baseStart_332597 := by decide
  rcases family_descends (prefixWord ++ tailWord_332597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332612 : List Nat := [2, 3, 4, 2, 2, 1, 5]
def baseStart_332612 : Nat := 118140960795 + 332612 * 2 ^ 59
def prefixEnd_332612 : Nat := 4983230072969 + 3 ^ 40 * 332612 * 2
def baseEnd_332612 : Nat := 33736262213008965475625

theorem tailTrace_332612 : CollatzResearch.WordTrace tailWord_332612 prefixEnd_332612 33736262213008965475625 := by
  unfold tailWord_332612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6065678135505502226092045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8087570847340669634789393 6065678135505502226092045)
  ·
    refine ⟨2274629300814563334784517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6065678135505502226092045 2274629300814563334784517)
    ·
      refine ⟨426492993902730625272097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2274629300814563334784517 426492993902730625272097)
      ·
        refine ⟨319869745427047968954073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426492993902730625272097 319869745427047968954073)
        ·
          refine ⟨239902309070285976715555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319869745427047968954073 239902309070285976715555)
          ·
            refine ⟨359853463605428965073333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239902309070285976715555 359853463605428965073333)
            ·
              refine ⟨33736262213008965475625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 359853463605428965073333 33736262213008965475625)
              ·
                rfl

theorem cell19_332612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_332612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332612 prefixEnd_332612 := by exact prefixLift 332612
  have htrace : WordTrace (prefixWord ++ tailWord_332612) baseStart_332612 baseEnd_332612 := by
    simpa [prefixWord, tailWord_332612, baseEnd_332612] using wordTrace_append hprefix tailTrace_332612
  have hstable : (prefixWord ++ tailWord_332612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332612).length < 2 ^ (prefixWord ++ tailWord_332612).sum := by decide
  have hdescent : baseEnd_332612 < baseStart_332612 := by decide
  rcases family_descends (prefixWord ++ tailWord_332612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332677 : List Nat := [1, 3, 1, 1, 3, 10]
def baseStart_332677 : Nat := 118140960795 + 332677 * 2 ^ 59
def prefixEnd_332677 : Nat := 4983230072969 + 3 ^ 40 * 332677 * 2
def baseEnd_332677 : Nat := 11247618350347333886917

theorem tailTrace_332677 : CollatzResearch.WordTrace tailWord_332677 prefixEnd_332677 11247618350347333886917 := by
  unfold tailWord_332677
  simp only [CollatzResearch.WordTrace]
  refine ⟨12133727015775520553300285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8089151343850347035533523 12133727015775520553300285)
  ·
    refine ⟨4550147630915820207487607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12133727015775520553300285 4550147630915820207487607)
    ·
      refine ⟨6825221446373730311231411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4550147630915820207487607 6825221446373730311231411)
      ·
        refine ⟨10237832169560595466847117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825221446373730311231411 10237832169560595466847117)
        ·
          refine ⟨3839187063585223300067669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10237832169560595466847117 3839187063585223300067669)
          ·
            refine ⟨11247618350347333886917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3839187063585223300067669 11247618350347333886917)
            ·
              rfl

theorem cell19_332677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 10].length) (baseStart_332677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332677 prefixEnd_332677 := by exact prefixLift 332677
  have htrace : WordTrace (prefixWord ++ tailWord_332677) baseStart_332677 baseEnd_332677 := by
    simpa [prefixWord, tailWord_332677, baseEnd_332677] using wordTrace_append hprefix tailTrace_332677
  have hstable : (prefixWord ++ tailWord_332677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332677).length < 2 ^ (prefixWord ++ tailWord_332677).sum := by decide
  have hdescent : baseEnd_332677 < baseStart_332677 := by decide
  rcases family_descends (prefixWord ++ tailWord_332677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332690 : List Nat := [3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_332690 : Nat := 118140960795 + 332690 * 2 ^ 59
def prefixEnd_332690 : Nat := 4983230072969 + 3 ^ 40 * 332690 * 2
def baseEnd_332690 : Nat := 101232520855945826693329

theorem tailTrace_332690 : CollatzResearch.WordTrace tailWord_332690 prefixEnd_332690 101232520855945826693329 := by
  unfold tailWord_332690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033550291182105943380881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8089467443152282515682349 3033550291182105943380881)
  ·
    refine ⟨2275162718386579457535661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3033550291182105943380881 2275162718386579457535661)
    ·
      refine ⟨853186019394967296575873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2275162718386579457535661 853186019394967296575873)
      ·
        refine ⟨639889514546225472431905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 853186019394967296575873 639889514546225472431905)
        ·
          refine ⟨479917135909669104323929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 639889514546225472431905 479917135909669104323929)
          ·
            refine ⟨359937851932251828242947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479917135909669104323929 359937851932251828242947)
            ·
              refine ⟨539906777898377742364421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359937851932251828242947 539906777898377742364421)
              ·
                refine ⟨101232520855945826693329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 539906777898377742364421 101232520855945826693329)
                ·
                  rfl

theorem cell19_332690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_332690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332690 prefixEnd_332690 := by exact prefixLift 332690
  have htrace : WordTrace (prefixWord ++ tailWord_332690) baseStart_332690 baseEnd_332690 := by
    simpa [prefixWord, tailWord_332690, baseEnd_332690] using wordTrace_append hprefix tailTrace_332690
  have hstable : (prefixWord ++ tailWord_332690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332690).length < 2 ^ (prefixWord ++ tailWord_332690).sum := by decide
  have hdescent : baseEnd_332690 < baseStart_332690 := by decide
  rcases family_descends (prefixWord ++ tailWord_332690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332713 : List Nat := [1, 2, 1, 1, 1, 1, 9, 3]
def baseStart_332713 : Nat := 118140960795 + 332713 * 2 ^ 59
def prefixEnd_332713 : Nat := 4983230072969 + 3 ^ 40 * 332713 * 2
def baseEnd_332713 : Nat := 101239519407088588182155

theorem tailTrace_332713 : CollatzResearch.WordTrace tailWord_332713 prefixEnd_332713 101239519407088588182155 := by
  unfold tailWord_332713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12135040043645098701610793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8090026695763399134407195 12135040043645098701610793)
  ·
    refine ⟨9101280032733824026208095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12135040043645098701610793 9101280032733824026208095)
    ·
      refine ⟨13651920049100736039312143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9101280032733824026208095 13651920049100736039312143)
      ·
        refine ⟨20477880073651104058968215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13651920049100736039312143 20477880073651104058968215)
        ·
          refine ⟨30716820110476656088452323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20477880073651104058968215 30716820110476656088452323)
          ·
            refine ⟨46075230165714984132678485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30716820110476656088452323 46075230165714984132678485)
            ·
              refine ⟨269972051752236235152413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 46075230165714984132678485 269972051752236235152413)
              ·
                refine ⟨101239519407088588182155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269972051752236235152413 101239519407088588182155)
                ·
                  rfl

theorem cell19_332713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_332713 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332713 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332713 prefixEnd_332713 := by exact prefixLift 332713
  have htrace : WordTrace (prefixWord ++ tailWord_332713) baseStart_332713 baseEnd_332713 := by
    simpa [prefixWord, tailWord_332713, baseEnd_332713] using wordTrace_append hprefix tailTrace_332713
  have hstable : (prefixWord ++ tailWord_332713).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332713).length < 2 ^ (prefixWord ++ tailWord_332713).sum := by decide
  have hdescent : baseEnd_332713 < baseStart_332713 := by decide
  rcases family_descends (prefixWord ++ tailWord_332713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332726 : List Nat := [5, 1, 4, 1, 1, 1, 6]
def baseStart_332726 : Nat := 118140960795 + 332726 * 2 ^ 59
def prefixEnd_332726 : Nat := 4983230072969 + 3 ^ 40 * 332726 * 2
def baseEnd_332726 : Nat := 33747825036636136631077

theorem tailTrace_332726 : CollatzResearch.WordTrace tailWord_332726 prefixEnd_332726 33747825036636136631077 := by
  unfold tailWord_332726
  simp only [CollatzResearch.WordTrace]
  refine ⟨758469637037375120114627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8090342795065334614556021 758469637037375120114627)
  ·
    refine ⟨1137704455556062680171941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758469637037375120114627 1137704455556062680171941)
    ·
      refine ⟨213319585416761752532239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1137704455556062680171941 213319585416761752532239)
      ·
        refine ⟨319979378125142628798359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213319585416761752532239 319979378125142628798359)
        ·
          refine ⟨479969067187713943197539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319979378125142628798359 479969067187713943197539)
          ·
            refine ⟨719953600781570914796309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479969067187713943197539 719953600781570914796309)
            ·
              refine ⟨33747825036636136631077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 719953600781570914796309 33747825036636136631077)
              ·
                rfl

theorem cell19_332726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_332726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332726 prefixEnd_332726 := by exact prefixLift 332726
  have htrace : WordTrace (prefixWord ++ tailWord_332726) baseStart_332726 baseEnd_332726 := by
    simpa [prefixWord, tailWord_332726, baseEnd_332726] using wordTrace_append hprefix tailTrace_332726
  have hstable : (prefixWord ++ tailWord_332726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332726).length < 2 ^ (prefixWord ++ tailWord_332726).sum := by decide
  have hdescent : baseEnd_332726 < baseStart_332726 := by decide
  rcases family_descends (prefixWord ++ tailWord_332726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332753 : List Nat := [1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_332753 : Nat := 118140960795 + 332753 * 2 ^ 59
def prefixEnd_332753 : Nat := 4983230072969 + 3 ^ 40 * 332753 * 2
def baseEnd_332753 : Nat := 101251690800380347293157

theorem tailTrace_332753 : CollatzResearch.WordTrace tailWord_332753 prefixEnd_332753 101251690800380347293157 := by
  unfold tailWord_332753
  simp only [CollatzResearch.WordTrace]
  refine ⟨12136498963500185533066913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8090999309000123688711275 12136498963500185533066913)
  ·
    refine ⟨9102374222625139149800185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12136498963500185533066913 9102374222625139149800185)
    ·
      refine ⟨6826780666968854362350139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9102374222625139149800185 6826780666968854362350139)
      ·
        refine ⟨10240171000453281543525209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6826780666968854362350139 10240171000453281543525209)
        ·
          refine ⟨7680128250339961157643907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10240171000453281543525209 7680128250339961157643907)
          ·
            refine ⟨11520192375509941736465861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680128250339961157643907 11520192375509941736465861)
            ·
              refine ⟨2160036070408114075587349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11520192375509941736465861 2160036070408114075587349)
              ·
                refine ⟨101251690800380347293157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2160036070408114075587349 101251690800380347293157)
                ·
                  rfl

theorem cell19_332753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_332753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332753 prefixEnd_332753 := by exact prefixLift 332753
  have htrace : WordTrace (prefixWord ++ tailWord_332753) baseStart_332753 baseEnd_332753 := by
    simpa [prefixWord, tailWord_332753, baseEnd_332753] using wordTrace_append hprefix tailTrace_332753
  have hstable : (prefixWord ++ tailWord_332753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332753).length < 2 ^ (prefixWord ++ tailWord_332753).sum := by decide
  have hdescent : baseEnd_332753 < baseStart_332753 := by decide
  rcases family_descends (prefixWord ++ tailWord_332753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332808 : List Nat := [2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_332808 : Nat := 118140960795 + 332808 * 2 ^ 59
def prefixEnd_332808 : Nat := 4983230072969 + 3 ^ 40 * 332808 * 2
def baseEnd_332808 : Nat := 101268426466156516070785

theorem tailTrace_332808 : CollatzResearch.WordTrace tailWord_332808 prefixEnd_332808 101268426466156516070785 := by
  unfold tailWord_332808
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069252489150464963159539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8092336652200619950879385 6069252489150464963159539)
  ·
    refine ⟨9103878733725697444739309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6069252489150464963159539 9103878733725697444739309)
    ·
      refine ⟨3413954525147136541777241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9103878733725697444739309 3413954525147136541777241)
      ·
        refine ⟨2560465893860352406332931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3413954525147136541777241 2560465893860352406332931)
        ·
          refine ⟨3840698840790528609499397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560465893860352406332931 3840698840790528609499397)
          ·
            refine ⟨720131032648224114281137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3840698840790528609499397 720131032648224114281137)
            ·
              refine ⟨540098274486168085710853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720131032648224114281137 540098274486168085710853)
              ·
                refine ⟨101268426466156516070785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540098274486168085710853 101268426466156516070785)
                ·
                  rfl

theorem cell19_332808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_332808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332808 prefixEnd_332808 := by exact prefixLift 332808
  have htrace : WordTrace (prefixWord ++ tailWord_332808) baseStart_332808 baseEnd_332808 := by
    simpa [prefixWord, tailWord_332808, baseEnd_332808] using wordTrace_append hprefix tailTrace_332808
  have hstable : (prefixWord ++ tailWord_332808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332808).length < 2 ^ (prefixWord ++ tailWord_332808).sum := by decide
  have hdescent : baseEnd_332808 < baseStart_332808 := by decide
  rcases family_descends (prefixWord ++ tailWord_332808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332882 : List Nat := [3, 2, 2, 1, 3, 2, 3, 3]
def baseStart_332882 : Nat := 118140960795 + 332882 * 2 ^ 59
def prefixEnd_332882 : Nat := 4983230072969 + 3 ^ 40 * 332882 * 2
def baseEnd_332882 : Nat := 101290943543746270426139

theorem tailTrace_332882 : CollatzResearch.WordTrace tailWord_332882 prefixEnd_332882 101290943543746270426139 := by
  unfold tailWord_332882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035300995008210141128225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8094135986688560376341933 3035300995008210141128225)
  ·
    refine ⟨2276475746256157605846169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3035300995008210141128225 2276475746256157605846169)
    ·
      refine ⟨1707356809692118204384627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2276475746256157605846169 1707356809692118204384627)
      ·
        refine ⟨2561035214538177306576941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707356809692118204384627 2561035214538177306576941)
        ·
          refine ⟨960388205451816489966353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2561035214538177306576941 960388205451816489966353)
          ·
            refine ⟨720291154088862367474765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960388205451816489966353 720291154088862367474765)
            ·
              refine ⟨270109182783323387803037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 720291154088862367474765 270109182783323387803037)
              ·
                refine ⟨101290943543746270426139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270109182783323387803037 101290943543746270426139)
                ·
                  rfl

theorem cell19_332882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_332882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332882 prefixEnd_332882 := by exact prefixLift 332882
  have htrace : WordTrace (prefixWord ++ tailWord_332882) baseStart_332882 baseEnd_332882 := by
    simpa [prefixWord, tailWord_332882, baseEnd_332882] using wordTrace_append hprefix tailTrace_332882
  have hstable : (prefixWord ++ tailWord_332882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332882).length < 2 ^ (prefixWord ++ tailWord_332882).sum := by decide
  have hdescent : baseEnd_332882 < baseStart_332882 := by decide
  rcases family_descends (prefixWord ++ tailWord_332882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332905 : List Nat := [1, 2, 1, 1, 1, 7, 6]
def baseStart_332905 : Nat := 118140960795 + 332905 * 2 ^ 59
def prefixEnd_332905 : Nat := 4983230072969 + 3 ^ 40 * 332905 * 2
def baseEnd_332905 : Nat := 33765980698296343971655

theorem tailTrace_332905 : CollatzResearch.WordTrace tailWord_332905 prefixEnd_332905 33765980698296343971655 := by
  unfold tailWord_332905
  simp only [CollatzResearch.WordTrace]
  refine ⟨12142042858949515492600169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8094695239299676995066779 12142042858949515492600169)
  ·
    refine ⟨9106532144212136619450127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12142042858949515492600169 9106532144212136619450127)
    ·
      refine ⟨13659798216318204929175191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9106532144212136619450127 13659798216318204929175191)
      ·
        refine ⟨20489697324477307393762787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13659798216318204929175191 20489697324477307393762787)
        ·
          refine ⟨30734545986715961090644181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20489697324477307393762787 30734545986715961090644181)
          ·
            refine ⟨720340921563655338061973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 30734545986715961090644181 720340921563655338061973)
            ·
              refine ⟨33765980698296343971655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 720340921563655338061973 33765980698296343971655)
              ·
                rfl

theorem cell19_332905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_332905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332905 prefixEnd_332905 := by exact prefixLift 332905
  have htrace : WordTrace (prefixWord ++ tailWord_332905) baseStart_332905 baseEnd_332905 := by
    simpa [prefixWord, tailWord_332905, baseEnd_332905] using wordTrace_append hprefix tailTrace_332905
  have hstable : (prefixWord ++ tailWord_332905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332905).length < 2 ^ (prefixWord ++ tailWord_332905).sum := by decide
  have hdescent : baseEnd_332905 < baseStart_332905 := by decide
  rcases family_descends (prefixWord ++ tailWord_332905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332924 : List Nat := [2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_332924 : Nat := 118140960795 + 332924 * 2 ^ 59
def prefixEnd_332924 : Nat := 4983230072969 + 3 ^ 40 * 332924 * 2
def baseEnd_332924 : Nat := 101303723506702617492691

theorem tailTrace_332924 : CollatzResearch.WordTrace tailWord_332924 prefixEnd_332924 101303723506702617492691 := by
  unfold tailWord_332924
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071367922940340868770913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8095157230587121158361217 6071367922940340868770913)
  ·
    refine ⟨4553525942205255651578185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6071367922940340868770913 4553525942205255651578185)
    ·
      refine ⟨3415144456653941738683639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4553525942205255651578185 3415144456653941738683639)
      ·
        refine ⟨5122716684980912608025459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415144456653941738683639 5122716684980912608025459)
        ·
          refine ⟨7684075027471368912038189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122716684980912608025459 7684075027471368912038189)
          ·
            refine ⟨2881528135301763342014321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7684075027471368912038189 2881528135301763342014321)
            ·
              refine ⟨2161146101476322506510741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881528135301763342014321 2161146101476322506510741)
              ·
                refine ⟨101303723506702617492691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2161146101476322506510741 101303723506702617492691)
                ·
                  rfl

theorem cell19_332924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_332924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332924 prefixEnd_332924 := by exact prefixLift 332924
  have htrace : WordTrace (prefixWord ++ tailWord_332924) baseStart_332924 baseEnd_332924 := by
    simpa [prefixWord, tailWord_332924, baseEnd_332924] using wordTrace_append hprefix tailTrace_332924
  have hstable : (prefixWord ++ tailWord_332924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332924).length < 2 ^ (prefixWord ++ tailWord_332924).sum := by decide
  have hdescent : baseEnd_332924 < baseStart_332924 := by decide
  rcases family_descends (prefixWord ++ tailWord_332924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332958 : List Nat := [4, 3, 1, 1, 2, 3, 5]
def baseStart_332958 : Nat := 118140960795 + 332958 * 2 ^ 59
def prefixEnd_332958 : Nat := 4983230072969 + 3 ^ 40 * 332958 * 2
def baseEnd_332958 : Nat := 33771356397000204245681

theorem tailTrace_332958 : CollatzResearch.WordTrace tailWord_332958 prefixEnd_332958 33771356397000204245681 := by
  unfold tailWord_332958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517996990969688193034941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8095983951838337029519685 1517996990969688193034941)
  ·
    refine ⟨569248871613633072388103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1517996990969688193034941 569248871613633072388103)
    ·
      refine ⟨853873307420449608582155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569248871613633072388103 853873307420449608582155)
      ·
        refine ⟨1280809961130674412873233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853873307420449608582155 1280809961130674412873233)
        ·
          refine ⟨960607470848005809654925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1280809961130674412873233 960607470848005809654925)
          ·
            refine ⟨360227801568002178620597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960607470848005809654925 360227801568002178620597)
            ·
              refine ⟨33771356397000204245681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 360227801568002178620597 33771356397000204245681)
              ·
                rfl

theorem cell19_332958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_332958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_332958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_332958 prefixEnd_332958 := by exact prefixLift 332958
  have htrace : WordTrace (prefixWord ++ tailWord_332958) baseStart_332958 baseEnd_332958 := by
    simpa [prefixWord, tailWord_332958, baseEnd_332958] using wordTrace_append hprefix tailTrace_332958
  have hstable : (prefixWord ++ tailWord_332958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332958).length < 2 ^ (prefixWord ++ tailWord_332958).sum := by decide
  have hdescent : baseEnd_332958 < baseStart_332958 := by decide
  rcases family_descends (prefixWord ++ tailWord_332958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333000 : List Nat := [2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_333000 : Nat := 118140960795 + 333000 * 2 ^ 59
def prefixEnd_333000 : Nat := 4983230072969 + 3 ^ 40 * 333000 * 2
def baseEnd_333000 : Nat := 101326849153956959803595

theorem tailTrace_333000 : CollatzResearch.WordTrace tailWord_333000 prefixEnd_333000 101326849153956959803595 := by
  unfold tailWord_333000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6072753896802673358654227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8097005195736897811538969 6072753896802673358654227)
  ·
    refine ⟨9109130845204010037981341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6072753896802673358654227 9109130845204010037981341)
    ·
      refine ⟨3415924066951503764243003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9109130845204010037981341 3415924066951503764243003)
      ·
        refine ⟨5123886100427255646364505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415924066951503764243003 5123886100427255646364505)
        ·
          refine ⟨3842914575320441734773379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5123886100427255646364505 3842914575320441734773379)
          ·
            refine ⟨5764371862980662602160069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842914575320441734773379 5764371862980662602160069)
            ·
              refine ⟨1080819724308874237905013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5764371862980662602160069 1080819724308874237905013)
              ·
                refine ⟨101326849153956959803595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1080819724308874237905013 101326849153956959803595)
                ·
                  rfl

theorem cell19_333000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_333000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333000 prefixEnd_333000 := by exact prefixLift 333000
  have htrace : WordTrace (prefixWord ++ tailWord_333000) baseStart_333000 baseEnd_333000 := by
    simpa [prefixWord, tailWord_333000, baseEnd_333000] using wordTrace_append hprefix tailTrace_333000
  have hstable : (prefixWord ++ tailWord_333000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333000).length < 2 ^ (prefixWord ++ tailWord_333000).sum := by decide
  have hdescent : baseEnd_333000 < baseStart_333000 := by decide
  rcases family_descends (prefixWord ++ tailWord_333000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333036 : List Nat := [2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_333036 : Nat := 118140960795 + 333036 * 2 ^ 59
def prefixEnd_333036 : Nat := 4983230072969 + 3 ^ 40 * 333036 * 2
def baseEnd_333036 : Nat := 101337803407919543003497

theorem tailTrace_333036 : CollatzResearch.WordTrace tailWord_333036 prefixEnd_333036 101337803407919543003497 := by
  unfold tailWord_333036
  simp only [CollatzResearch.WordTrace]
  refine ⟨6073410410737462432809481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8097880547649949910412641 6073410410737462432809481)
  ·
    refine ⟨4555057808053096824607111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6073410410737462432809481 4555057808053096824607111)
    ·
      refine ⟨6832586712079645236910667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555057808053096824607111 6832586712079645236910667)
      ·
        refine ⟨10248880068119467855366001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6832586712079645236910667 10248880068119467855366001)
        ·
          refine ⟨7686660051089600891524501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10248880068119467855366001 7686660051089600891524501)
          ·
            refine ⟨360312189894825041790211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7686660051089600891524501 360312189894825041790211)
            ·
              refine ⟨540468284842237562685317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360312189894825041790211 540468284842237562685317)
              ·
                refine ⟨101337803407919543003497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540468284842237562685317 101337803407919543003497)
                ·
                  rfl

theorem cell19_333036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_333036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333036 prefixEnd_333036 := by exact prefixLift 333036
  have htrace : WordTrace (prefixWord ++ tailWord_333036) baseStart_333036 baseEnd_333036 := by
    simpa [prefixWord, tailWord_333036, baseEnd_333036] using wordTrace_append hprefix tailTrace_333036
  have hstable : (prefixWord ++ tailWord_333036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333036).length < 2 ^ (prefixWord ++ tailWord_333036).sum := by decide
  have hdescent : baseEnd_333036 < baseStart_333036 := by decide
  rcases family_descends (prefixWord ++ tailWord_333036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333055 : List Nat := [1, 1, 2, 2, 1, 6, 3, 3]
def baseStart_333055 : Nat := 118140960795 + 333055 * 2 ^ 59
def prefixEnd_333055 : Nat := 4983230072969 + 3 ^ 40 * 333055 * 2
def baseEnd_333055 : Nat := 101343584819733128581223

theorem tailTrace_333055 : CollatzResearch.WordTrace tailWord_333055 prefixEnd_333055 101343584819733128581223 := by
  unfold tailWord_333055
  simp only [CollatzResearch.WordTrace]
  refine ⟨12147513808406091110560619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8098342538937394073707079 12147513808406091110560619)
  ·
    refine ⟨18221270712609136665840929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12147513808406091110560619 18221270712609136665840929)
    ·
      refine ⟨13665953034456852499380697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18221270712609136665840929 13665953034456852499380697)
      ·
        refine ⟨10249464775842639374535523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13665953034456852499380697 10249464775842639374535523)
        ·
          refine ⟨15374197163763959061803285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10249464775842639374535523 15374197163763959061803285)
          ·
            refine ⟨720665492051435581022029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15374197163763959061803285 720665492051435581022029)
            ·
              refine ⟨270249559519288342883261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 720665492051435581022029 270249559519288342883261)
              ·
                refine ⟨101343584819733128581223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270249559519288342883261 101343584819733128581223)
                ·
                  rfl

theorem cell19_333055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_333055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333055 prefixEnd_333055 := by exact prefixLift 333055
  have htrace : WordTrace (prefixWord ++ tailWord_333055) baseStart_333055 baseEnd_333055 := by
    simpa [prefixWord, tailWord_333055, baseEnd_333055] using wordTrace_append hprefix tailTrace_333055
  have hstable : (prefixWord ++ tailWord_333055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333055).length < 2 ^ (prefixWord ++ tailWord_333055).sum := by decide
  have hdescent : baseEnd_333055 < baseStart_333055 := by decide
  rcases family_descends (prefixWord ++ tailWord_333055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333114 : List Nat := [3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_333114 : Nat := 118140960795 + 333114 * 2 ^ 59
def prefixEnd_333114 : Nat := 4983230072969 + 3 ^ 40 * 333114 * 2
def baseEnd_333114 : Nat := 101361537624838473269951

theorem tailTrace_333114 : CollatzResearch.WordTrace tailWord_333114 prefixEnd_333114 101361537624838473269951 := by
  unfold tailWord_333114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037416428798086046739599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8099777143461562791305597 3037416428798086046739599)
  ·
    refine ⟨4556124643197129070109399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3037416428798086046739599 4556124643197129070109399)
    ·
      refine ⟨6834186964795693605164099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556124643197129070109399 6834186964795693605164099)
      ·
        refine ⟨10251280447193540407746149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6834186964795693605164099 10251280447193540407746149)
        ·
          refine ⟨1922115083848788826452403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10251280447193540407746149 1922115083848788826452403)
          ·
            refine ⟨2883172625773183239678605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922115083848788826452403 2883172625773183239678605)
            ·
              refine ⟨1081189734664943714879477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2883172625773183239678605 1081189734664943714879477)
              ·
                refine ⟨101361537624838473269951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1081189734664943714879477 101361537624838473269951)
                ·
                  rfl

theorem cell19_333114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_333114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333114 prefixEnd_333114 := by exact prefixLift 333114
  have htrace : WordTrace (prefixWord ++ tailWord_333114) baseStart_333114 baseEnd_333114 := by
    simpa [prefixWord, tailWord_333114, baseEnd_333114] using wordTrace_append hprefix tailTrace_333114
  have hstable : (prefixWord ++ tailWord_333114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333114).length < 2 ^ (prefixWord ++ tailWord_333114).sum := by decide
  have hdescent : baseEnd_333114 < baseStart_333114 := by decide
  rcases family_descends (prefixWord ++ tailWord_333114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333152 : List Nat := [2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_333152 : Nat := 118140960795 + 333152 * 2 ^ 59
def prefixEnd_333152 : Nat := 4983230072969 + 3 ^ 40 * 333152 * 2
def baseEnd_333152 : Nat := 101373100448465644425403

theorem tailTrace_333152 : CollatzResearch.WordTrace tailWord_333152 prefixEnd_333152 101373100448465644425403 := by
  unfold tailWord_333152
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075525844527338338420855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8100701126036451117894473 6075525844527338338420855)
  ·
    refine ⟨9113288766791007507631283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6075525844527338338420855 9113288766791007507631283)
    ·
      refine ⟨13669933150186511261446925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9113288766791007507631283 13669933150186511261446925)
      ·
        refine ⟨5126224931319941723042597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13669933150186511261446925 5126224931319941723042597)
        ·
          refine ⟨961167174622489073070487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5126224931319941723042597 961167174622489073070487)
          ·
            refine ⟨1441750761933733609605731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961167174622489073070487 1441750761933733609605731)
            ·
              refine ⟨2162626142900600414408597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441750761933733609605731 2162626142900600414408597)
              ·
                refine ⟨101373100448465644425403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2162626142900600414408597 101373100448465644425403)
                ·
                  rfl

theorem cell19_333152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_333152 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333152 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333152 prefixEnd_333152 := by exact prefixLift 333152
  have htrace : WordTrace (prefixWord ++ tailWord_333152) baseStart_333152 baseEnd_333152 := by
    simpa [prefixWord, tailWord_333152, baseEnd_333152] using wordTrace_append hprefix tailTrace_333152
  have hstable : (prefixWord ++ tailWord_333152).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333152).length < 2 ^ (prefixWord ++ tailWord_333152).sum := by decide
  have hdescent : baseEnd_333152 < baseStart_333152 := by decide
  rcases family_descends (prefixWord ++ tailWord_333152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333209 : List Nat := [1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_333209 : Nat := 118140960795 + 333209 * 2 ^ 59
def prefixEnd_333209 : Nat := 4983230072969 + 3 ^ 40 * 333209 * 2
def baseEnd_333209 : Nat := 101390444683906401158581

theorem tailTrace_333209 : CollatzResearch.WordTrace tailWord_333209 prefixEnd_333209 101390444683906401158581 := by
  unfold tailWord_333209
  simp only [CollatzResearch.WordTrace]
  refine ⟨12153130649848175411666681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8102087099898783607777787 12153130649848175411666681)
  ·
    refine ⟨9114847987386131558750011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12153130649848175411666681 9114847987386131558750011)
    ·
      refine ⟨13672271981079197338125017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114847987386131558750011 13672271981079197338125017)
      ·
        refine ⟨10254203985809398003593763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13672271981079197338125017 10254203985809398003593763)
        ·
          refine ⟨15381305978714097005390645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10254203985809398003593763 15381305978714097005390645)
          ·
            refine ⟨1441997435504446594255373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15381305978714097005390645 1441997435504446594255373)
            ·
              refine ⟨540749038314167472845765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1441997435504446594255373 540749038314167472845765)
              ·
                refine ⟨101390444683906401158581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540749038314167472845765 101390444683906401158581)
                ·
                  rfl

theorem cell19_333209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_333209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333209 prefixEnd_333209 := by exact prefixLift 333209
  have htrace : WordTrace (prefixWord ++ tailWord_333209) baseStart_333209 baseEnd_333209 := by
    simpa [prefixWord, tailWord_333209, baseEnd_333209] using wordTrace_append hprefix tailTrace_333209
  have hstable : (prefixWord ++ tailWord_333209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333209).length < 2 ^ (prefixWord ++ tailWord_333209).sum := by decide
  have hdescent : baseEnd_333209 < baseStart_333209 := by decide
  rcases family_descends (prefixWord ++ tailWord_333209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333283 : List Nat := [1, 1, 1, 6, 2, 1, 4, 3]
def baseStart_333283 : Nat := 118140960795 + 333283 * 2 ^ 59
def prefixEnd_333283 : Nat := 4983230072969 + 3 ^ 40 * 333283 * 2
def baseEnd_333283 : Nat := 101412961761496155513935

theorem tailTrace_333283 : CollatzResearch.WordTrace tailWord_333283 prefixEnd_333283 101412961761496155513935 := by
  unfold tailWord_333283
  simp only [CollatzResearch.WordTrace]
  refine ⟨12155829651580086049860503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8103886434386724033240335 12155829651580086049860503)
  ·
    refine ⟨18233744477370129074790755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12155829651580086049860503 18233744477370129074790755)
    ·
      refine ⟨27350616716055193612186133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18233744477370129074790755 27350616716055193612186133)
      ·
        refine ⟨1282060158565087200571225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27350616716055193612186133 1282060158565087200571225)
        ·
          refine ⟨961545118923815400428419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1282060158565087200571225 961545118923815400428419)
          ·
            refine ⟨1442317678385723100642629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961545118923815400428419 1442317678385723100642629)
            ·
              refine ⟨270434564697323081370493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1442317678385723100642629 270434564697323081370493)
              ·
                refine ⟨101412961761496155513935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270434564697323081370493 101412961761496155513935)
                ·
                  rfl

theorem cell19_333283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_333283 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333283 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333283 prefixEnd_333283 := by exact prefixLift 333283
  have htrace : WordTrace (prefixWord ++ tailWord_333283) baseStart_333283 baseEnd_333283 := by
    simpa [prefixWord, tailWord_333283, baseEnd_333283] using wordTrace_append hprefix tailTrace_333283
  have hstable : (prefixWord ++ tailWord_333283).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333283).length < 2 ^ (prefixWord ++ tailWord_333283).sum := by decide
  have hdescent : baseEnd_333283 < baseStart_333283 := by decide
  rcases family_descends (prefixWord ++ tailWord_333283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333302 : List Nat := [5, 1, 1, 1, 2, 4, 5]
def baseStart_333302 : Nat := 118140960795 + 333302 * 2 ^ 59
def prefixEnd_333302 : Nat := 4983230072969 + 3 ^ 40 * 333302 * 2
def baseEnd_333302 : Nat := 33806247724436580363887

theorem tailTrace_333302 : CollatzResearch.WordTrace tailWord_333302 prefixEnd_333302 33806247724436580363887 := by
  unfold tailWord_333302
  simp only [CollatzResearch.WordTrace]
  refine ⟨759782664906953268425135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8104348425674168196534773 759782664906953268425135)
  ·
    refine ⟨1139673997360429902637703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 759782664906953268425135 1139673997360429902637703)
    ·
      refine ⟨1709510996040644853956555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1139673997360429902637703 1709510996040644853956555)
      ·
        refine ⟨2564266494060967280934833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709510996040644853956555 2564266494060967280934833)
        ·
          refine ⟨1923199870545725460701125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564266494060967280934833 1923199870545725460701125)
          ·
            refine ⟨360599975727323523881461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1923199870545725460701125 360599975727323523881461)
            ·
              refine ⟨33806247724436580363887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 360599975727323523881461 33806247724436580363887)
              ·
                rfl

theorem cell19_333302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_333302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333302 prefixEnd_333302 := by exact prefixLift 333302
  have htrace : WordTrace (prefixWord ++ tailWord_333302) baseStart_333302 baseEnd_333302 := by
    simpa [prefixWord, tailWord_333302, baseEnd_333302] using wordTrace_append hprefix tailTrace_333302
  have hstable : (prefixWord ++ tailWord_333302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333302).length < 2 ^ (prefixWord ++ tailWord_333302).sum := by decide
  have hdescent : baseEnd_333302 < baseStart_333302 := by decide
  rcases family_descends (prefixWord ++ tailWord_333302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333304 : List Nat := [2, 1, 2, 1, 1, 7, 5]
def baseStart_333304 : Nat := 118140960795 + 333304 * 2 ^ 59
def prefixEnd_333304 : Nat := 4983230072969 + 3 ^ 40 * 333304 * 2
def baseEnd_333304 : Nat := 33806450580991443015737

theorem tailTrace_333304 : CollatzResearch.WordTrace tailWord_333304 prefixEnd_333304 33806450580991443015737 := by
  unfold tailWord_333304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078297792252003318187483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8104397056336004424249977 6078297792252003318187483)
  ·
    refine ⟨9117446688378004977281225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6078297792252003318187483 9117446688378004977281225)
    ·
      refine ⟨6838085016283503732960919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9117446688378004977281225 6838085016283503732960919)
      ·
        refine ⟨10257127524425255599441379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838085016283503732960919 10257127524425255599441379)
        ·
          refine ⟨15385691286637883399162069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10257127524425255599441379 15385691286637883399162069)
          ·
            refine ⟨360602139530575392167861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15385691286637883399162069 360602139530575392167861)
            ·
              refine ⟨33806450580991443015737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 360602139530575392167861 33806450580991443015737)
              ·
                rfl

theorem cell19_333304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_333304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333304 prefixEnd_333304 := by exact prefixLift 333304
  have htrace : WordTrace (prefixWord ++ tailWord_333304) baseStart_333304 baseEnd_333304 := by
    simpa [prefixWord, tailWord_333304, baseEnd_333304] using wordTrace_append hprefix tailTrace_333304
  have hstable : (prefixWord ++ tailWord_333304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333304).length < 2 ^ (prefixWord ++ tailWord_333304).sum := by decide
  have hdescent : baseEnd_333304 < baseStart_333304 := by decide
  rcases family_descends (prefixWord ++ tailWord_333304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333363 : List Nat := [1, 1, 1, 2, 4, 10]
def baseStart_333363 : Nat := 118140960795 + 333363 * 2 ^ 59
def prefixEnd_333363 : Nat := 4983230072969 + 3 ^ 40 * 333363 * 2
def baseEnd_333363 : Nat := 11270811616453297081771

theorem tailTrace_333363 : CollatzResearch.WordTrace tailWord_333363 prefixEnd_333363 11270811616453297081771 := by
  unfold tailWord_333363
  simp only [CollatzResearch.WordTrace]
  refine ⟨12158747491290259712772743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8105831660860173141848495 12158747491290259712772743)
  ·
    refine ⟨18238121236935389569159115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12158747491290259712772743 18238121236935389569159115)
    ·
      refine ⟨27357181855403084353738673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18238121236935389569159115 27357181855403084353738673)
      ·
        refine ⟨20517886391552313265304005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27357181855403084353738673 20517886391552313265304005)
        ·
          refine ⟨3847103698416058737244501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20517886391552313265304005 3847103698416058737244501)
          ·
            refine ⟨11270811616453297081771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3847103698416058737244501 11270811616453297081771)
            ·
              rfl

theorem cell19_333363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 10].length) (baseStart_333363 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333363 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333363 prefixEnd_333363 := by exact prefixLift 333363
  have htrace : WordTrace (prefixWord ++ tailWord_333363) baseStart_333363 baseEnd_333363 := by
    simpa [prefixWord, tailWord_333363, baseEnd_333363] using wordTrace_append hprefix tailTrace_333363
  have hstable : (prefixWord ++ tailWord_333363).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333363).length < 2 ^ (prefixWord ++ tailWord_333363).sum := by decide
  have hdescent : baseEnd_333363 < baseStart_333363 := by decide
  rcases family_descends (prefixWord ++ tailWord_333363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333401 : List Nat := [1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_333401 : Nat := 118140960795 + 333401 * 2 ^ 59
def prefixEnd_333401 : Nat := 4983230072969 + 3 ^ 40 * 333401 * 2
def baseEnd_333401 : Nat := 101448867371706844891391

theorem tailTrace_333401 : CollatzResearch.WordTrace tailWord_333401 prefixEnd_333401 101448867371706844891391 := by
  unfold tailWord_333401
  simp only [CollatzResearch.WordTrace]
  refine ⟨12160133465152592202656057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8106755643435061468437371 12160133465152592202656057)
  ·
    refine ⟨9120100098864444151992043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12160133465152592202656057 9120100098864444151992043)
    ·
      refine ⟨13680150148296666227988065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9120100098864444151992043 13680150148296666227988065)
      ·
        refine ⟨10260112611222499670991049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13680150148296666227988065 10260112611222499670991049)
        ·
          refine ⟨7695084458416874753243287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10260112611222499670991049 7695084458416874753243287)
          ·
            refine ⟨11542626687625312129864931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7695084458416874753243287 11542626687625312129864931)
            ·
              refine ⟨17313940031437968194797397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11542626687625312129864931 17313940031437968194797397)
              ·
                refine ⟨101448867371706844891391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17313940031437968194797397 101448867371706844891391)
                ·
                  rfl

theorem cell19_333401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_333401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333401 prefixEnd_333401 := by exact prefixLift 333401
  have htrace : WordTrace (prefixWord ++ tailWord_333401) baseStart_333401 baseEnd_333401 := by
    simpa [prefixWord, tailWord_333401, baseEnd_333401] using wordTrace_append hprefix tailTrace_333401
  have hstable : (prefixWord ++ tailWord_333401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333401).length < 2 ^ (prefixWord ++ tailWord_333401).sum := by decide
  have hdescent : baseEnd_333401 < baseStart_333401 := by decide
  rcases family_descends (prefixWord ++ tailWord_333401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333418 : List Nat := [3, 1, 3, 2, 1, 3, 6]
def baseStart_333418 : Nat := 118140960795 + 333418 * 2 ^ 59
def prefixEnd_333418 : Nat := 4983230072969 + 3 ^ 40 * 333418 * 2
def baseEnd_333418 : Nat := 33818013404618614171189

theorem tailTrace_333418 : CollatzResearch.WordTrace tailWord_333418 prefixEnd_333418 33818013404618614171189 := by
  unfold tailWord_333418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3040188376522751026506227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8107169004060669404016605 3040188376522751026506227)
  ·
    refine ⟨4560282564784126539759341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3040188376522751026506227 4560282564784126539759341)
    ·
      refine ⟨1710105961794047452409753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4560282564784126539759341 1710105961794047452409753)
      ·
        refine ⟨1282579471345535589307315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1710105961794047452409753 1282579471345535589307315)
        ·
          refine ⟨1923869207018303383960973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282579471345535589307315 1923869207018303383960973)
          ·
            refine ⟨721450952631863768985365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1923869207018303383960973 721450952631863768985365)
            ·
              refine ⟨33818013404618614171189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 721450952631863768985365 33818013404618614171189)
              ·
                rfl

theorem cell19_333418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_333418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333418 prefixEnd_333418 := by exact prefixLift 333418
  have htrace : WordTrace (prefixWord ++ tailWord_333418) baseStart_333418 baseEnd_333418 := by
    simpa [prefixWord, tailWord_333418, baseEnd_333418] using wordTrace_append hprefix tailTrace_333418
  have hstable : (prefixWord ++ tailWord_333418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333418).length < 2 ^ (prefixWord ++ tailWord_333418).sum := by decide
  have hdescent : baseEnd_333418 < baseStart_333418 := by decide
  rcases family_descends (prefixWord ++ tailWord_333418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333454 : List Nat := [4, 1, 1, 3, 1, 2, 4, 3]
def baseStart_333454 : Nat := 118140960795 + 333454 * 2 ^ 59
def prefixEnd_333454 : Nat := 4983230072969 + 3 ^ 40 * 333454 * 2
def baseEnd_333454 : Nat := 101464994467818425713469

theorem tailTrace_333454 : CollatzResearch.WordTrace tailWord_333454 prefixEnd_333454 101464994467818425713469 := by
  unfold tailWord_333454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520258316745072781791927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8108044355973721502890277 1520258316745072781791927)
  ·
    refine ⟨2280387475117609172687891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1520258316745072781791927 2280387475117609172687891)
    ·
      refine ⟨3420581212676413759031837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2280387475117609172687891 3420581212676413759031837)
      ·
        refine ⟨1282717954753655159636939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3420581212676413759031837 1282717954753655159636939)
        ·
          refine ⟨1924076932130482739455409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282717954753655159636939 1924076932130482739455409)
          ·
            refine ⟨1443057699097862054591557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1924076932130482739455409 1443057699097862054591557)
            ·
              refine ⟨270573318580849135235917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1443057699097862054591557 270573318580849135235917)
              ·
                refine ⟨101464994467818425713469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270573318580849135235917 101464994467818425713469)
                ·
                  rfl

theorem cell19_333454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_333454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333454 prefixEnd_333454 := by exact prefixLift 333454
  have htrace : WordTrace (prefixWord ++ tailWord_333454) baseStart_333454 baseEnd_333454 := by
    simpa [prefixWord, tailWord_333454, baseEnd_333454] using wordTrace_append hprefix tailTrace_333454
  have hstable : (prefixWord ++ tailWord_333454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333454).length < 2 ^ (prefixWord ++ tailWord_333454).sum := by decide
  have hdescent : baseEnd_333454 < baseStart_333454 := by decide
  rcases family_descends (prefixWord ++ tailWord_333454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333471 : List Nat := [1, 1, 2, 7, 2, 1, 5]
def baseStart_333471 : Nat := 118140960795 + 333471 * 2 ^ 59
def prefixEnd_333471 : Nat := 4983230072969 + 3 ^ 40 * 333471 * 2
def baseEnd_333471 : Nat := 33823389103322474445215

theorem tailTrace_333471 : CollatzResearch.WordTrace tailWord_333471 prefixEnd_333471 33823389103322474445215 := by
  unfold tailWord_333471
  simp only [CollatzResearch.WordTrace]
  refine ⟨12162686574898994157704267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8108457716599329438469511 12162686574898994157704267)
  ·
    refine ⟨18244029862348491236556401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12162686574898994157704267 18244029862348491236556401)
    ·
      refine ⟨13683022396761368427417301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18244029862348491236556401 13683022396761368427417301)
      ·
        refine ⟨320695837424094572517593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13683022396761368427417301 320695837424094572517593)
        ·
          refine ⟨240521878068070929388195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320695837424094572517593 240521878068070929388195)
          ·
            refine ⟨360782817102106394082293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240521878068070929388195 360782817102106394082293)
            ·
              refine ⟨33823389103322474445215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 360782817102106394082293 33823389103322474445215)
              ·
                rfl

theorem cell19_333471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_333471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333471 prefixEnd_333471 := by exact prefixLift 333471
  have htrace : WordTrace (prefixWord ++ tailWord_333471) baseStart_333471 baseEnd_333471 := by
    simpa [prefixWord, tailWord_333471, baseEnd_333471] using wordTrace_append hprefix tailTrace_333471
  have hstable : (prefixWord ++ tailWord_333471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333471).length < 2 ^ (prefixWord ++ tailWord_333471).sum := by decide
  have hdescent : baseEnd_333471 < baseStart_333471 := by decide
  rcases family_descends (prefixWord ++ tailWord_333471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333477 : List Nat := [1, 3, 1, 2, 1, 2, 9]
def baseStart_333477 : Nat := 118140960795 + 333477 * 2 ^ 59
def prefixEnd_333477 : Nat := 4983230072969 + 3 ^ 40 * 333477 * 2
def baseEnd_333477 : Nat := 33823997672987062400765

theorem tailTrace_333477 : CollatzResearch.WordTrace tailWord_333477 prefixEnd_333477 33823997672987062400765 := by
  unfold tailWord_333477
  simp only [CollatzResearch.WordTrace]
  refine ⟨12162905412877257182422685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8108603608584838121615123 12162905412877257182422685)
  ·
    refine ⟨4561089529828971443408507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12162905412877257182422685 4561089529828971443408507)
    ·
      refine ⟨6841634294743457165112761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4561089529828971443408507 6841634294743457165112761)
      ·
        refine ⟨5131225721057592873834571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6841634294743457165112761 5131225721057592873834571)
        ·
          refine ⟨7696838581586389310751857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5131225721057592873834571 7696838581586389310751857)
          ·
            refine ⟨5772628936189791983063893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7696838581586389310751857 5772628936189791983063893)
            ·
              refine ⟨33823997672987062400765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5772628936189791983063893 33823997672987062400765)
              ·
                rfl

theorem cell19_333477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_333477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333477 prefixEnd_333477 := by exact prefixLift 333477
  have htrace : WordTrace (prefixWord ++ tailWord_333477) baseStart_333477 baseEnd_333477 := by
    simpa [prefixWord, tailWord_333477, baseEnd_333477] using wordTrace_append hprefix tailTrace_333477
  have hstable : (prefixWord ++ tailWord_333477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333477).length < 2 ^ (prefixWord ++ tailWord_333477).sum := by decide
  have hdescent : baseEnd_333477 < baseStart_333477 := by decide
  rcases family_descends (prefixWord ++ tailWord_333477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333532 : List Nat := [2, 2, 5, 1, 9]
def baseStart_333532 : Nat := 118140960795 + 333532 * 2 ^ 59
def prefixEnd_333532 : Nat := 4983230072969 + 3 ^ 40 * 333532 * 2
def baseEnd_333532 : Nat := 3758841803138420591849

theorem tailTrace_333532 : CollatzResearch.WordTrace tailWord_333532 prefixEnd_333532 3758841803138420591849 := by
  unfold tailWord_333532
  simp only [CollatzResearch.WordTrace]
  refine ⟨6082455713839000787837425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8109940951785334383783233 6082455713839000787837425)
  ·
    refine ⟨4561841785379250590878069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6082455713839000787837425 4561841785379250590878069)
    ·
      refine ⟨427672667379304742894819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4561841785379250590878069 427672667379304742894819)
      ·
        refine ⟨641509001068957114342229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427672667379304742894819 641509001068957114342229)
        ·
          refine ⟨3758841803138420591849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 641509001068957114342229 3758841803138420591849)
          ·
            rfl

theorem cell19_333532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 9].length) (baseStart_333532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333532 prefixEnd_333532 := by exact prefixLift 333532
  have htrace : WordTrace (prefixWord ++ tailWord_333532) baseStart_333532 baseEnd_333532 := by
    simpa [prefixWord, tailWord_333532, baseEnd_333532] using wordTrace_append hprefix tailTrace_333532
  have hstable : (prefixWord ++ tailWord_333532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333532).length < 2 ^ (prefixWord ++ tailWord_333532).sum := by decide
  have hdescent : baseEnd_333532 < baseStart_333532 := by decide
  rcases family_descends (prefixWord ++ tailWord_333532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333549 : List Nat := [1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_333549 : Nat := 118140960795 + 333549 * 2 ^ 59
def prefixEnd_333549 : Nat := 4983230072969 + 3 ^ 40 * 333549 * 2
def baseEnd_333549 : Nat := 101493901526886353602099

theorem tailTrace_333549 : CollatzResearch.WordTrace tailWord_333549 prefixEnd_333549 101493901526886353602099 := by
  unfold tailWord_333549
  simp only [CollatzResearch.WordTrace]
  refine ⟨12165531468616413479043701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8110354312410942319362467 12165531468616413479043701)
  ·
    refine ⟨1140518575182788763660347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12165531468616413479043701 1140518575182788763660347)
    ·
      refine ⟨1710777862774183145490521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1140518575182788763660347 1710777862774183145490521)
      ·
        refine ⟨1283083397080637359117891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1710777862774183145490521 1283083397080637359117891)
        ·
          refine ⟨1924625095620956038676837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283083397080637359117891 1924625095620956038676837)
          ·
            refine ⟨360867205428929257251907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1924625095620956038676837 360867205428929257251907)
            ·
              refine ⟨541300808143393885877861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360867205428929257251907 541300808143393885877861)
              ·
                refine ⟨101493901526886353602099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 541300808143393885877861 101493901526886353602099)
                ·
                  rfl

theorem cell19_333549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_333549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333549 prefixEnd_333549 := by exact prefixLift 333549
  have htrace : WordTrace (prefixWord ++ tailWord_333549) baseStart_333549 baseEnd_333549 := by
    simpa [prefixWord, tailWord_333549, baseEnd_333549] using wordTrace_append hprefix tailTrace_333549
  have hstable : (prefixWord ++ tailWord_333549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333549).length < 2 ^ (prefixWord ++ tailWord_333549).sum := by decide
  have hdescent : baseEnd_333549 < baseStart_333549 := by decide
  rcases family_descends (prefixWord ++ tailWord_333549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333566 : List Nat := [4, 2, 2, 1, 3, 1, 3, 3]
def baseStart_333566 : Nat := 118140960795 + 333566 * 2 ^ 59
def prefixEnd_333566 : Nat := 4983230072969 + 3 ^ 40 * 333566 * 2
def baseEnd_333566 : Nat := 101499074369035351224275

theorem tailTrace_333566 : CollatzResearch.WordTrace tailWord_333566 prefixEnd_333566 101499074369035351224275 := by
  unfold tailWord_333566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520768938694353172801569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8110767673036550254941701 1520768938694353172801569)
  ·
    refine ⟨1140576704020764879601177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1520768938694353172801569 1140576704020764879601177)
    ·
      refine ⟨855432528015573659700883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1140576704020764879601177 855432528015573659700883)
      ·
        refine ⟨1283148792023360489551325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855432528015573659700883 1283148792023360489551325)
        ·
          refine ⟨481180797008760183581747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1283148792023360489551325 481180797008760183581747)
          ·
            refine ⟨721771195513140275372621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481180797008760183581747 721771195513140275372621)
            ·
              refine ⟨270664198317427603264733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 721771195513140275372621 270664198317427603264733)
              ·
                refine ⟨101499074369035351224275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270664198317427603264733 101499074369035351224275)
                ·
                  rfl

theorem cell19_333566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_333566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333566 prefixEnd_333566 := by exact prefixLift 333566
  have htrace : WordTrace (prefixWord ++ tailWord_333566) baseStart_333566 baseEnd_333566 := by
    simpa [prefixWord, tailWord_333566, baseEnd_333566] using wordTrace_append hprefix tailTrace_333566
  have hstable : (prefixWord ++ tailWord_333566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333566).length < 2 ^ (prefixWord ++ tailWord_333566).sum := by decide
  have hdescent : baseEnd_333566 < baseStart_333566 := by decide
  rcases family_descends (prefixWord ++ tailWord_333566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333625 : List Nat := [1, 2, 1, 7, 1, 1, 1, 5]
def baseStart_333625 : Nat := 118140960795 + 333625 * 2 ^ 59
def prefixEnd_333625 : Nat := 4983230072969 + 3 ^ 40 * 333625 * 2
def baseEnd_333625 : Nat := 101517027174140695913003

theorem tailTrace_333625 : CollatzResearch.WordTrace tailWord_333625 prefixEnd_333625 101517027174140695913003 := by
  unfold tailWord_333625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12168303416341078458810329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8112202277560718972540219 12168303416341078458810329)
  ·
    refine ⟨9126227562255808844107747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12168303416341078458810329 9126227562255808844107747)
    ·
      refine ⟨13689341343383713266161621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9126227562255808844107747 13689341343383713266161621)
      ·
        refine ⟨320843937735555779675663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13689341343383713266161621 320843937735555779675663)
        ·
          refine ⟨481265906603333669513495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320843937735555779675663 481265906603333669513495)
          ·
            refine ⟨721898859905000504270243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481265906603333669513495 721898859905000504270243)
            ·
              refine ⟨1082848289857500756405365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721898859905000504270243 1082848289857500756405365)
              ·
                refine ⟨101517027174140695913003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1082848289857500756405365 101517027174140695913003)
                ·
                  rfl

theorem cell19_333625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_333625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333625 prefixEnd_333625 := by exact prefixLift 333625
  have htrace : WordTrace (prefixWord ++ tailWord_333625) baseStart_333625 baseEnd_333625 := by
    simpa [prefixWord, tailWord_333625, baseEnd_333625] using wordTrace_append hprefix tailTrace_333625
  have hstable : (prefixWord ++ tailWord_333625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333625).length < 2 ^ (prefixWord ++ tailWord_333625).sum := by decide
  have hdescent : baseEnd_333625 < baseStart_333625 := by decide
  rcases family_descends (prefixWord ++ tailWord_333625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333644 : List Nat := [2, 2, 1, 3, 5, 1, 5]
def baseStart_333644 : Nat := 118140960795 + 333644 * 2 ^ 59
def prefixEnd_333644 : Nat := 4983230072969 + 3 ^ 40 * 333644 * 2
def baseEnd_333644 : Nat := 33840936195318093830243

theorem tailTrace_333644 : CollatzResearch.WordTrace tailWord_333644 prefixEnd_333644 33840936195318093830243 := by
  unfold tailWord_333644
  simp only [CollatzResearch.WordTrace]
  refine ⟨6084498201636122351875993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8112664268848163135834657 6084498201636122351875993)
  ·
    refine ⟨4563373651227091763906995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6084498201636122351875993 4563373651227091763906995)
    ·
      refine ⟨6845060476840637645860493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4563373651227091763906995 6845060476840637645860493)
      ·
        refine ⟨2566897678815239117197685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6845060476840637645860493 2566897678815239117197685)
        ·
          refine ⟨240646657388928667237283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2566897678815239117197685 240646657388928667237283)
          ·
            refine ⟨360969986083393000855925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240646657388928667237283 360969986083393000855925)
            ·
              refine ⟨33840936195318093830243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 360969986083393000855925 33840936195318093830243)
              ·
                rfl

theorem cell19_333644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_333644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333644 prefixEnd_333644 := by exact prefixLift 333644
  have htrace : WordTrace (prefixWord ++ tailWord_333644) baseStart_333644 baseEnd_333644 := by
    simpa [prefixWord, tailWord_333644, baseEnd_333644] using wordTrace_append hprefix tailTrace_333644
  have hstable : (prefixWord ++ tailWord_333644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333644).length < 2 ^ (prefixWord ++ tailWord_333644).sum := by decide
  have hdescent : baseEnd_333644 < baseStart_333644 := by decide
  rcases family_descends (prefixWord ++ tailWord_333644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333703 : List Nat := [1, 1, 4, 2, 5, 6]
def baseStart_333703 : Nat := 118140960795 + 333703 * 2 ^ 59
def prefixEnd_333703 : Nat := 4983230072969 + 3 ^ 40 * 333703 * 2
def baseEnd_333703 : Nat := 11282306821228847353273

theorem tailTrace_333703 : CollatzResearch.WordTrace tailWord_333703 prefixEnd_333703 11282306821228847353273 := by
  unfold tailWord_333703
  simp only [CollatzResearch.WordTrace]
  refine ⟨12171148310058497780149763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8114098873372331853433175 12171148310058497780149763)
  ·
    refine ⟨18256722465087746670224645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12171148310058497780149763 18256722465087746670224645)
    ·
      refine ⟨3423135462203952500667121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18256722465087746670224645 3423135462203952500667121)
      ·
        refine ⟨2567351596652964375500341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3423135462203952500667121 2567351596652964375500341)
        ·
          refine ⟨240689212186215410203157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2567351596652964375500341 240689212186215410203157)
          ·
            refine ⟨11282306821228847353273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 240689212186215410203157 11282306821228847353273)
            ·
              rfl

theorem cell19_333703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 6].length) (baseStart_333703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333703 prefixEnd_333703 := by exact prefixLift 333703
  have htrace : WordTrace (prefixWord ++ tailWord_333703) baseStart_333703 baseEnd_333703 := by
    simpa [prefixWord, tailWord_333703, baseEnd_333703] using wordTrace_append hprefix tailTrace_333703
  have hstable : (prefixWord ++ tailWord_333703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333703).length < 2 ^ (prefixWord ++ tailWord_333703).sum := by decide
  have hdescent : baseEnd_333703 < baseStart_333703 := by decide
  rcases family_descends (prefixWord ++ tailWord_333703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333722 : List Nat := [3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_333722 : Nat := 118140960795 + 333722 * 2 ^ 59
def prefixEnd_333722 : Nat := 4983230072969 + 3 ^ 40 * 333722 * 2
def baseEnd_333722 : Nat := 101546542802873211757183

theorem tailTrace_333722 : CollatzResearch.WordTrace tailWord_333722 prefixEnd_333722 101546542802873211757183 := by
  unfold tailWord_333722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042960324247416006272855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8114560864659776016727613 3042960324247416006272855)
  ·
    refine ⟨4564440486371124009409283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3042960324247416006272855 4564440486371124009409283)
    ·
      refine ⟨6846660729556686014113925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4564440486371124009409283 6846660729556686014113925)
      ·
        refine ⟨1283748886791878627646361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6846660729556686014113925 1283748886791878627646361)
        ·
          refine ⟨962811665093908970734771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1283748886791878627646361 962811665093908970734771)
          ·
            refine ⟨1444217497640863456102157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962811665093908970734771 1444217497640863456102157)
            ·
              refine ⟨541581561615323796038309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1444217497640863456102157 541581561615323796038309)
              ·
                refine ⟨101546542802873211757183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 541581561615323796038309 101546542802873211757183)
                ·
                  rfl

theorem cell19_333722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_333722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333722 prefixEnd_333722 := by exact prefixLift 333722
  have htrace : WordTrace (prefixWord ++ tailWord_333722) baseStart_333722 baseEnd_333722 := by
    simpa [prefixWord, tailWord_333722, baseEnd_333722] using wordTrace_append hprefix tailTrace_333722
  have hstable : (prefixWord ++ tailWord_333722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333722).length < 2 ^ (prefixWord ++ tailWord_333722).sum := by decide
  have hdescent : baseEnd_333722 < baseStart_333722 := by decide
  rcases family_descends (prefixWord ++ tailWord_333722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333912 : List Nat := [2, 1, 2, 2, 1, 5, 3, 3]
def baseStart_333912 : Nat := 118140960795 + 333912 * 2 ^ 59
def prefixEnd_333912 : Nat := 4983230072969 + 3 ^ 40 * 333912 * 2
def baseEnd_333912 : Nat := 101604356921009067534443

theorem tailTrace_333912 : CollatzResearch.WordTrace tailWord_333912 prefixEnd_333912 101604356921009067534443 := by
  unfold tailWord_333912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089385583150663237253995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8119180777534217649671993 6089385583150663237253995)
  ·
    refine ⟨9134078374725994855880993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089385583150663237253995 9134078374725994855880993)
    ·
      refine ⟨6850558781044496141910745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9134078374725994855880993 6850558781044496141910745)
      ·
        refine ⟨5137919085783372106433059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6850558781044496141910745 5137919085783372106433059)
        ·
          refine ⟨7706878628675058159649589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5137919085783372106433059 7706878628675058159649589)
          ·
            refine ⟨722519871438286702467149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7706878628675058159649589 722519871438286702467149)
            ·
              refine ⟨270944951789357513425181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722519871438286702467149 270944951789357513425181)
              ·
                refine ⟨101604356921009067534443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270944951789357513425181 101604356921009067534443)
                ·
                  rfl

theorem cell19_333912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_333912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333912 prefixEnd_333912 := by exact prefixLift 333912
  have htrace : WordTrace (prefixWord ++ tailWord_333912) baseStart_333912 baseEnd_333912 := by
    simpa [prefixWord, tailWord_333912, baseEnd_333912] using wordTrace_append hprefix tailTrace_333912
  have hstable : (prefixWord ++ tailWord_333912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333912).length < 2 ^ (prefixWord ++ tailWord_333912).sum := by decide
  have hdescent : baseEnd_333912 < baseStart_333912 := by decide
  rcases family_descends (prefixWord ++ tailWord_333912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333933 : List Nat := [1, 5, 1, 1, 2, 1, 8]
def baseStart_333933 : Nat := 118140960795 + 333933 * 2 ^ 59
def prefixEnd_333933 : Nat := 4983230072969 + 3 ^ 40 * 333933 * 2
def baseEnd_333933 : Nat := 33870248967495747022573

theorem tailTrace_333933 : CollatzResearch.WordTrace tailWord_333933 prefixEnd_333933 33870248967495747022573 := by
  unfold tailWord_333933
  simp only [CollatzResearch.WordTrace]
  refine ⟨12179537099225247061022453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8119691399483498040681635 12179537099225247061022453)
  ·
    refine ⟨1141831603052366911970855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12179537099225247061022453 1141831603052366911970855)
    ·
      refine ⟨1712747404578550367956283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141831603052366911970855 1712747404578550367956283)
      ·
        refine ⟨2569121106867825551934425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712747404578550367956283 2569121106867825551934425)
        ·
          refine ⟨1926840830150869163950819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2569121106867825551934425 1926840830150869163950819)
          ·
            refine ⟨2890261245226303745926229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926840830150869163950819 2890261245226303745926229)
            ·
              refine ⟨33870248967495747022573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2890261245226303745926229 33870248967495747022573)
              ·
                rfl

theorem cell19_333933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_333933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333933 prefixEnd_333933 := by exact prefixLift 333933
  have htrace : WordTrace (prefixWord ++ tailWord_333933) baseStart_333933 baseEnd_333933 := by
    simpa [prefixWord, tailWord_333933, baseEnd_333933] using wordTrace_append hprefix tailTrace_333933
  have hstable : (prefixWord ++ tailWord_333933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333933).length < 2 ^ (prefixWord ++ tailWord_333933).sum := by decide
  have hdescent : baseEnd_333933 < baseStart_333933 := by decide
  rcases family_descends (prefixWord ++ tailWord_333933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333988 : List Nat := [2, 3, 1, 2, 4, 2, 5]
def baseStart_333988 : Nat := 118140960795 + 333988 * 2 ^ 59
def prefixEnd_333988 : Nat := 4983230072969 + 3 ^ 40 * 333988 * 2
def baseEnd_333988 : Nat := 33875827522754469948449

theorem tailTrace_333988 : CollatzResearch.WordTrace tailWord_333988 prefixEnd_333988 33875827522754469948449 := by
  unfold tailWord_333988
  simp only [CollatzResearch.WordTrace]
  refine ⟨6090771557012995727137309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8121028742683994302849745 6090771557012995727137309)
  ·
    refine ⟨2284039333879873397676491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6090771557012995727137309 2284039333879873397676491)
    ·
      refine ⟨3426059000819810096514737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284039333879873397676491 3426059000819810096514737)
      ·
        refine ⟨2569544250614857572386053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3426059000819810096514737 2569544250614857572386053)
        ·
          refine ⟨481789546990285794822385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2569544250614857572386053 481789546990285794822385)
          ·
            refine ⟨361342160242714346116789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481789546990285794822385 361342160242714346116789)
            ·
              refine ⟨33875827522754469948449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 361342160242714346116789 33875827522754469948449)
              ·
                rfl

theorem cell19_333988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_333988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_333988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_333988 prefixEnd_333988 := by exact prefixLift 333988
  have htrace : WordTrace (prefixWord ++ tailWord_333988) baseStart_333988 baseEnd_333988 := by
    simpa [prefixWord, tailWord_333988, baseEnd_333988] using wordTrace_append hprefix tailTrace_333988
  have hstable : (prefixWord ++ tailWord_333988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333988).length < 2 ^ (prefixWord ++ tailWord_333988).sum := by decide
  have hdescent : baseEnd_333988 < baseStart_333988 := by decide
  rcases family_descends (prefixWord ++ tailWord_333988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334005 : List Nat := [1, 3, 3, 4, 1, 1, 2, 4]
def baseStart_334005 : Nat := 118140960795 + 334005 * 2 ^ 59
def prefixEnd_334005 : Nat := 4983230072969 + 3 ^ 40 * 334005 * 2
def baseEnd_334005 : Nat := 101632655410412407467523

theorem tailTrace_334005 : CollatzResearch.WordTrace tailWord_334005 prefixEnd_334005 101632655410412407467523 := by
  unfold tailWord_334005
  simp only [CollatzResearch.WordTrace]
  refine ⟨12182163154964403357643469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8121442103309602238428979 12182163154964403357643469)
  ·
    refine ⟨4568311183111651259116301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12182163154964403357643469 4568311183111651259116301)
    ·
      refine ⟨1713116693666869222168613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4568311183111651259116301 1713116693666869222168613)
      ·
        refine ⟨321209380062537979156615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1713116693666869222168613 321209380062537979156615)
        ·
          refine ⟨481814070093806968734923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321209380062537979156615 481814070093806968734923)
          ·
            refine ⟨722721105140710453102385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481814070093806968734923 722721105140710453102385)
            ·
              refine ⟨542040828855532839826789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722721105140710453102385 542040828855532839826789)
              ·
                refine ⟨101632655410412407467523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542040828855532839826789 101632655410412407467523)
                ·
                  rfl

theorem cell19_334005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_334005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334005 prefixEnd_334005 := by exact prefixLift 334005
  have htrace : WordTrace (prefixWord ++ tailWord_334005) baseStart_334005 baseEnd_334005 := by
    simpa [prefixWord, tailWord_334005, baseEnd_334005] using wordTrace_append hprefix tailTrace_334005
  have hstable : (prefixWord ++ tailWord_334005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334005).length < 2 ^ (prefixWord ++ tailWord_334005).sum := by decide
  have hdescent : baseEnd_334005 < baseStart_334005 := by decide
  rcases family_descends (prefixWord ++ tailWord_334005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334009 : List Nat := [1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_334009 : Nat := 118140960795 + 334009 * 2 ^ 59
def prefixEnd_334009 : Nat := 4983230072969 + 3 ^ 40 * 334009 * 2
def baseEnd_334009 : Nat := 101633872549741583378623

theorem tailTrace_334009 : CollatzResearch.WordTrace tailWord_334009 prefixEnd_334009 101633872549741583378623 := by
  unfold tailWord_334009
  simp only [CollatzResearch.WordTrace]
  refine ⟨12182309046949912040789081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8121539364633274693859387 12182309046949912040789081)
  ·
    refine ⟨9136731785212434030591811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12182309046949912040789081 9136731785212434030591811)
    ·
      refine ⟨13705097677818651045887717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9136731785212434030591811 13705097677818651045887717)
      ·
        refine ⟨2569705814590997071103947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13705097677818651045887717 2569705814590997071103947)
        ·
          refine ⟨3854558721886495606655921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569705814590997071103947 3854558721886495606655921)
          ·
            refine ⟨2890919041414871704991941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3854558721886495606655921 2890919041414871704991941)
            ·
              refine ⟨542047320265288444685989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2890919041414871704991941 542047320265288444685989)
              ·
                refine ⟨101633872549741583378623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542047320265288444685989 101633872549741583378623)
                ·
                  rfl

theorem cell19_334009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_334009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334009 prefixEnd_334009 := by exact prefixLift 334009
  have htrace : WordTrace (prefixWord ++ tailWord_334009) baseStart_334009 baseEnd_334009 := by
    simpa [prefixWord, tailWord_334009, baseEnd_334009] using wordTrace_append hprefix tailTrace_334009
  have hstable : (prefixWord ++ tailWord_334009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334009).length < 2 ^ (prefixWord ++ tailWord_334009).sum := by decide
  have hdescent : baseEnd_334009 < baseStart_334009 := by decide
  rcases family_descends (prefixWord ++ tailWord_334009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334161 : List Nat := [1, 2, 2, 1, 4, 4, 5]
def baseStart_334161 : Nat := 118140960795 + 334161 * 2 ^ 59
def prefixEnd_334161 : Nat := 4983230072969 + 3 ^ 40 * 334161 * 2
def baseEnd_334161 : Nat := 33893374614750089333477

theorem tailTrace_334161 : CollatzResearch.WordTrace tailWord_334161 prefixEnd_334161 33893374614750089333477 := by
  unfold tailWord_334161
  simp only [CollatzResearch.WordTrace]
  refine ⟨12187852942399242000322337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8125235294932828000214891 12187852942399242000322337)
  ·
    refine ⟨9140889706799431500241753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12187852942399242000322337 9140889706799431500241753)
    ·
      refine ⟨6855667280099573625181315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9140889706799431500241753 6855667280099573625181315)
      ·
        refine ⟨10283500920149360437771973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6855667280099573625181315 10283500920149360437771973)
        ·
          refine ⟨1928156422528005082082245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10283500920149360437771973 1928156422528005082082245)
          ·
            refine ⟨361529329224000952890421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1928156422528005082082245 361529329224000952890421)
            ·
              refine ⟨33893374614750089333477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 361529329224000952890421 33893374614750089333477)
              ·
                rfl

theorem cell19_334161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_334161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334161 prefixEnd_334161 := by exact prefixLift 334161
  have htrace : WordTrace (prefixWord ++ tailWord_334161) baseStart_334161 baseEnd_334161 := by
    simpa [prefixWord, tailWord_334161, baseEnd_334161] using wordTrace_append hprefix tailTrace_334161
  have hstable : (prefixWord ++ tailWord_334161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334161).length < 2 ^ (prefixWord ++ tailWord_334161).sum := by decide
  have hdescent : baseEnd_334161 < baseStart_334161 := by decide
  rcases family_descends (prefixWord ++ tailWord_334161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334178 : List Nat := [3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_334178 : Nat := 118140960795 + 334178 * 2 ^ 59
def prefixEnd_334178 : Nat := 4983230072969 + 3 ^ 40 * 334178 * 2
def baseEnd_334178 : Nat := 101685296686399265622607

theorem tailTrace_334178 : CollatzResearch.WordTrace tailWord_334178 prefixEnd_334178 101685296686399265622607 := by
  unfold tailWord_334178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3047118245834413475922797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8125648655558435935794125 3047118245834413475922797)
  ·
    refine ⟨1142669342187905053471049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3047118245834413475922797 1142669342187905053471049)
    ·
      refine ⟨857002006640928790103287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1142669342187905053471049 857002006640928790103287)
      ·
        refine ⟨1285503009961393185154931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857002006640928790103287 1285503009961393185154931)
        ·
          refine ⟨1928254514942089777732397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285503009961393185154931 1928254514942089777732397)
          ·
            refine ⟨723095443103283666649649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1928254514942089777732397 723095443103283666649649)
            ·
              refine ⟨542321582327462749987237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723095443103283666649649 542321582327462749987237)
              ·
                refine ⟨101685296686399265622607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542321582327462749987237 101685296686399265622607)
                ·
                  rfl

theorem cell19_334178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_334178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334178 prefixEnd_334178 := by exact prefixLift 334178
  have htrace : WordTrace (prefixWord ++ tailWord_334178) baseStart_334178 baseEnd_334178 := by
    simpa [prefixWord, tailWord_334178, baseEnd_334178] using wordTrace_append hprefix tailTrace_334178
  have hstable : (prefixWord ++ tailWord_334178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334178).length < 2 ^ (prefixWord ++ tailWord_334178).sum := by decide
  have hdescent : baseEnd_334178 < baseStart_334178 := by decide
  rcases family_descends (prefixWord ++ tailWord_334178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334180 : List Nat := [2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_334180 : Nat := 118140960795 + 334180 * 2 ^ 59
def prefixEnd_334180 : Nat := 4983230072969 + 3 ^ 40 * 334180 * 2
def baseEnd_334180 : Nat := 101685905256063853578157

theorem tailTrace_334180 : CollatzResearch.WordTrace tailWord_334180 prefixEnd_334180 101685905256063853578157 := by
  unfold tailWord_334180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094272964665204122631997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8125697286220272163509329 6094272964665204122631997)
  ·
    refine ⟨2285352361749451545986999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6094272964665204122631997 2285352361749451545986999)
    ·
      refine ⟨3428028542624177318980499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2285352361749451545986999 3428028542624177318980499)
      ·
        refine ⟨5142042813936265978470749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428028542624177318980499 5142042813936265978470749)
        ·
          refine ⟨1928266055226099741926531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5142042813936265978470749 1928266055226099741926531)
          ·
            refine ⟨2892399082839149612889797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928266055226099741926531 2892399082839149612889797)
            ·
              refine ⟨542324828032340552416837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2892399082839149612889797 542324828032340552416837)
              ·
                refine ⟨101685905256063853578157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542324828032340552416837 101685905256063853578157)
                ·
                  rfl

theorem cell19_334180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_334180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334180 prefixEnd_334180 := by exact prefixLift 334180
  have htrace : WordTrace (prefixWord ++ tailWord_334180) baseStart_334180 baseEnd_334180 := by
    simpa [prefixWord, tailWord_334180, baseEnd_334180] using wordTrace_append hprefix tailTrace_334180
  have hstable : (prefixWord ++ tailWord_334180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334180).length < 2 ^ (prefixWord ++ tailWord_334180).sum := by decide
  have hdescent : baseEnd_334180 < baseStart_334180 := by decide
  rcases family_descends (prefixWord ++ tailWord_334180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334218 : List Nat := [3, 1, 2, 5, 8]
def baseStart_334218 : Nat := 118140960795 + 334218 * 2 ^ 59
def prefixEnd_334218 : Nat := 4983230072969 + 3 ^ 40 * 334218 * 2
def baseEnd_334218 : Nat := 3766572891840408323467

theorem tailTrace_334218 : CollatzResearch.WordTrace tailWord_334218 prefixEnd_334218 3766572891840408323467 := by
  unfold tailWord_334218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3047482975798185183786827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8126621268795160490098205 3047482975798185183786827)
  ·
    refine ⟨4571224463697277775680241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3047482975798185183786827 4571224463697277775680241)
    ·
      refine ⟨3428418347772958331760181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4571224463697277775680241 3428418347772958331760181)
      ·
        refine ⟨321414220103714843602517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3428418347772958331760181 321414220103714843602517)
        ·
          refine ⟨3766572891840408323467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 321414220103714843602517 3766572891840408323467)
          ·
            rfl

theorem cell19_334218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 8].length) (baseStart_334218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334218 prefixEnd_334218 := by exact prefixLift 334218
  have htrace : WordTrace (prefixWord ++ tailWord_334218) baseStart_334218 baseEnd_334218 := by
    simpa [prefixWord, tailWord_334218, baseEnd_334218] using wordTrace_append hprefix tailTrace_334218
  have hstable : (prefixWord ++ tailWord_334218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334218).length < 2 ^ (prefixWord ++ tailWord_334218).sum := by decide
  have hdescent : baseEnd_334218 < baseStart_334218 := by decide
  rcases family_descends (prefixWord ++ tailWord_334218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334220 : List Nat := [2, 2, 1, 2, 1, 11]
def baseStart_334220 : Nat := 118140960795 + 334220 * 2 ^ 59
def prefixEnd_334220 : Nat := 4983230072969 + 3 ^ 40 * 334220 * 2
def baseEnd_334220 : Nat := 11299786294372845854351

theorem tailTrace_334220 : CollatzResearch.WordTrace tailWord_334220 prefixEnd_334220 11299786294372845854351 := by
  unfold tailWord_334220
  simp only [CollatzResearch.WordTrace]
  refine ⟨6095002424592747538360057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8126669899456996717813409 6095002424592747538360057)
  ·
    refine ⟨4571251818444560653770043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6095002424592747538360057 4571251818444560653770043)
    ·
      refine ⟨6856877727666840980655065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4571251818444560653770043 6856877727666840980655065)
      ·
        refine ⟨5142658295750130735491299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6856877727666840980655065 5142658295750130735491299)
        ·
          refine ⟨7713987443625196103236949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142658295750130735491299 7713987443625196103236949)
          ·
            refine ⟨11299786294372845854351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7713987443625196103236949 11299786294372845854351)
            ·
              rfl

theorem cell19_334220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 11].length) (baseStart_334220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334220 prefixEnd_334220 := by exact prefixLift 334220
  have htrace : WordTrace (prefixWord ++ tailWord_334220) baseStart_334220 baseEnd_334220 := by
    simpa [prefixWord, tailWord_334220, baseEnd_334220] using wordTrace_append hprefix tailTrace_334220
  have hstable : (prefixWord ++ tailWord_334220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334220).length < 2 ^ (prefixWord ++ tailWord_334220).sum := by decide
  have hdescent : baseEnd_334220 < baseStart_334220 := by decide
  rcases family_descends (prefixWord ++ tailWord_334220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334296 : List Nat := [2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_334296 : Nat := 118140960795 + 334296 * 2 ^ 59
def prefixEnd_334296 : Nat := 4983230072969 + 3 ^ 40 * 334296 * 2
def baseEnd_334296 : Nat := 101721202296609955000063

theorem tailTrace_334296 : CollatzResearch.WordTrace tailWord_334296 prefixEnd_334296 101721202296609955000063 := by
  unfold tailWord_334296
  simp only [CollatzResearch.WordTrace]
  refine ⟨6096388398455080028243371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8128517864606773370991161 6096388398455080028243371)
  ·
    refine ⟨9144582597682620042365057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6096388398455080028243371 9144582597682620042365057)
    ·
      refine ⟨6858436948261965031773793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9144582597682620042365057 6858436948261965031773793)
      ·
        refine ⟨5143827711196473773830345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6858436948261965031773793 5143827711196473773830345)
        ·
          refine ⟨3857870783397355330372759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5143827711196473773830345 3857870783397355330372759)
          ·
            refine ⟨5786806175096032995559139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3857870783397355330372759 5786806175096032995559139)
            ·
              refine ⟨8680209262644049493338709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5786806175096032995559139 8680209262644049493338709)
              ·
                refine ⟨101721202296609955000063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8680209262644049493338709 101721202296609955000063)
                ·
                  rfl

theorem cell19_334296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_334296 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334296 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334296 prefixEnd_334296 := by exact prefixLift 334296
  have htrace : WordTrace (prefixWord ++ tailWord_334296) baseStart_334296 baseEnd_334296 := by
    simpa [prefixWord, tailWord_334296, baseEnd_334296] using wordTrace_append hprefix tailTrace_334296
  have hstable : (prefixWord ++ tailWord_334296).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334296).length < 2 ^ (prefixWord ++ tailWord_334296).sum := by decide
  have hdescent : baseEnd_334296 < baseStart_334296 := by decide
  rcases family_descends (prefixWord ++ tailWord_334296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334309 : List Nat := [1, 3, 1, 5, 2, 2, 2, 3]
def baseStart_334309 : Nat := 118140960795 + 334309 * 2 ^ 59
def prefixEnd_334309 : Nat := 4983230072969 + 3 ^ 40 * 334309 * 2
def baseEnd_334309 : Nat := 101725157999429776711139

theorem tailTrace_334309 : CollatzResearch.WordTrace tailWord_334309 prefixEnd_334309 101725157999429776711139 := by
  unfold tailWord_334309
  simp only [CollatzResearch.WordTrace]
  refine ⟨12193250945863063276709981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8128833963908708851139987 12193250945863063276709981)
  ·
    refine ⟨4572469104698648728766243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12193250945863063276709981 4572469104698648728766243)
    ·
      refine ⟨6858703657047973093149365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4572469104698648728766243 6858703657047973093149365)
      ·
        refine ⟨643003467848247477482753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6858703657047973093149365 643003467848247477482753)
        ·
          refine ⟨482252600886185608112065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643003467848247477482753 482252600886185608112065)
          ·
            refine ⟨361689450664639206084049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482252600886185608112065 361689450664639206084049)
            ·
              refine ⟨271267087998479404563037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361689450664639206084049 271267087998479404563037)
              ·
                refine ⟨101725157999429776711139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271267087998479404563037 101725157999429776711139)
                ·
                  rfl

theorem cell19_334309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_334309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334309 prefixEnd_334309 := by exact prefixLift 334309
  have htrace : WordTrace (prefixWord ++ tailWord_334309) baseStart_334309 baseEnd_334309 := by
    simpa [prefixWord, tailWord_334309, baseEnd_334309] using wordTrace_append hprefix tailTrace_334309
  have hstable : (prefixWord ++ tailWord_334309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334309).length < 2 ^ (prefixWord ++ tailWord_334309).sum := by decide
  have hdescent : baseEnd_334309 < baseStart_334309 := by decide
  rcases family_descends (prefixWord ++ tailWord_334309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334315 : List Nat := [1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_334315 : Nat := 118140960795 + 334315 * 2 ^ 59
def prefixEnd_334315 : Nat := 4983230072969 + 3 ^ 40 * 334315 * 2
def baseEnd_334315 : Nat := 101726983708423540577789

theorem tailTrace_334315 : CollatzResearch.WordTrace tailWord_334315 prefixEnd_334315 101726983708423540577789 := by
  unfold tailWord_334315
  simp only [CollatzResearch.WordTrace]
  refine ⟨12193469783841326301428399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8128979855894217534285599 12193469783841326301428399)
  ·
    refine ⟨18290204675761989452142599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12193469783841326301428399 18290204675761989452142599)
    ·
      refine ⟨27435307013642984178213899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18290204675761989452142599 27435307013642984178213899)
      ·
        refine ⟨41152960520464476267320849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27435307013642984178213899 41152960520464476267320849)
        ·
          refine ⟨30864720390348357200490637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41152960520464476267320849 30864720390348357200490637)
          ·
            refine ⟨11574270146380633950183989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30864720390348357200490637 11574270146380633950183989)
            ·
              refine ⟨1085087826223184432829749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11574270146380633950183989 1085087826223184432829749)
              ·
                refine ⟨101726983708423540577789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1085087826223184432829749 101726983708423540577789)
                ·
                  rfl

theorem cell19_334315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_334315 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334315 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334315 prefixEnd_334315 := by exact prefixLift 334315
  have htrace : WordTrace (prefixWord ++ tailWord_334315) baseStart_334315 baseEnd_334315 := by
    simpa [prefixWord, tailWord_334315, baseEnd_334315] using wordTrace_append hprefix tailTrace_334315
  have hstable : (prefixWord ++ tailWord_334315).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334315).length < 2 ^ (prefixWord ++ tailWord_334315).sum := by decide
  have hdescent : baseEnd_334315 < baseStart_334315 := by decide
  rcases family_descends (prefixWord ++ tailWord_334315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334446 : List Nat := [4, 1, 2, 2, 2, 2, 6]
def baseStart_334446 : Nat := 118140960795 + 334446 * 2 ^ 59
def prefixEnd_334446 : Nat := 4983230072969 + 3 ^ 40 * 334446 * 2
def baseEnd_334446 : Nat := 33922281673818017222107

theorem tailTrace_334446 : CollatzResearch.WordTrace tailWord_334446 prefixEnd_334446 33922281673818017222107 := by
  unfold tailWord_334446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524780968295841959305899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8132165164244490449631461 1524780968295841959305899)
  ·
    refine ⟨2287171452443762938958849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1524780968295841959305899 2287171452443762938958849)
    ·
      refine ⟨1715378589332822204219137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2287171452443762938958849 1715378589332822204219137)
      ·
        refine ⟨1286533941999616653164353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1715378589332822204219137 1286533941999616653164353)
        ·
          refine ⟨964900456499712489873265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1286533941999616653164353 964900456499712489873265)
          ·
            refine ⟨723675342374784367404949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964900456499712489873265 723675342374784367404949)
            ·
              refine ⟨33922281673818017222107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 723675342374784367404949 33922281673818017222107)
              ·
                rfl

theorem cell19_334446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_334446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334446 prefixEnd_334446 := by exact prefixLift 334446
  have htrace : WordTrace (prefixWord ++ tailWord_334446) baseStart_334446 baseEnd_334446 := by
    simpa [prefixWord, tailWord_334446, baseEnd_334446] using wordTrace_append hprefix tailTrace_334446
  have hstable : (prefixWord ++ tailWord_334446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334446).length < 2 ^ (prefixWord ++ tailWord_334446).sum := by decide
  have hdescent : baseEnd_334446 < baseStart_334446 := by decide
  rcases family_descends (prefixWord ++ tailWord_334446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334482 : List Nat := [3, 2, 3, 1, 2, 1, 4, 3]
def baseStart_334482 : Nat := 118140960795 + 334482 * 2 ^ 59
def prefixEnd_334482 : Nat := 4983230072969 + 3 ^ 40 * 334482 * 2
def baseEnd_334482 : Nat := 101777799275416634866223

theorem tailTrace_334482 : CollatzResearch.WordTrace tailWord_334482 prefixEnd_334482 101777799275416634866223 := by
  unfold tailWord_334482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3049890193559078455689425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8133040516157542548505133 3049890193559078455689425)
  ·
    refine ⟨2287417645169308841767069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3049890193559078455689425 2287417645169308841767069)
    ·
      refine ⟨857781616938490815662651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2287417645169308841767069 857781616938490815662651)
      ·
        refine ⟨1286672425407736223493977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857781616938490815662651 1286672425407736223493977)
        ·
          refine ⟨965004319055802167620483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1286672425407736223493977 965004319055802167620483)
          ·
            refine ⟨1447506478583703251430725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965004319055802167620483 1447506478583703251430725)
            ·
              refine ⟨271407464734444359643261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1447506478583703251430725 271407464734444359643261)
              ·
                refine ⟨101777799275416634866223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271407464734444359643261 101777799275416634866223)
                ·
                  rfl

theorem cell19_334482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_334482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334482 prefixEnd_334482 := by exact prefixLift 334482
  have htrace : WordTrace (prefixWord ++ tailWord_334482) baseStart_334482 baseEnd_334482 := by
    simpa [prefixWord, tailWord_334482, baseEnd_334482] using wordTrace_append hprefix tailTrace_334482
  have hstable : (prefixWord ++ tailWord_334482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334482).length < 2 ^ (prefixWord ++ tailWord_334482).sum := by decide
  have hdescent : baseEnd_334482 < baseStart_334482 := by decide
  rcases family_descends (prefixWord ++ tailWord_334482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334518 : List Nat := [5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_334518 : Nat := 118140960795 + 334518 * 2 ^ 59
def prefixEnd_334518 : Nat := 4983230072969 + 3 ^ 40 * 334518 * 2
def baseEnd_334518 : Nat := 101788753529379218066125

theorem tailTrace_334518 : CollatzResearch.WordTrace tailWord_334518 prefixEnd_334518 101788753529379218066125 := by
  unfold tailWord_334518
  simp only [CollatzResearch.WordTrace]
  refine ⟨762554612631618248191763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8133915868070594647378805 762554612631618248191763)
  ·
    refine ⟨1143831918947427372287645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762554612631618248191763 1143831918947427372287645)
    ·
      refine ⟨428936969605285264607867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1143831918947427372287645 428936969605285264607867)
      ·
        refine ⟨643405454407927896911801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428936969605285264607867 643405454407927896911801)
        ·
          refine ⟨482554090805945922683851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643405454407927896911801 482554090805945922683851)
          ·
            refine ⟨723831136208918884025777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482554090805945922683851 723831136208918884025777)
            ·
              refine ⟨542873352156689163019333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723831136208918884025777 542873352156689163019333)
              ·
                refine ⟨101788753529379218066125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542873352156689163019333 101788753529379218066125)
                ·
                  rfl

theorem cell19_334518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_334518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334518 prefixEnd_334518 := by exact prefixLift 334518
  have htrace : WordTrace (prefixWord ++ tailWord_334518) baseStart_334518 baseEnd_334518 := by
    simpa [prefixWord, tailWord_334518, baseEnd_334518] using wordTrace_append hprefix tailTrace_334518
  have hstable : (prefixWord ++ tailWord_334518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334518).length < 2 ^ (prefixWord ++ tailWord_334518).sum := by decide
  have hdescent : baseEnd_334518 < baseStart_334518 := by decide
  rcases family_descends (prefixWord ++ tailWord_334518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334655 : List Nat := [1, 1, 2, 2, 5, 1, 4, 3]
def baseStart_334655 : Nat := 118140960795 + 334655 * 2 ^ 59
def prefixEnd_334655 : Nat := 4983230072969 + 3 ^ 40 * 334655 * 2
def baseEnd_334655 : Nat := 101830440551403493021307

theorem tailTrace_334655 : CollatzResearch.WordTrace tailWord_334655 prefixEnd_334655 101830440551403493021307 := by
  unfold tailWord_334655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12205870602609564368805419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8137247068406376245870279 12205870602609564368805419)
  ·
    refine ⟨18308805903914346553208129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12205870602609564368805419 18308805903914346553208129)
    ·
      refine ⟨13731604427935759914906097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18308805903914346553208129 13731604427935759914906097)
      ·
        refine ⟨10298703320951819936179573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13731604427935759914906097 10298703320951819936179573)
        ·
          refine ⟨965503436339233119016835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10298703320951819936179573 965503436339233119016835)
          ·
            refine ⟨1448255154508849678525253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965503436339233119016835 1448255154508849678525253)
            ·
              refine ⟨271547841470409314723485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1448255154508849678525253 271547841470409314723485)
              ·
                refine ⟨101830440551403493021307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271547841470409314723485 101830440551403493021307)
                ·
                  rfl

theorem cell19_334655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_334655 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334655 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334655 prefixEnd_334655 := by exact prefixLift 334655
  have htrace : WordTrace (prefixWord ++ tailWord_334655) baseStart_334655 baseEnd_334655 := by
    simpa [prefixWord, tailWord_334655, baseEnd_334655] using wordTrace_append hprefix tailTrace_334655
  have hstable : (prefixWord ++ tailWord_334655).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334655).length < 2 ^ (prefixWord ++ tailWord_334655).sum := by decide
  have hdescent : baseEnd_334655 < baseStart_334655 := by decide
  rcases family_descends (prefixWord ++ tailWord_334655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334695 : List Nat := [1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_334695 : Nat := 118140960795 + 334695 * 2 ^ 59
def prefixEnd_334695 : Nat := 4983230072969 + 3 ^ 40 * 334695 * 2
def baseEnd_334695 : Nat := 101842611944695252132309

theorem tailTrace_334695 : CollatzResearch.WordTrace tailWord_334695 prefixEnd_334695 101842611944695252132309 := by
  unfold tailWord_334695
  simp only [CollatzResearch.WordTrace]
  refine ⟨12207329522464651200261539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8138219681643100800174359 12207329522464651200261539)
  ·
    refine ⟨18310994283696976800392309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12207329522464651200261539 18310994283696976800392309)
    ·
      refine ⟨1716655714096591575036779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18310994283696976800392309 1716655714096591575036779)
      ·
        refine ⟨2574983571144887362555169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716655714096591575036779 2574983571144887362555169)
        ·
          refine ⟨1931237678358665521916377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2574983571144887362555169 1931237678358665521916377)
          ·
            refine ⟨1448428258768999141437283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1931237678358665521916377 1448428258768999141437283)
            ·
              refine ⟨2172642388153498712155925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448428258768999141437283 2172642388153498712155925)
              ·
                refine ⟨101842611944695252132309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2172642388153498712155925 101842611944695252132309)
                ·
                  rfl

theorem cell19_334695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_334695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334695 prefixEnd_334695 := by exact prefixLift 334695
  have htrace : WordTrace (prefixWord ++ tailWord_334695) baseStart_334695 baseEnd_334695 := by
    simpa [prefixWord, tailWord_334695, baseEnd_334695] using wordTrace_append hprefix tailTrace_334695
  have hstable : (prefixWord ++ tailWord_334695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334695).length < 2 ^ (prefixWord ++ tailWord_334695).sum := by decide
  have hdescent : baseEnd_334695 < baseStart_334695 := by decide
  rcases family_descends (prefixWord ++ tailWord_334695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334748 : List Nat := [2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_334748 : Nat := 118140960795 + 334748 * 2 ^ 59
def prefixEnd_334748 : Nat := 4983230072969 + 3 ^ 40 * 334748 * 2
def baseEnd_334748 : Nat := 101858739040806832954387

theorem tailTrace_334748 : CollatzResearch.WordTrace tailWord_334748 prefixEnd_334748 101858739040806832954387 := by
  unfold tailWord_334748
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104631295636320625970449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8139508394181760834627265 6104631295636320625970449)
  ·
    refine ⟨4578473471727240469477837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6104631295636320625970449 4578473471727240469477837)
    ·
      refine ⟨1716927551897715176054189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4578473471727240469477837 1716927551897715176054189)
      ·
        refine ⟨643847831961643191020321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1716927551897715176054189 643847831961643191020321)
        ·
          refine ⟨482885873971232393265241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643847831961643191020321 482885873971232393265241)
          ·
            refine ⟨362164405478424294948931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482885873971232393265241 362164405478424294948931)
            ·
              refine ⟨543246608217636442423397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362164405478424294948931 543246608217636442423397)
              ·
                refine ⟨101858739040806832954387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 543246608217636442423397 101858739040806832954387)
                ·
                  rfl

theorem cell19_334748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_334748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334748 prefixEnd_334748 := by exact prefixLift 334748
  have htrace : WordTrace (prefixWord ++ tailWord_334748) baseStart_334748 baseEnd_334748 := by
    simpa [prefixWord, tailWord_334748, baseEnd_334748] using wordTrace_append hprefix tailTrace_334748
  have hstable : (prefixWord ++ tailWord_334748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334748).length < 2 ^ (prefixWord ++ tailWord_334748).sum := by decide
  have hdescent : baseEnd_334748 < baseStart_334748 := by decide
  rcases family_descends (prefixWord ++ tailWord_334748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334752 : List Nat := [2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_334752 : Nat := 118140960795 + 334752 * 2 ^ 59
def prefixEnd_334752 : Nat := 4983230072969 + 3 ^ 40 * 334752 * 2
def baseEnd_334752 : Nat := 101859956180136008865487

theorem tailTrace_334752 : CollatzResearch.WordTrace tailWord_334752 prefixEnd_334752 101859956180136008865487 := by
  unfold tailWord_334752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104704241629074967543255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8139605655505433290057673 6104704241629074967543255)
  ·
    refine ⟨9157056362443612451314883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6104704241629074967543255 9157056362443612451314883)
    ·
      refine ⟨13735584543665418676972325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9157056362443612451314883 13735584543665418676972325)
      ·
        refine ⟨2575422101937266001932311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13735584543665418676972325 2575422101937266001932311)
        ·
          refine ⟨3863133152905899002898467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575422101937266001932311 3863133152905899002898467)
          ·
            refine ⟨5794699729358848504347701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863133152905899002898467 5794699729358848504347701)
            ·
              refine ⟨543253099627392047282597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5794699729358848504347701 543253099627392047282597)
              ·
                refine ⟨101859956180136008865487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 543253099627392047282597 101859956180136008865487)
                ·
                  rfl

theorem cell19_334752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_334752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334752 prefixEnd_334752 := by exact prefixLift 334752
  have htrace : WordTrace (prefixWord ++ tailWord_334752) baseStart_334752 baseEnd_334752 := by
    simpa [prefixWord, tailWord_334752, baseEnd_334752] using wordTrace_append hprefix tailTrace_334752
  have hstable : (prefixWord ++ tailWord_334752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334752).length < 2 ^ (prefixWord ++ tailWord_334752).sum := by decide
  have hdescent : baseEnd_334752 < baseStart_334752 := by decide
  rcases family_descends (prefixWord ++ tailWord_334752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334765 : List Nat := [1, 5, 2, 3, 1, 1, 3, 3]
def baseStart_334765 : Nat := 118140960795 + 334765 * 2 ^ 59
def prefixEnd_334765 : Nat := 4983230072969 + 3 ^ 40 * 334765 * 2
def baseEnd_334765 : Nat := 101863911882955830576563

theorem tailTrace_334765 : CollatzResearch.WordTrace tailWord_334765 prefixEnd_334765 101863911882955830576563 := by
  unfold tailWord_334765
  simp only [CollatzResearch.WordTrace]
  refine ⟨12209882632211053155309749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8139921754807368770206499 12209882632211053155309749)
  ·
    refine ⟨1144676496769786233310289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12209882632211053155309749 1144676496769786233310289)
    ·
      refine ⟨858507372577339674982717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1144676496769786233310289 858507372577339674982717)
      ·
        refine ⟨321940264716502378118519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 858507372577339674982717 321940264716502378118519)
        ·
          refine ⟨482910397074753567177779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321940264716502378118519 482910397074753567177779)
          ·
            refine ⟨724365595612130350766669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482910397074753567177779 724365595612130350766669)
            ·
              refine ⟨271637098354548881537501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 724365595612130350766669 271637098354548881537501)
              ·
                refine ⟨101863911882955830576563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271637098354548881537501 101863911882955830576563)
                ·
                  rfl

theorem cell19_334765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_334765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334765 prefixEnd_334765 := by exact prefixLift 334765
  have htrace : WordTrace (prefixWord ++ tailWord_334765) baseStart_334765 baseEnd_334765 := by
    simpa [prefixWord, tailWord_334765, baseEnd_334765] using wordTrace_append hprefix tailTrace_334765
  have hstable : (prefixWord ++ tailWord_334765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334765).length < 2 ^ (prefixWord ++ tailWord_334765).sum := by decide
  have hdescent : baseEnd_334765 < baseStart_334765 := by decide
  rcases family_descends (prefixWord ++ tailWord_334765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334826 : List Nat := [3, 1, 3, 1, 2, 2, 4, 3]
def baseStart_334826 : Nat := 118140960795 + 334826 * 2 ^ 59
def prefixEnd_334826 : Nat := 4983230072969 + 3 ^ 40 * 334826 * 2
def baseEnd_334826 : Nat := 101882473257725763220841

theorem tailTrace_334826 : CollatzResearch.WordTrace tailWord_334826 prefixEnd_334826 101882473257725763220841 := by
  unfold tailWord_334826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053026871247515143320083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8141404989993373715520221 3053026871247515143320083)
  ·
    refine ⟨4579540306871272714980125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3053026871247515143320083 4579540306871272714980125)
    ·
      refine ⟨1717327615076727268117547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4579540306871272714980125 1717327615076727268117547)
      ·
        refine ⟨2575991422615090902176321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717327615076727268117547 2575991422615090902176321)
        ·
          refine ⟨1931993566961318176632241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2575991422615090902176321 1931993566961318176632241)
          ·
            refine ⟨1448995175220988632474181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1931993566961318176632241 1448995175220988632474181)
            ·
              refine ⟨271686595353935368588909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1448995175220988632474181 271686595353935368588909)
              ·
                refine ⟨101882473257725763220841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271686595353935368588909 101882473257725763220841)
                ·
                  rfl

theorem cell19_334826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_334826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334826 prefixEnd_334826 := by exact prefixLift 334826
  have htrace : WordTrace (prefixWord ++ tailWord_334826) baseStart_334826 baseEnd_334826 := by
    simpa [prefixWord, tailWord_334826, baseEnd_334826] using wordTrace_append hprefix tailTrace_334826
  have hstable : (prefixWord ++ tailWord_334826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334826).length < 2 ^ (prefixWord ++ tailWord_334826).sum := by decide
  have hdescent : baseEnd_334826 < baseStart_334826 := by decide
  rcases family_descends (prefixWord ++ tailWord_334826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334940 : List Nat := [2, 2, 4, 1, 1, 1, 5, 3]
def baseStart_334940 : Nat := 118140960795 + 334940 * 2 ^ 59
def prefixEnd_334940 : Nat := 4983230072969 + 3 ^ 40 * 334940 * 2
def baseEnd_334940 : Nat := 101917161728607276687197

theorem tailTrace_334940 : CollatzResearch.WordTrace tailWord_334940 prefixEnd_334940 101917161728607276687197 := by
  unfold tailWord_334940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6108132703288529021465137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8144176937718038695286849 6108132703288529021465137)
  ·
    refine ⟨4581099527466396766098853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6108132703288529021465137 4581099527466396766098853)
    ·
      refine ⟨858956161399949393643535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4581099527466396766098853 858956161399949393643535)
      ·
        refine ⟨1288434242099924090465303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858956161399949393643535 1288434242099924090465303)
        ·
          refine ⟨1932651363149886135697955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288434242099924090465303 1932651363149886135697955)
          ·
            refine ⟨2898977044724829203546933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932651363149886135697955 2898977044724829203546933)
            ·
              refine ⟨271779097942952737832525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2898977044724829203546933 271779097942952737832525)
              ·
                refine ⟨101917161728607276687197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271779097942952737832525 101917161728607276687197)
                ·
                  rfl

theorem cell19_334940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_334940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334940 prefixEnd_334940 := by exact prefixLift 334940
  have htrace : WordTrace (prefixWord ++ tailWord_334940) baseStart_334940 baseEnd_334940 := by
    simpa [prefixWord, tailWord_334940, baseEnd_334940] using wordTrace_append hprefix tailTrace_334940
  have hstable : (prefixWord ++ tailWord_334940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334940).length < 2 ^ (prefixWord ++ tailWord_334940).sum := by decide
  have hdescent : baseEnd_334940 < baseStart_334940 := by decide
  rcases family_descends (prefixWord ++ tailWord_334940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334999 : List Nat := [1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_334999 : Nat := 118140960795 + 334999 * 2 ^ 59
def prefixEnd_334999 : Nat := 4983230072969 + 3 ^ 40 * 334999 * 2
def baseEnd_334999 : Nat := 101935114533712621375925

theorem tailTrace_334999 : CollatzResearch.WordTrace tailWord_334999 prefixEnd_334999 101935114533712621375925 := by
  unfold tailWord_334999
  simp only [CollatzResearch.WordTrace]
  refine ⟨12218417313363311119328051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8145611542242207412885367 12218417313363311119328051)
  ·
    refine ⟨18327625970044966678992077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12218417313363311119328051 18327625970044966678992077)
    ·
      refine ⟨6872859738766862504622029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18327625970044966678992077 6872859738766862504622029)
      ·
        refine ⟨2577322402037573439233261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6872859738766862504622029 2577322402037573439233261)
        ·
          refine ⟨966495900764090039712473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2577322402037573439233261 966495900764090039712473)
          ·
            refine ⟨724871925573067529784355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966495900764090039712473 724871925573067529784355)
            ·
              refine ⟨1087307888359601294676533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724871925573067529784355 1087307888359601294676533)
              ·
                refine ⟨101935114533712621375925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1087307888359601294676533 101935114533712621375925)
                ·
                  rfl

theorem cell19_334999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_334999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_334999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_334999 prefixEnd_334999 := by exact prefixLift 334999
  have htrace : WordTrace (prefixWord ++ tailWord_334999) baseStart_334999 baseEnd_334999 := by
    simpa [prefixWord, tailWord_334999, baseEnd_334999] using wordTrace_append hprefix tailTrace_334999
  have hstable : (prefixWord ++ tailWord_334999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334999).length < 2 ^ (prefixWord ++ tailWord_334999).sum := by decide
  have hdescent : baseEnd_334999 < baseStart_334999 := by decide
  rcases family_descends (prefixWord ++ tailWord_334999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335039 : List Nat := [1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_335039 : Nat := 118140960795 + 335039 * 2 ^ 59
def prefixEnd_335039 : Nat := 4983230072969 + 3 ^ 40 * 335039 * 2
def baseEnd_335039 : Nat := 101947285927004380486927

theorem tailTrace_335039 : CollatzResearch.WordTrace tailWord_335039 prefixEnd_335039 101947285927004380486927 := by
  unfold tailWord_335039
  simp only [CollatzResearch.WordTrace]
  refine ⟨12219876233218397950784171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8146584155478931967189447 12219876233218397950784171)
  ·
    refine ⟨18329814349827596926176257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12219876233218397950784171 18329814349827596926176257)
    ·
      refine ⟨13747360762370697694632193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18329814349827596926176257 13747360762370697694632193)
      ·
        refine ⟨10310520571778023270974145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13747360762370697694632193 10310520571778023270974145)
        ·
          refine ⟨7732890428833517453230609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10310520571778023270974145 7732890428833517453230609)
          ·
            refine ⟨5799667821625138089922957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7732890428833517453230609 5799667821625138089922957)
            ·
              refine ⟨2174875433109426783721109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5799667821625138089922957 2174875433109426783721109)
              ·
                refine ⟨101947285927004380486927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2174875433109426783721109 101947285927004380486927)
                ·
                  rfl

theorem cell19_335039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_335039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335039 prefixEnd_335039 := by exact prefixLift 335039
  have htrace : WordTrace (prefixWord ++ tailWord_335039) baseStart_335039 baseEnd_335039 := by
    simpa [prefixWord, tailWord_335039, baseEnd_335039] using wordTrace_append hprefix tailTrace_335039
  have hstable : (prefixWord ++ tailWord_335039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335039).length < 2 ^ (prefixWord ++ tailWord_335039).sum := by decide
  have hdescent : baseEnd_335039 < baseStart_335039 := by decide
  rcases family_descends (prefixWord ++ tailWord_335039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335077 : List Nat := [1, 3, 1, 4, 10]
def baseStart_335077 : Nat := 118140960795 + 335077 * 2 ^ 59
def prefixEnd_335077 : Nat := 4983230072969 + 3 ^ 40 * 335077 * 2
def baseEnd_335077 : Nat := 3776253657430798208977

theorem tailTrace_335077 : CollatzResearch.WordTrace tailWord_335077 prefixEnd_335077 3776253657430798208977 := by
  unfold tailWord_335077
  simp only [CollatzResearch.WordTrace]
  refine ⟨12221262207080730440667485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8147508138053820293778323 12221262207080730440667485)
  ·
    refine ⟨4582973327655273915250307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12221262207080730440667485 4582973327655273915250307)
    ·
      refine ⟨6874459991482910872875461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4582973327655273915250307 6874459991482910872875461)
      ·
        refine ⟨1288961248403045788664149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6874459991482910872875461 1288961248403045788664149)
        ·
          refine ⟨3776253657430798208977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1288961248403045788664149 3776253657430798208977)
          ·
            rfl

theorem cell19_335077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 10].length) (baseStart_335077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335077 prefixEnd_335077 := by exact prefixLift 335077
  have htrace : WordTrace (prefixWord ++ tailWord_335077) baseStart_335077 baseEnd_335077 := by
    simpa [prefixWord, tailWord_335077, baseEnd_335077] using wordTrace_append hprefix tailTrace_335077
  have hstable : (prefixWord ++ tailWord_335077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335077).length < 2 ^ (prefixWord ++ tailWord_335077).sum := by decide
  have hdescent : baseEnd_335077 < baseStart_335077 := by decide
  rcases family_descends (prefixWord ++ tailWord_335077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335090 : List Nat := [3, 2, 1, 3, 4, 1, 1, 4]
def baseStart_335090 : Nat := 118140960795 + 335090 * 2 ^ 59
def prefixEnd_335090 : Nat := 4983230072969 + 3 ^ 40 * 335090 * 2
def baseEnd_335090 : Nat := 101962804453451373353455

theorem tailTrace_335090 : CollatzResearch.WordTrace tailWord_335090 prefixEnd_335090 101962804453451373353455 := by
  unfold tailWord_335090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055434089008408415222681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8147824237355755773927149 3055434089008408415222681)
  ·
    refine ⟨2291575566756306311417011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3055434089008408415222681 2291575566756306311417011)
    ·
      refine ⟨3437363350134459467125517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2291575566756306311417011 3437363350134459467125517)
      ·
        refine ⟨1289011256300422300172069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3437363350134459467125517 1289011256300422300172069)
        ·
          refine ⟨241689610556329181282263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1289011256300422300172069 241689610556329181282263)
          ·
            refine ⟨362534415834493771923395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241689610556329181282263 362534415834493771923395)
            ·
              refine ⟨543801623751740657885093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362534415834493771923395 543801623751740657885093)
              ·
                refine ⟨101962804453451373353455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 543801623751740657885093 101962804453451373353455)
                ·
                  rfl

theorem cell19_335090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_335090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335090 prefixEnd_335090 := by exact prefixLift 335090
  have htrace : WordTrace (prefixWord ++ tailWord_335090) baseStart_335090 baseEnd_335090 := by
    simpa [prefixWord, tailWord_335090, baseEnd_335090] using wordTrace_append hprefix tailTrace_335090
  have hstable : (prefixWord ++ tailWord_335090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335090).length < 2 ^ (prefixWord ++ tailWord_335090).sum := by decide
  have hdescent : baseEnd_335090 < baseStart_335090 := by decide
  rcases family_descends (prefixWord ++ tailWord_335090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335113 : List Nat := [1, 2, 1, 1, 3, 3, 5, 3]
def baseStart_335113 : Nat := 118140960795 + 335113 * 2 ^ 59
def prefixEnd_335113 : Nat := 4983230072969 + 3 ^ 40 * 335113 * 2
def baseEnd_335113 : Nat := 101969803004594134842281

theorem tailTrace_335113 : CollatzResearch.WordTrace tailWord_335113 prefixEnd_335113 101969803004594134842281 := by
  unfold tailWord_335113
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222575234950308588977993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8148383489966872392651995 12222575234950308588977993)
  ·
    refine ⟨9166931426212731441733495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12222575234950308588977993 9166931426212731441733495)
    ·
      refine ⟨13750397139319097162600243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9166931426212731441733495 13750397139319097162600243)
      ·
        refine ⟨20625595708978645743900365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13750397139319097162600243 20625595708978645743900365)
        ·
          refine ⟨7734598390866992153962637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20625595708978645743900365 7734598390866992153962637)
          ·
            refine ⟨2900474396575122057735989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7734598390866992153962637 2900474396575122057735989)
            ·
              refine ⟨271919474678917692912749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2900474396575122057735989 271919474678917692912749)
              ·
                refine ⟨101969803004594134842281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271919474678917692912749 101969803004594134842281)
                ·
                  rfl

theorem cell19_335113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_335113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335113 prefixEnd_335113 := by exact prefixLift 335113
  have htrace : WordTrace (prefixWord ++ tailWord_335113) baseStart_335113 baseEnd_335113 := by
    simpa [prefixWord, tailWord_335113, baseEnd_335113] using wordTrace_append hprefix tailTrace_335113
  have hstable : (prefixWord ++ tailWord_335113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335113).length < 2 ^ (prefixWord ++ tailWord_335113).sum := by decide
  have hdescent : baseEnd_335113 < baseStart_335113 := by decide
  rcases family_descends (prefixWord ++ tailWord_335113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335189 : List Nat := [1, 3, 2, 2, 3, 3, 5]
def baseStart_335189 : Nat := 118140960795 + 335189 * 2 ^ 59
def prefixEnd_335189 : Nat := 4983230072969 + 3 ^ 40 * 335189 * 2
def baseEnd_335189 : Nat := 33997642883949492384395

theorem tailTrace_335189 : CollatzResearch.WordTrace tailWord_335189 prefixEnd_335189 33997642883949492384395 := by
  unfold tailWord_335189
  simp only [CollatzResearch.WordTrace]
  refine ⟨12225347182674973568744621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8150231455116649045829747 12225347182674973568744621)
  ·
    refine ⟨4584505193503115088279233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12225347182674973568744621 4584505193503115088279233)
    ·
      refine ⟨3438378895127336316209425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4584505193503115088279233 3438378895127336316209425)
      ·
        refine ⟨2578784171345502237157069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3438378895127336316209425 2578784171345502237157069)
        ·
          refine ⟨967044064254563338933901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2578784171345502237157069 967044064254563338933901)
          ·
            refine ⟨362641524095461252100213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 967044064254563338933901 362641524095461252100213)
            ·
              refine ⟨33997642883949492384395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 362641524095461252100213 33997642883949492384395)
              ·
                rfl

theorem cell19_335189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_335189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335189 prefixEnd_335189 := by exact prefixLift 335189
  have htrace : WordTrace (prefixWord ++ tailWord_335189) baseStart_335189 baseEnd_335189 := by
    simpa [prefixWord, tailWord_335189, baseEnd_335189] using wordTrace_append hprefix tailTrace_335189
  have hstable : (prefixWord ++ tailWord_335189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335189).length < 2 ^ (prefixWord ++ tailWord_335189).sum := by decide
  have hdescent : baseEnd_335189 < baseStart_335189 := by decide
  rcases family_descends (prefixWord ++ tailWord_335189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335191 : List Nat := [1, 1, 3, 2, 3, 2, 7]
def baseStart_335191 : Nat := 118140960795 + 335191 * 2 ^ 59
def prefixEnd_335191 : Nat := 4983230072969 + 3 ^ 40 * 335191 * 2
def baseEnd_335191 : Nat := 33997845740504355036245

theorem tailTrace_335191 : CollatzResearch.WordTrace tailWord_335191 prefixEnd_335191 33997845740504355036245 := by
  unfold tailWord_335191
  simp only [CollatzResearch.WordTrace]
  refine ⟨12225420128667727910317427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8150280085778485273544951 12225420128667727910317427)
  ·
    refine ⟨18338130193001591865476141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12225420128667727910317427 18338130193001591865476141)
    ·
      refine ⟨6876798822375596949553553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18338130193001591865476141 6876798822375596949553553)
      ·
        refine ⟨5157599116781697712165165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6876798822375596949553553 5157599116781697712165165)
        ·
          refine ⟨1934099668793136642061937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5157599116781697712165165 1934099668793136642061937)
          ·
            refine ⟨1450574751594852481546453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1934099668793136642061937 1450574751594852481546453)
            ·
              refine ⟨33997845740504355036245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1450574751594852481546453 33997845740504355036245)
              ·
                rfl

theorem cell19_335191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_335191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335191 prefixEnd_335191 := by exact prefixLift 335191
  have htrace : WordTrace (prefixWord ++ tailWord_335191) baseStart_335191 baseEnd_335191 := by
    simpa [prefixWord, tailWord_335191, baseEnd_335191] using wordTrace_append hprefix tailTrace_335191
  have hstable : (prefixWord ++ tailWord_335191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335191).length < 2 ^ (prefixWord ++ tailWord_335191).sum := by decide
  have hdescent : baseEnd_335191 < baseStart_335191 := by decide
  rcases family_descends (prefixWord ++ tailWord_335191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335229 : List Nat := [1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_335229 : Nat := 118140960795 + 335229 * 2 ^ 59
def prefixEnd_335229 : Nat := 4983230072969 + 3 ^ 40 * 335229 * 2
def baseEnd_335229 : Nat := 102005100045140236264187

theorem tailTrace_335229 : CollatzResearch.WordTrace tailWord_335229 prefixEnd_335229 102005100045140236264187 := by
  unfold tailWord_335229
  simp only [CollatzResearch.WordTrace]
  refine ⟨12226806102530060400200741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8151204068353373600133827 12226806102530060400200741)
  ·
    refine ⟨2292526144224386325037639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12226806102530060400200741 2292526144224386325037639)
    ·
      refine ⟨3438789216336579487556459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2292526144224386325037639 3438789216336579487556459)
      ·
        refine ⟨5158183824504869231334689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3438789216336579487556459 5158183824504869231334689)
        ·
          refine ⟨3868637868378651923501017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5158183824504869231334689 3868637868378651923501017)
          ·
            refine ⟨2901478401283988942625763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3868637868378651923501017 2901478401283988942625763)
            ·
              refine ⟨4352217601925983413938645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901478401283988942625763 4352217601925983413938645)
              ·
                refine ⟨102005100045140236264187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4352217601925983413938645 102005100045140236264187)
                ·
                  rfl

theorem cell19_335229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_335229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335229 prefixEnd_335229 := by exact prefixLift 335229
  have htrace : WordTrace (prefixWord ++ tailWord_335229) baseStart_335229 baseEnd_335229 := by
    simpa [prefixWord, tailWord_335229, baseEnd_335229] using wordTrace_append hprefix tailTrace_335229
  have hstable : (prefixWord ++ tailWord_335229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335229).length < 2 ^ (prefixWord ++ tailWord_335229).sum := by decide
  have hdescent : baseEnd_335229 < baseStart_335229 := by decide
  rcases family_descends (prefixWord ++ tailWord_335229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335246 : List Nat := [4, 1, 1, 4, 2, 7]
def baseStart_335246 : Nat := 118140960795 + 335246 * 2 ^ 59
def prefixEnd_335246 : Nat := 4983230072969 + 3 ^ 40 * 335246 * 2
def baseEnd_335246 : Nat := 11334474765254359320707

theorem tailTrace_335246 : CollatzResearch.WordTrace tailWord_335246 prefixEnd_335246 11334474765254359320707 := by
  unfold tailWord_335246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1528428267933559037946199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8151617428978981535713061 1528428267933559037946199)
  ·
    refine ⟨2292642401900338556919299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1528428267933559037946199 2292642401900338556919299)
    ·
      refine ⟨3438963602850507835378949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2292642401900338556919299 3438963602850507835378949)
      ·
        refine ⟨644805675534470219133553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3438963602850507835378949 644805675534470219133553)
        ·
          refine ⟨483604256650852664350165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644805675534470219133553 483604256650852664350165)
          ·
            refine ⟨11334474765254359320707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 483604256650852664350165 11334474765254359320707)
            ·
              rfl

theorem cell19_335246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 7].length) (baseStart_335246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335246 prefixEnd_335246 := by exact prefixLift 335246
  have htrace : WordTrace (prefixWord ++ tailWord_335246) baseStart_335246 baseEnd_335246 := by
    simpa [prefixWord, tailWord_335246, baseEnd_335246] using wordTrace_append hprefix tailTrace_335246
  have hstable : (prefixWord ++ tailWord_335246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335246).length < 2 ^ (prefixWord ++ tailWord_335246).sum := by decide
  have hdescent : baseEnd_335246 < baseStart_335246 := by decide
  rcases family_descends (prefixWord ++ tailWord_335246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335381 : List Nat := [1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_335381 : Nat := 118140960795 + 335381 * 2 ^ 59
def prefixEnd_335381 : Nat := 4983230072969 + 3 ^ 40 * 335381 * 2
def baseEnd_335381 : Nat := 102051351339648920885995

theorem tailTrace_335381 : CollatzResearch.WordTrace tailWord_335381 prefixEnd_335381 102051351339648920885995 := by
  unfold tailWord_335381
  simp only [CollatzResearch.WordTrace]
  refine ⟨12232349997979390359733997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8154899998652926906489331 12232349997979390359733997)
  ·
    refine ⟨4587131249242271384900249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12232349997979390359733997 4587131249242271384900249)
    ·
      refine ⟨3440348436931703538675187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4587131249242271384900249 3440348436931703538675187)
      ·
        refine ⟨5160522655397555308012781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3440348436931703538675187 5160522655397555308012781)
        ·
          refine ⟨1935195995774083240504793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5160522655397555308012781 1935195995774083240504793)
          ·
            refine ⟨1451396996830562430378595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935195995774083240504793 1451396996830562430378595)
            ·
              refine ⟨2177095495245843645567893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451396996830562430378595 2177095495245843645567893)
              ·
                refine ⟨102051351339648920885995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2177095495245843645567893 102051351339648920885995)
                ·
                  rfl

theorem cell19_335381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_335381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335381 prefixEnd_335381 := by exact prefixLift 335381
  have htrace : WordTrace (prefixWord ++ tailWord_335381) baseStart_335381 baseEnd_335381 := by
    simpa [prefixWord, tailWord_335381, baseEnd_335381] using wordTrace_append hprefix tailTrace_335381
  have hstable : (prefixWord ++ tailWord_335381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335381).length < 2 ^ (prefixWord ++ tailWord_335381).sum := by decide
  have hdescent : baseEnd_335381 < baseStart_335381 := by decide
  rcases family_descends (prefixWord ++ tailWord_335381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335430 : List Nat := [6, 1, 1, 1, 4, 1, 1, 4]
def baseStart_335430 : Nat := 118140960795 + 335430 * 2 ^ 59
def prefixEnd_335430 : Nat := 4983230072969 + 3 ^ 40 * 335430 * 2
def baseEnd_335430 : Nat := 102066261296431325796973

theorem tailTrace_335430 : CollatzResearch.WordTrace tailWord_335430 prefixEnd_335430 102066261296431325796973 := by
  unfold tailWord_335430
  simp only [CollatzResearch.WordTrace]
  refine ⟨382316786712558491508367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8156091449867914485511829 382316786712558491508367)
  ·
    refine ⟨573475180068837737262551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 382316786712558491508367 573475180068837737262551)
    ·
      refine ⟨860212770103256605893827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 573475180068837737262551 860212770103256605893827)
      ·
        refine ⟨1290319155154884908840741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860212770103256605893827 1290319155154884908840741)
        ·
          refine ⟨241934841591540920407639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1290319155154884908840741 241934841591540920407639)
          ·
            refine ⟨362902262387311380611459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241934841591540920407639 362902262387311380611459)
            ·
              refine ⟨544353393580967070917189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362902262387311380611459 544353393580967070917189)
              ·
                refine ⟨102066261296431325796973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544353393580967070917189 102066261296431325796973)
                ·
                  rfl

theorem cell19_335430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_335430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335430 prefixEnd_335430 := by exact prefixLift 335430
  have htrace : WordTrace (prefixWord ++ tailWord_335430) baseStart_335430 baseEnd_335430 := by
    simpa [prefixWord, tailWord_335430, baseEnd_335430] using wordTrace_append hprefix tailTrace_335430
  have hstable : (prefixWord ++ tailWord_335430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335430).length < 2 ^ (prefixWord ++ tailWord_335430).sum := by decide
  have hdescent : baseEnd_335430 < baseStart_335430 := by decide
  rcases family_descends (prefixWord ++ tailWord_335430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335436 : List Nat := [2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_335436 : Nat := 118140960795 + 335436 * 2 ^ 59
def prefixEnd_335436 : Nat := 4983230072969 + 3 ^ 40 * 335436 * 2
def baseEnd_335436 : Nat := 102068087005425089663623

theorem tailTrace_335436 : CollatzResearch.WordTrace tailWord_335436 prefixEnd_335436 102068087005425089663623 := by
  unfold tailWord_335436
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117178006390067376493081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8156237341853423168657441 6117178006390067376493081)
  ·
    refine ⟨4587883504792550532369811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6117178006390067376493081 4587883504792550532369811)
    ·
      refine ⟨6881825257188825798554717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4587883504792550532369811 6881825257188825798554717)
      ·
        refine ⟨2580684471445809674458019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6881825257188825798554717 2580684471445809674458019)
        ·
          refine ⟨3871026707168714511687029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580684471445809674458019 3871026707168714511687029)
          ·
            refine ⟨362908753797066985470659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3871026707168714511687029 362908753797066985470659)
            ·
              refine ⟨544363130695600478205989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362908753797066985470659 544363130695600478205989)
              ·
                refine ⟨102068087005425089663623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544363130695600478205989 102068087005425089663623)
                ·
                  rfl

theorem cell19_335436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_335436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335436 prefixEnd_335436 := by exact prefixLift 335436
  have htrace : WordTrace (prefixWord ++ tailWord_335436) baseStart_335436 baseEnd_335436 := by
    simpa [prefixWord, tailWord_335436, baseEnd_335436] using wordTrace_append hprefix tailTrace_335436
  have hstable : (prefixWord ++ tailWord_335436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335436).length < 2 ^ (prefixWord ++ tailWord_335436).sum := by decide
  have hdescent : baseEnd_335436 < baseStart_335436 := by decide
  rcases family_descends (prefixWord ++ tailWord_335436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335508 : List Nat := [2, 4, 2, 2, 2, 2, 2, 3]
def baseStart_335508 : Nat := 118140960795 + 335508 * 2 ^ 59
def prefixEnd_335508 : Nat := 4983230072969 + 3 ^ 40 * 335508 * 2
def baseEnd_335508 : Nat := 102089995513350256063427

theorem tailTrace_335508 : CollatzResearch.WordTrace tailWord_335508 prefixEnd_335508 102089995513350256063427 := by
  unfold tailWord_335508
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118491034259645524803589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8157988045679527366404785 6118491034259645524803589)
  ·
    refine ⟨1147217068923683535900673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6118491034259645524803589 1147217068923683535900673)
    ·
      refine ⟨860412801692762651925505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1147217068923683535900673 860412801692762651925505)
      ·
        refine ⟨645309601269571988944129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 860412801692762651925505 645309601269571988944129)
        ·
          refine ⟨483982200952178991708097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645309601269571988944129 483982200952178991708097)
          ·
            refine ⟨362986650714134243781073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483982200952178991708097 362986650714134243781073)
            ·
              refine ⟨272239988035600682835805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362986650714134243781073 272239988035600682835805)
              ·
                refine ⟨102089995513350256063427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272239988035600682835805 102089995513350256063427)
                ·
                  rfl

theorem cell19_335508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_335508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335508 prefixEnd_335508 := by exact prefixLift 335508
  have htrace : WordTrace (prefixWord ++ tailWord_335508) baseStart_335508 baseEnd_335508 := by
    simpa [prefixWord, tailWord_335508, baseEnd_335508] using wordTrace_append hprefix tailTrace_335508
  have hstable : (prefixWord ++ tailWord_335508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335508).length < 2 ^ (prefixWord ++ tailWord_335508).sum := by decide
  have hdescent : baseEnd_335508 < baseStart_335508 := by decide
  rcases family_descends (prefixWord ++ tailWord_335508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335512 : List Nat := [2, 1, 2, 4, 1, 2, 4, 3]
def baseStart_335512 : Nat := 118140960795 + 335512 * 2 ^ 59
def prefixEnd_335512 : Nat := 4983230072969 + 3 ^ 40 * 335512 * 2
def baseEnd_335512 : Nat := 102091212652679431974527

theorem tailTrace_335512 : CollatzResearch.WordTrace tailWord_335512 prefixEnd_335512 102091212652679431974527 := by
  unfold tailWord_335512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118563980252399866376395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8158085307003199821835193 6118563980252399866376395)
  ·
    refine ⟨9177845970378599799564593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6118563980252399866376395 9177845970378599799564593)
    ·
      refine ⟨6883384477783949849673445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9177845970378599799564593 6883384477783949849673445)
      ·
        refine ⟨1290634589584490596813771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6883384477783949849673445 1290634589584490596813771)
        ·
          refine ⟨1935951884376735895220657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290634589584490596813771 1935951884376735895220657)
          ·
            refine ⟨1451963913282551921415493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935951884376735895220657 1451963913282551921415493)
            ·
              refine ⟨272243233740478485265405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1451963913282551921415493 272243233740478485265405)
              ·
                refine ⟨102091212652679431974527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272243233740478485265405 102091212652679431974527)
                ·
                  rfl

theorem cell19_335512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_335512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335512 prefixEnd_335512 := by exact prefixLift 335512
  have htrace : WordTrace (prefixWord ++ tailWord_335512) baseStart_335512 baseEnd_335512 := by
    simpa [prefixWord, tailWord_335512, baseEnd_335512] using wordTrace_append hprefix tailTrace_335512
  have hstable : (prefixWord ++ tailWord_335512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335512).length < 2 ^ (prefixWord ++ tailWord_335512).sum := by decide
  have hdescent : baseEnd_335512 < baseStart_335512 := by decide
  rcases family_descends (prefixWord ++ tailWord_335512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335550 : List Nat := [4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_335550 : Nat := 118140960795 + 335550 * 2 ^ 59
def prefixEnd_335550 : Nat := 4983230072969 + 3 ^ 40 * 335550 * 2
def baseEnd_335550 : Nat := 102102775476306603129979

theorem tailTrace_335550 : CollatzResearch.WordTrace tailWord_335550 prefixEnd_335550 102102775476306603129979 := by
  unfold tailWord_335550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529814241795891527829513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8159009289578088148424069 1529814241795891527829513)
  ·
    refine ⟨1147360681346918645872135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1529814241795891527829513 1147360681346918645872135)
    ·
      refine ⟨1721041022020377968808203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147360681346918645872135 1721041022020377968808203)
      ·
        refine ⟨2581561533030566953212305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721041022020377968808203 2581561533030566953212305)
        ·
          refine ⟨1936171149772925214909229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2581561533030566953212305 1936171149772925214909229)
          ·
            refine ⟨726064181164846955590961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1936171149772925214909229 726064181164846955590961)
            ·
              refine ⟨544548135873635216693221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726064181164846955590961 544548135873635216693221)
              ·
                refine ⟨102102775476306603129979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544548135873635216693221 102102775476306603129979)
                ·
                  rfl

theorem cell19_335550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_335550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335550 prefixEnd_335550 := by exact prefixLift 335550
  have htrace : WordTrace (prefixWord ++ tailWord_335550) baseStart_335550 baseEnd_335550 := by
    simpa [prefixWord, tailWord_335550, baseEnd_335550] using wordTrace_append hprefix tailTrace_335550
  have hstable : (prefixWord ++ tailWord_335550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335550).length < 2 ^ (prefixWord ++ tailWord_335550).sum := by decide
  have hdescent : baseEnd_335550 < baseStart_335550 := by decide
  rcases family_descends (prefixWord ++ tailWord_335550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335552 : List Nat := [2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_335552 : Nat := 118140960795 + 335552 * 2 ^ 59
def prefixEnd_335552 : Nat := 4983230072969 + 3 ^ 40 * 335552 * 2
def baseEnd_335552 : Nat := 102103384045971191085529

theorem tailTrace_335552 : CollatzResearch.WordTrace tailWord_335552 prefixEnd_335552 102103384045971191085529 := by
  unfold tailWord_335552
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119293440179943282104455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8159057920239924376139273 6119293440179943282104455)
  ·
    refine ⟨9178940160269914923156683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6119293440179943282104455 9178940160269914923156683)
    ·
      refine ⟨13768410240404872384735025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9178940160269914923156683 13768410240404872384735025)
      ·
        refine ⟨10326307680303654288551269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13768410240404872384735025 10326307680303654288551269)
        ·
          refine ⟨1936182690056935179103363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10326307680303654288551269 1936182690056935179103363)
          ·
            refine ⟨2904274035085402768655045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936182690056935179103363 2904274035085402768655045)
            ·
              refine ⟨544551381578513019122821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2904274035085402768655045 544551381578513019122821)
              ·
                refine ⟨102103384045971191085529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544551381578513019122821 102103384045971191085529)
                ·
                  rfl

theorem cell19_335552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_335552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335552 prefixEnd_335552 := by exact prefixLift 335552
  have htrace : WordTrace (prefixWord ++ tailWord_335552) baseStart_335552 baseEnd_335552 := by
    simpa [prefixWord, tailWord_335552, baseEnd_335552] using wordTrace_append hprefix tailTrace_335552
  have hstable : (prefixWord ++ tailWord_335552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335552).length < 2 ^ (prefixWord ++ tailWord_335552).sum := by decide
  have hdescent : baseEnd_335552 < baseStart_335552 := by decide
  rcases family_descends (prefixWord ++ tailWord_335552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335611 : List Nat := [1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_335611 : Nat := 118140960795 + 335611 * 2 ^ 59
def prefixEnd_335611 : Nat := 4983230072969 + 3 ^ 40 * 335611 * 2
def baseEnd_335611 : Nat := 102121336851076535774257

theorem tailTrace_335611 : CollatzResearch.WordTrace tailWord_335611 prefixEnd_335611 102121336851076535774257 := by
  unfold tailWord_335611
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240738787146139640606687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8160492524764093093737791 12240738787146139640606687)
  ·
    refine ⟨18361108180719209460910031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12240738787146139640606687 18361108180719209460910031)
    ·
      refine ⟨27541662271078814191365047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18361108180719209460910031 27541662271078814191365047)
      ·
        refine ⟨41312493406618221287047571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27541662271078814191365047 41312493406618221287047571)
        ·
          refine ⟨61968740109927331930571357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41312493406618221287047571 61968740109927331930571357)
          ·
            refine ⟨23238277541222749473964259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61968740109927331930571357 23238277541222749473964259)
            ·
              refine ⟨34857416311834124210946389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23238277541222749473964259 34857416311834124210946389)
              ·
                refine ⟨102121336851076535774257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34857416311834124210946389 102121336851076535774257)
                ·
                  rfl

theorem cell19_335611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_335611 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335611 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335611 prefixEnd_335611 := by exact prefixLift 335611
  have htrace : WordTrace (prefixWord ++ tailWord_335611) baseStart_335611 baseEnd_335611 := by
    simpa [prefixWord, tailWord_335611, baseEnd_335611] using wordTrace_append hprefix tailTrace_335611
  have hstable : (prefixWord ++ tailWord_335611).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335611).length < 2 ^ (prefixWord ++ tailWord_335611).sum := by decide
  have hdescent : baseEnd_335611 < baseStart_335611 := by decide
  rcases family_descends (prefixWord ++ tailWord_335611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335626 : List Nat := [3, 1, 2, 2, 1, 4, 3, 3]
def baseStart_335626 : Nat := 118140960795 + 335626 * 2 ^ 59
def prefixEnd_335626 : Nat := 4983230072969 + 3 ^ 40 * 335626 * 2
def baseEnd_335626 : Nat := 102125901123560945440883

theorem tailTrace_335626 : CollatzResearch.WordTrace tailWord_335626 prefixEnd_335626 102125901123560945440883 := by
  unfold tailWord_335626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060321470522949300600683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8160857254727864801601821 3060321470522949300600683)
  ·
    refine ⟨4590482205784423950901025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3060321470522949300600683 4590482205784423950901025)
    ·
      refine ⟨3442861654338317963175769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4590482205784423950901025 3442861654338317963175769)
      ·
        refine ⟨2582146240753738472381827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3442861654338317963175769 2582146240753738472381827)
        ·
          refine ⟨3873219361130607708572741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582146240753738472381827 3873219361130607708572741)
          ·
            refine ⟨726228630211988945357389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3873219361130607708572741 726228630211988945357389)
            ·
              refine ⟨272335736329495854509021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726228630211988945357389 272335736329495854509021)
              ·
                refine ⟨102125901123560945440883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272335736329495854509021 102125901123560945440883)
                ·
                  rfl

theorem cell19_335626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_335626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335626 prefixEnd_335626 := by exact prefixLift 335626
  have htrace : WordTrace (prefixWord ++ tailWord_335626) baseStart_335626 baseEnd_335626 := by
    simpa [prefixWord, tailWord_335626, baseEnd_335626] using wordTrace_append hprefix tailTrace_335626
  have hstable : (prefixWord ++ tailWord_335626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335626).length < 2 ^ (prefixWord ++ tailWord_335626).sum := by decide
  have hdescent : baseEnd_335626 < baseStart_335626 := by decide
  rcases family_descends (prefixWord ++ tailWord_335626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335683 : List Nat := [1, 1, 1, 3, 1, 7, 2, 3]
def baseStart_335683 : Nat := 118140960795 + 335683 * 2 ^ 59
def prefixEnd_335683 : Nat := 4983230072969 + 3 ^ 40 * 335683 * 2
def baseEnd_335683 : Nat := 102143245359001702174061

theorem tailTrace_335683 : CollatzResearch.WordTrace tailWord_335683 prefixEnd_335683 102143245359001702174061 := by
  unfold tailWord_335683
  simp only [CollatzResearch.WordTrace]
  refine ⟨12243364842885295937227703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8162243228590197291485135 12243364842885295937227703)
  ·
    refine ⟨18365047264327943905841555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12243364842885295937227703 18365047264327943905841555)
    ·
      refine ⟨27547570896491915858762333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18365047264327943905841555 27547570896491915858762333)
      ·
        refine ⟨10330339086184468447035875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27547570896491915858762333 10330339086184468447035875)
        ·
          refine ⟨15495508629276702670553813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330339086184468447035875 15495508629276702670553813)
          ·
            refine ⟨363175983498672718841105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15495508629276702670553813 363175983498672718841105)
            ·
              refine ⟨272381987624004539130829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363175983498672718841105 272381987624004539130829)
              ·
                refine ⟨102143245359001702174061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272381987624004539130829 102143245359001702174061)
                ·
                  rfl

theorem cell19_335683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_335683 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335683 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335683 prefixEnd_335683 := by exact prefixLift 335683
  have htrace : WordTrace (prefixWord ++ tailWord_335683) baseStart_335683 baseEnd_335683 := by
    simpa [prefixWord, tailWord_335683, baseEnd_335683] using wordTrace_append hprefix tailTrace_335683
  have hstable : (prefixWord ++ tailWord_335683).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335683).length < 2 ^ (prefixWord ++ tailWord_335683).sum := by decide
  have hdescent : baseEnd_335683 < baseStart_335683 := by decide
  rcases family_descends (prefixWord ++ tailWord_335683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335744 : List Nat := [2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_335744 : Nat := 118140960795 + 335744 * 2 ^ 59
def prefixEnd_335744 : Nat := 4983230072969 + 3 ^ 40 * 335744 * 2
def baseEnd_335744 : Nat := 102161806733771634818339

theorem tailTrace_335744 : CollatzResearch.WordTrace tailWord_335744 prefixEnd_335744 102161806733771634818339 := by
  unfold tailWord_335744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122794847832151677599143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8163726463776202236798857 6122794847832151677599143)
  ·
    refine ⟨9184192271748227516398715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6122794847832151677599143 9184192271748227516398715)
    ·
      refine ⟨13776288407622341274598073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9184192271748227516398715 13776288407622341274598073)
      ·
        refine ⟨10332216305716755955948555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13776288407622341274598073 10332216305716755955948555)
        ·
          refine ⟨15498324458575133933922833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10332216305716755955948555 15498324458575133933922833)
          ·
            refine ⟨11623743343931350450442125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15498324458575133933922833 11623743343931350450442125)
            ·
              refine ⟨4358903753974256418915797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11623743343931350450442125 4358903753974256418915797)
              ·
                refine ⟨102161806733771634818339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4358903753974256418915797 102161806733771634818339)
                ·
                  rfl

theorem cell19_335744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_335744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335744 prefixEnd_335744 := by exact prefixLift 335744
  have htrace : WordTrace (prefixWord ++ tailWord_335744) baseStart_335744 baseEnd_335744 := by
    simpa [prefixWord, tailWord_335744, baseEnd_335744] using wordTrace_append hprefix tailTrace_335744
  have hstable : (prefixWord ++ tailWord_335744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335744).length < 2 ^ (prefixWord ++ tailWord_335744).sum := by decide
  have hdescent : baseEnd_335744 < baseStart_335744 := by decide
  rcases family_descends (prefixWord ++ tailWord_335744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335774 : List Nat := [4, 3, 1, 3, 1, 2, 1, 4]
def baseStart_335774 : Nat := 118140960795 + 335774 * 2 ^ 59
def prefixEnd_335774 : Nat := 4983230072969 + 3 ^ 40 * 335774 * 2
def baseEnd_335774 : Nat := 102170935278740454151591

theorem tailTrace_335774 : CollatzResearch.WordTrace tailWord_335774 prefixEnd_335774 102170935278740454151591 := by
  unfold tailWord_335774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530835485694452309848797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8164455923703745652526917 1530835485694452309848797)
  ·
    refine ⟨574063307135419616193299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1530835485694452309848797 574063307135419616193299)
    ·
      refine ⟨861094960703129424289949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574063307135419616193299 861094960703129424289949)
      ·
        refine ⟨322910610263673534108731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 861094960703129424289949 322910610263673534108731)
        ·
          refine ⟨484365915395510301163097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322910610263673534108731 484365915395510301163097)
          ·
            refine ⟨363274436546632725872323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484365915395510301163097 363274436546632725872323)
            ·
              refine ⟨544911654819949088808485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363274436546632725872323 544911654819949088808485)
              ·
                refine ⟨102170935278740454151591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544911654819949088808485 102170935278740454151591)
                ·
                  rfl

theorem cell19_335774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_335774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335774 prefixEnd_335774 := by exact prefixLift 335774
  have htrace : WordTrace (prefixWord ++ tailWord_335774) baseStart_335774 baseEnd_335774 := by
    simpa [prefixWord, tailWord_335774, baseEnd_335774] using wordTrace_append hprefix tailTrace_335774
  have hstable : (prefixWord ++ tailWord_335774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335774).length < 2 ^ (prefixWord ++ tailWord_335774).sum := by decide
  have hdescent : baseEnd_335774 < baseStart_335774 := by decide
  rcases family_descends (prefixWord ++ tailWord_335774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335780 : List Nat := [2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_335780 : Nat := 118140960795 + 335780 * 2 ^ 59
def prefixEnd_335780 : Nat := 4983230072969 + 3 ^ 40 * 335780 * 2
def baseEnd_335780 : Nat := 102172760987734218018241

theorem tailTrace_335780 : CollatzResearch.WordTrace tailWord_335780 prefixEnd_335780 102172760987734218018241 := by
  unfold tailWord_335780
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123451361766940751754397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8164601815689254335672529 6123451361766940751754397)
  ·
    refine ⟨2296294260662602781907899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6123451361766940751754397 2296294260662602781907899)
    ·
      refine ⟨3444441390993904172861849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2296294260662602781907899 3444441390993904172861849)
      ·
        refine ⟨2583331043245428129646387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3444441390993904172861849 2583331043245428129646387)
        ·
          refine ⟨3874996564868142194469581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583331043245428129646387 3874996564868142194469581)
          ·
            refine ⟨1453123711825553322926093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3874996564868142194469581 1453123711825553322926093)
            ·
              refine ⟨544921391934582496097285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1453123711825553322926093 544921391934582496097285)
              ·
                refine ⟨102172760987734218018241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544921391934582496097285 102172760987734218018241)
                ·
                  rfl

theorem cell19_335780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_335780 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335780 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335780 prefixEnd_335780 := by exact prefixLift 335780
  have htrace : WordTrace (prefixWord ++ tailWord_335780) baseStart_335780 baseEnd_335780 := by
    simpa [prefixWord, tailWord_335780, baseEnd_335780] using wordTrace_append hprefix tailTrace_335780
  have hstable : (prefixWord ++ tailWord_335780).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335780).length < 2 ^ (prefixWord ++ tailWord_335780).sum := by decide
  have hdescent : baseEnd_335780 < baseStart_335780 := by decide
  rcases family_descends (prefixWord ++ tailWord_335780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335797 : List Nat := [1, 3, 3, 2, 1, 3, 3, 3]
def baseStart_335797 : Nat := 118140960795 + 335797 * 2 ^ 59
def prefixEnd_335797 : Nat := 4983230072969 + 3 ^ 40 * 335797 * 2
def baseEnd_335797 : Nat := 102177933829883215640417

theorem tailTrace_335797 : CollatzResearch.WordTrace tailWord_335797 prefixEnd_335797 102177933829883215640417 := by
  unfold tailWord_335797
  simp only [CollatzResearch.WordTrace]
  refine ⟨12247522764472293406877645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8165015176314862271251763 12247522764472293406877645)
  ·
    refine ⟨4592821036677110027579117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12247522764472293406877645 4592821036677110027579117)
    ·
      refine ⟨1722307888753916260342169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4592821036677110027579117 1722307888753916260342169)
      ·
        refine ⟨1291730916565437195256627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1722307888753916260342169 1291730916565437195256627)
        ·
          refine ⟨1937596374848155792884941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291730916565437195256627 1937596374848155792884941)
          ·
            refine ⟨726598640568058422331853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1937596374848155792884941 726598640568058422331853)
            ·
              refine ⟨272474490213021908374445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726598640568058422331853 272474490213021908374445)
              ·
                refine ⟨102177933829883215640417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272474490213021908374445 102177933829883215640417)
                ·
                  rfl

theorem cell19_335797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_335797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335797 prefixEnd_335797 := by exact prefixLift 335797
  have htrace : WordTrace (prefixWord ++ tailWord_335797) baseStart_335797 baseEnd_335797 := by
    simpa [prefixWord, tailWord_335797, baseEnd_335797] using wordTrace_append hprefix tailTrace_335797
  have hstable : (prefixWord ++ tailWord_335797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335797).length < 2 ^ (prefixWord ++ tailWord_335797).sum := by decide
  have hdescent : baseEnd_335797 < baseStart_335797 := by decide
  rcases family_descends (prefixWord ++ tailWord_335797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335854 : List Nat := [4, 1, 2, 1, 3, 1, 4, 3]
def baseStart_335854 : Nat := 118140960795 + 335854 * 2 ^ 59
def prefixEnd_335854 : Nat := 4983230072969 + 3 ^ 40 * 335854 * 2
def baseEnd_335854 : Nat := 102195278065323972373595

theorem tailTrace_335854 : CollatzResearch.WordTrace tailWord_335854 prefixEnd_335854 102195278065323972373595 := by
  unfold tailWord_335854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531200215658224017712827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8166401150177194761135077 1531200215658224017712827)
  ·
    refine ⟨2296800323487336026569241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1531200215658224017712827 2296800323487336026569241)
    ·
      refine ⟨1722600242615502019926931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2296800323487336026569241 1722600242615502019926931)
      ·
        refine ⟨2583900363923253029890397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1722600242615502019926931 2583900363923253029890397)
        ·
          refine ⟨968962636471219886208899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2583900363923253029890397 968962636471219886208899)
          ·
            refine ⟨1453443954706829829313349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968962636471219886208899 1453443954706829829313349)
            ·
              refine ⟨272520741507530592996253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1453443954706829829313349 272520741507530592996253)
              ·
                refine ⟨102195278065323972373595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272520741507530592996253 102195278065323972373595)
                ·
                  rfl

theorem cell19_335854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_335854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335854 prefixEnd_335854 := by exact prefixLift 335854
  have htrace : WordTrace (prefixWord ++ tailWord_335854) baseStart_335854 baseEnd_335854 := by
    simpa [prefixWord, tailWord_335854, baseEnd_335854] using wordTrace_append hprefix tailTrace_335854
  have hstable : (prefixWord ++ tailWord_335854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335854).length < 2 ^ (prefixWord ++ tailWord_335854).sum := by decide
  have hdescent : baseEnd_335854 < baseStart_335854 := by decide
  rcases family_descends (prefixWord ++ tailWord_335854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335856 : List Nat := [2, 1, 1, 1, 3, 2, 6, 3]
def baseStart_335856 : Nat := 118140960795 + 335856 * 2 ^ 59
def prefixEnd_335856 : Nat := 4983230072969 + 3 ^ 40 * 335856 * 2
def baseEnd_335856 : Nat := 102195886634988560329145

theorem tailTrace_335856 : CollatzResearch.WordTrace tailWord_335856 prefixEnd_335856 102195886634988560329145 := by
  unfold tailWord_335856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124837335629273241637711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8166449780839030988850281 6124837335629273241637711)
  ·
    refine ⟨9187256003443909862456567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6124837335629273241637711 9187256003443909862456567)
    ·
      refine ⟨13780884005165864793684851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9187256003443909862456567 13780884005165864793684851)
      ·
        refine ⟨20671326007748797190527277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13780884005165864793684851 20671326007748797190527277)
        ·
          refine ⟨7751747252905798946447729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20671326007748797190527277 7751747252905798946447729)
          ·
            refine ⟨5813810439679349209835797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7751747252905798946447729 5813810439679349209835797)
            ·
              refine ⟨272522364359969494211053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5813810439679349209835797 272522364359969494211053)
              ·
                refine ⟨102195886634988560329145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272522364359969494211053 102195886634988560329145)
                ·
                  rfl

theorem cell19_335856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_335856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335856 prefixEnd_335856 := by exact prefixLift 335856
  have htrace : WordTrace (prefixWord ++ tailWord_335856) baseStart_335856 baseEnd_335856 := by
    simpa [prefixWord, tailWord_335856, baseEnd_335856] using wordTrace_append hprefix tailTrace_335856
  have hstable : (prefixWord ++ tailWord_335856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335856).length < 2 ^ (prefixWord ++ tailWord_335856).sum := by decide
  have hdescent : baseEnd_335856 < baseStart_335856 := by decide
  rcases family_descends (prefixWord ++ tailWord_335856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335877 : List Nat := [1, 3, 1, 1, 2, 4, 7]
def baseStart_335877 : Nat := 118140960795 + 335877 * 2 ^ 59
def prefixEnd_335877 : Nat := 4983230072969 + 3 ^ 40 * 335877 * 2
def baseEnd_335877 : Nat := 34067425538822244620807

theorem tailTrace_335877 : CollatzResearch.WordTrace tailWord_335877 prefixEnd_335877 34067425538822244620807 := by
  unfold tailWord_335877
  simp only [CollatzResearch.WordTrace]
  refine ⟨12250440604182467069789885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8166960402788311379859923 12250440604182467069789885)
  ·
    refine ⟨4593915226568425151171207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12250440604182467069789885 4593915226568425151171207)
    ·
      refine ⟨6890872839852637726756811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4593915226568425151171207 6890872839852637726756811)
      ·
        refine ⟨10336309259778956590135217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6890872839852637726756811 10336309259778956590135217)
        ·
          refine ⟨7752231944834217442601413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10336309259778956590135217 7752231944834217442601413)
          ·
            refine ⟨1453543489656415770487765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7752231944834217442601413 1453543489656415770487765)
            ·
              refine ⟨34067425538822244620807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1453543489656415770487765 34067425538822244620807)
              ·
                rfl

theorem cell19_335877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_335877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335877 prefixEnd_335877 := by exact prefixLift 335877
  have htrace : WordTrace (prefixWord ++ tailWord_335877) baseStart_335877 baseEnd_335877 := by
    simpa [prefixWord, tailWord_335877, baseEnd_335877] using wordTrace_append hprefix tailTrace_335877
  have hstable : (prefixWord ++ tailWord_335877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335877).length < 2 ^ (prefixWord ++ tailWord_335877).sum := by decide
  have hdescent : baseEnd_335877 < baseStart_335877 := by decide
  rcases family_descends (prefixWord ++ tailWord_335877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335972 : List Nat := [2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_335972 : Nat := 118140960795 + 335972 * 2 ^ 59
def prefixEnd_335972 : Nat := 4983230072969 + 3 ^ 40 * 335972 * 2
def baseEnd_335972 : Nat := 102231183675534661751051

theorem tailTrace_335972 : CollatzResearch.WordTrace tailWord_335972 prefixEnd_335972 102231183675534661751051 := by
  unfold tailWord_335972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6126952769419149147249085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8169270359225532196332113 6126952769419149147249085)
  ·
    refine ⟨2297607288532180930218407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6126952769419149147249085 2297607288532180930218407)
    ·
      refine ⟨3446410932798271395327611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2297607288532180930218407 3446410932798271395327611)
      ·
        refine ⟨5169616399197407092991417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446410932798271395327611 5169616399197407092991417)
        ·
          refine ⟨3877212299398055319743563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5169616399197407092991417 3877212299398055319743563)
          ·
            refine ⟨5815818449097082979615345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877212299398055319743563 5815818449097082979615345)
            ·
              refine ⟨4361863836822812234711509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5815818449097082979615345 4361863836822812234711509)
              ·
                refine ⟨102231183675534661751051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4361863836822812234711509 102231183675534661751051)
                ·
                  rfl

theorem cell19_335972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_335972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335972 prefixEnd_335972 := by exact prefixLift 335972
  have htrace : WordTrace (prefixWord ++ tailWord_335972) baseStart_335972 baseEnd_335972 := by
    simpa [prefixWord, tailWord_335972, baseEnd_335972] using wordTrace_append hprefix tailTrace_335972
  have hstable : (prefixWord ++ tailWord_335972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335972).length < 2 ^ (prefixWord ++ tailWord_335972).sum := by decide
  have hdescent : baseEnd_335972 < baseStart_335972 := by decide
  rcases family_descends (prefixWord ++ tailWord_335972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335991 : List Nat := [1, 1, 3, 1, 1, 6, 6]
def baseStart_335991 : Nat := 118140960795 + 335991 * 2 ^ 59
def prefixEnd_335991 : Nat := 4983230072969 + 3 ^ 40 * 335991 * 2
def baseEnd_335991 : Nat := 34078988362449415776259

theorem tailTrace_335991 : CollatzResearch.WordTrace tailWord_335991 prefixEnd_335991 34078988362449415776259 := by
  unfold tailWord_335991
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254598525769464539439827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8169732350512976359626551 12254598525769464539439827)
  ·
    refine ⟨18381897788654196809159741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12254598525769464539439827 18381897788654196809159741)
    ·
      refine ⟨6893211670745323803434903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18381897788654196809159741 6893211670745323803434903)
      ·
        refine ⟨10339817506117985705152355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6893211670745323803434903 10339817506117985705152355)
        ·
          refine ⟨15509726259176978557728533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10339817506117985705152355 15509726259176978557728533)
          ·
            refine ⟨727018418398920869893525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15509726259176978557728533 727018418398920869893525)
            ·
              refine ⟨34078988362449415776259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 727018418398920869893525 34078988362449415776259)
              ·
                rfl

theorem cell19_335991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_335991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_335991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_335991 prefixEnd_335991 := by exact prefixLift 335991
  have htrace : WordTrace (prefixWord ++ tailWord_335991) baseStart_335991 baseEnd_335991 := by
    simpa [prefixWord, tailWord_335991, baseEnd_335991] using wordTrace_append hprefix tailTrace_335991
  have hstable : (prefixWord ++ tailWord_335991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335991).length < 2 ^ (prefixWord ++ tailWord_335991).sum := by decide
  have hdescent : baseEnd_335991 < baseStart_335991 := by decide
  rcases family_descends (prefixWord ++ tailWord_335991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336023 : List Nat := [1, 1, 3, 3, 5, 1, 2, 3]
def baseStart_336023 : Nat := 118140960795 + 336023 * 2 ^ 59
def prefixEnd_336023 : Nat := 4983230072969 + 3 ^ 40 * 336023 * 2
def baseEnd_336023 : Nat := 102246702201981654617579

theorem tailTrace_336023 : CollatzResearch.WordTrace tailWord_336023 prefixEnd_336023 102246702201981654617579 := by
  unfold tailWord_336023
  simp only [CollatzResearch.WordTrace]
  refine ⟨12255765661653534004604723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8170510441102356003069815 12255765661653534004604723)
  ·
    refine ⟨18383648492480301006907085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12255765661653534004604723 18383648492480301006907085)
    ·
      refine ⟨6893868184680112877590157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18383648492480301006907085 6893868184680112877590157)
      ·
        refine ⟨2585200569255042329096309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6893868184680112877590157 2585200569255042329096309)
        ·
          refine ⟨242362553367660218352779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2585200569255042329096309 242362553367660218352779)
          ·
            refine ⟨363543830051490327529169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242362553367660218352779 363543830051490327529169)
            ·
              refine ⟨272657872538617745646877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363543830051490327529169 272657872538617745646877)
              ·
                refine ⟨102246702201981654617579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272657872538617745646877 102246702201981654617579)
                ·
                  rfl

theorem cell19_336023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 3].length) (baseStart_336023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336023 prefixEnd_336023 := by exact prefixLift 336023
  have htrace : WordTrace (prefixWord ++ tailWord_336023) baseStart_336023 baseEnd_336023 := by
    simpa [prefixWord, tailWord_336023, baseEnd_336023] using wordTrace_append hprefix tailTrace_336023
  have hstable : (prefixWord ++ tailWord_336023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336023).length < 2 ^ (prefixWord ++ tailWord_336023).sum := by decide
  have hdescent : baseEnd_336023 < baseStart_336023 := by decide
  rcases family_descends (prefixWord ++ tailWord_336023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336042 : List Nat := [3, 1, 5, 1, 3, 1, 5]
def baseStart_336042 : Nat := 118140960795 + 336042 * 2 ^ 59
def prefixEnd_336042 : Nat := 4983230072969 + 3 ^ 40 * 336042 * 2
def baseEnd_336042 : Nat := 34084161204598413398435

theorem tailTrace_336042 : CollatzResearch.WordTrace tailWord_336042 prefixEnd_336042 34084161204598413398435 := by
  unfold tailWord_336042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064114662146175062386595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8170972432389800166364253 3064114662146175062386595)
  ·
    refine ⟨4596171993219262593579893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3064114662146175062386595 4596171993219262593579893)
    ·
      refine ⟨430891124364305868148115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4596171993219262593579893 430891124364305868148115)
      ·
        refine ⟨646336686546458802222173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430891124364305868148115 646336686546458802222173)
        ·
          refine ⟨242376257454922050833315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 646336686546458802222173 242376257454922050833315)
          ·
            refine ⟨363564386182383076249973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242376257454922050833315 363564386182383076249973)
            ·
              refine ⟨34084161204598413398435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 363564386182383076249973 34084161204598413398435)
              ·
                rfl

theorem cell19_336042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_336042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336042 prefixEnd_336042 := by exact prefixLift 336042
  have htrace : WordTrace (prefixWord ++ tailWord_336042) baseStart_336042 baseEnd_336042 := by
    simpa [prefixWord, tailWord_336042, baseEnd_336042] using wordTrace_append hprefix tailTrace_336042
  have hstable : (prefixWord ++ tailWord_336042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336042).length < 2 ^ (prefixWord ++ tailWord_336042).sum := by decide
  have hdescent : baseEnd_336042 < baseStart_336042 := by decide
  rcases family_descends (prefixWord ++ tailWord_336042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336122 : List Nat := [3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_336122 : Nat := 118140960795 + 336122 * 2 ^ 59
def prefixEnd_336122 : Nat := 4983230072969 + 3 ^ 40 * 336122 * 2
def baseEnd_336122 : Nat := 102276826400378758417309

theorem tailTrace_336122 : CollatzResearch.WordTrace tailWord_336122 prefixEnd_336122 102276826400378758417309 := by
  unfold tailWord_336122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064844122073718478114655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8172917658863249274972413 3064844122073718478114655)
  ·
    refine ⟨4597266183110577717171983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3064844122073718478114655 4597266183110577717171983)
    ·
      refine ⟨6895899274665866575757975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4597266183110577717171983 6895899274665866575757975)
      ·
        refine ⟨10343848911998799863636963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6895899274665866575757975 10343848911998799863636963)
        ·
          refine ⟨15515773367998199795455445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10343848911998799863636963 15515773367998199795455445)
          ·
            refine ⟨363650938312457807705987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15515773367998199795455445 363650938312457807705987)
            ·
              refine ⟨545476407468686711558981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363650938312457807705987 545476407468686711558981)
              ·
                refine ⟨102276826400378758417309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545476407468686711558981 102276826400378758417309)
                ·
                  rfl

theorem cell19_336122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_336122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336122 prefixEnd_336122 := by exact prefixLift 336122
  have htrace : WordTrace (prefixWord ++ tailWord_336122) baseStart_336122 baseEnd_336122 := by
    simpa [prefixWord, tailWord_336122, baseEnd_336122] using wordTrace_append hprefix tailTrace_336122
  have hstable : (prefixWord ++ tailWord_336122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336122).length < 2 ^ (prefixWord ++ tailWord_336122).sum := by decide
  have hdescent : baseEnd_336122 < baseStart_336122 := by decide
  rcases family_descends (prefixWord ++ tailWord_336122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336158 : List Nat := [4, 3, 2, 1, 1, 2, 6]
def baseStart_336158 : Nat := 118140960795 + 336158 * 2 ^ 59
def prefixEnd_336158 : Nat := 4983230072969 + 3 ^ 40 * 336158 * 2
def baseEnd_336158 : Nat := 34095926884780447205737

theorem tailTrace_336158 : CollatzResearch.WordTrace tailWord_336158 prefixEnd_336158 34095926884780447205737 := by
  unfold tailWord_336158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1532586189520556507596141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8173793010776301373846085 1532586189520556507596141)
  ·
    refine ⟨574719821070208690348553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1532586189520556507596141 574719821070208690348553)
    ·
      refine ⟨431039865802656517761415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 574719821070208690348553 431039865802656517761415)
      ·
        refine ⟨646559798703984776642123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431039865802656517761415 646559798703984776642123)
        ·
          refine ⟨969839698055977164963185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646559798703984776642123 969839698055977164963185)
          ·
            refine ⟨727379773541982873722389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 969839698055977164963185 727379773541982873722389)
            ·
              refine ⟨34095926884780447205737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 727379773541982873722389 34095926884780447205737)
              ·
                rfl

theorem cell19_336158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_336158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336158 prefixEnd_336158 := by exact prefixLift 336158
  have htrace : WordTrace (prefixWord ++ tailWord_336158) baseStart_336158 baseEnd_336158 := by
    simpa [prefixWord, tailWord_336158, baseEnd_336158] using wordTrace_append hprefix tailTrace_336158
  have hstable : (prefixWord ++ tailWord_336158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336158).length < 2 ^ (prefixWord ++ tailWord_336158).sum := by decide
  have hdescent : baseEnd_336158 < baseStart_336158 := by decide
  rcases family_descends (prefixWord ++ tailWord_336158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336181 : List Nat := [1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_336181 : Nat := 118140960795 + 336181 * 2 ^ 59
def prefixEnd_336181 : Nat := 4983230072969 + 3 ^ 40 * 336181 * 2
def baseEnd_336181 : Nat := 102294779205484103106037

theorem tailTrace_336181 : CollatzResearch.WordTrace tailWord_336181 prefixEnd_336181 102294779205484103106037 := by
  unfold tailWord_336181
  simp only [CollatzResearch.WordTrace]
  refine ⟨12261528395081126988856397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8174352263387417992570931 12261528395081126988856397)
  ·
    refine ⟨4598073148155422620821149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12261528395081126988856397 4598073148155422620821149)
    ·
      refine ⟨1724277430558283482807931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4598073148155422620821149 1724277430558283482807931)
      ·
        refine ⟨2586416145837425224211897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724277430558283482807931 2586416145837425224211897)
        ·
          refine ⟨1939812109378068918158923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2586416145837425224211897 1939812109378068918158923)
          ·
            refine ⟨2909718164067103377238385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939812109378068918158923 2909718164067103377238385)
            ·
              refine ⟨2182288623050327532928789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2909718164067103377238385 2182288623050327532928789)
              ·
                refine ⟨102294779205484103106037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2182288623050327532928789 102294779205484103106037)
                ·
                  rfl

theorem cell19_336181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_336181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336181 prefixEnd_336181 := by exact prefixLift 336181
  have htrace : WordTrace (prefixWord ++ tailWord_336181) baseStart_336181 baseEnd_336181 := by
    simpa [prefixWord, tailWord_336181, baseEnd_336181] using wordTrace_append hprefix tailTrace_336181
  have hstable : (prefixWord ++ tailWord_336181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336181).length < 2 ^ (prefixWord ++ tailWord_336181).sum := by decide
  have hdescent : baseEnd_336181 < baseStart_336181 := by decide
  rcases family_descends (prefixWord ++ tailWord_336181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336196 : List Nat := [2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_336196 : Nat := 118140960795 + 336196 * 2 ^ 59
def prefixEnd_336196 : Nat := 4983230072969 + 3 ^ 40 * 336196 * 2
def baseEnd_336196 : Nat := 102299343477968512772663

theorem tailTrace_336196 : CollatzResearch.WordTrace tailWord_336196 prefixEnd_336196 102299343477968512772663 := by
  unfold tailWord_336196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131037745013392275326221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8174716993351189700434961 6131037745013392275326221)
  ·
    refine ⟨2299139154380022103247333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6131037745013392275326221 2299139154380022103247333)
    ·
      refine ⟨431088591446254144358875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2299139154380022103247333 431088591446254144358875)
      ·
        refine ⟨646632887169381216538313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431088591446254144358875 646632887169381216538313)
        ·
          refine ⟨484974665377035912403735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646632887169381216538313 484974665377035912403735)
          ·
            refine ⟨727461998065553868605603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484974665377035912403735 727461998065553868605603)
            ·
              refine ⟨1091192997098330802908405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727461998065553868605603 1091192997098330802908405)
              ·
                refine ⟨102299343477968512772663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1091192997098330802908405 102299343477968512772663)
                ·
                  rfl

theorem cell19_336196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_336196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336196 prefixEnd_336196 := by exact prefixLift 336196
  have htrace : WordTrace (prefixWord ++ tailWord_336196) baseStart_336196 baseEnd_336196 := by
    simpa [prefixWord, tailWord_336196, baseEnd_336196] using wordTrace_append hprefix tailTrace_336196
  have hstable : (prefixWord ++ tailWord_336196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336196).length < 2 ^ (prefixWord ++ tailWord_336196).sum := by decide
  have hdescent : baseEnd_336196 < baseStart_336196 := by decide
  rcases family_descends (prefixWord ++ tailWord_336196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336236 : List Nat := [2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_336236 : Nat := 118140960795 + 336236 * 2 ^ 59
def prefixEnd_336236 : Nat := 4983230072969 + 3 ^ 40 * 336236 * 2
def baseEnd_336236 : Nat := 102311514871260271883665

theorem tailTrace_336236 : CollatzResearch.WordTrace tailWord_336236 prefixEnd_336236 102311514871260271883665 := by
  unfold tailWord_336236
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131767204940935691054281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8175689606587914254739041 6131767204940935691054281)
  ·
    refine ⟨4598825403705701768290711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6131767204940935691054281 4598825403705701768290711)
    ·
      refine ⟨6898238105558552652436067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4598825403705701768290711 6898238105558552652436067)
      ·
        refine ⟨10347357158337828978654101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6898238105558552652436067 10347357158337828978654101)
        ·
          refine ⟨485032366797085733374411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10347357158337828978654101 485032366797085733374411)
          ·
            refine ⟨727548550195628600061617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485032366797085733374411 727548550195628600061617)
            ·
              refine ⟨545661412646721450046213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727548550195628600061617 545661412646721450046213)
              ·
                refine ⟨102311514871260271883665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545661412646721450046213 102311514871260271883665)
                ·
                  rfl

theorem cell19_336236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_336236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336236 prefixEnd_336236 := by exact prefixLift 336236
  have htrace : WordTrace (prefixWord ++ tailWord_336236) baseStart_336236 baseEnd_336236 := by
    simpa [prefixWord, tailWord_336236, baseEnd_336236] using wordTrace_append hprefix tailTrace_336236
  have hstable : (prefixWord ++ tailWord_336236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336236).length < 2 ^ (prefixWord ++ tailWord_336236).sum := by decide
  have hdescent : baseEnd_336236 < baseStart_336236 := by decide
  rcases family_descends (prefixWord ++ tailWord_336236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336276 : List Nat := [2, 4, 2, 1, 10]
def baseStart_336276 : Nat := 118140960795 + 336276 * 2 ^ 59
def prefixEnd_336276 : Nat := 4983230072969 + 3 ^ 40 * 336276 * 2
def baseEnd_336276 : Nat := 3789766157946371518321

theorem tailTrace_336276 : CollatzResearch.WordTrace tailWord_336276 prefixEnd_336276 3789766157946371518321 := by
  unfold tailWord_336276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132496664868479106782341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8176662219824638809043121 6132496664868479106782341)
  ·
    refine ⟨1149843124662839832521689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6132496664868479106782341 1149843124662839832521689)
    ·
      refine ⟨862382343497129874391267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1149843124662839832521689 862382343497129874391267)
      ·
        refine ⟨1293573515245694811586901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862382343497129874391267 1293573515245694811586901)
        ·
          refine ⟨3789766157946371518321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1293573515245694811586901 3789766157946371518321)
          ·
            rfl

theorem cell19_336276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 10].length) (baseStart_336276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336276 prefixEnd_336276 := by exact prefixLift 336276
  have htrace : WordTrace (prefixWord ++ tailWord_336276) baseStart_336276 baseEnd_336276 := by
    simpa [prefixWord, tailWord_336276, baseEnd_336276] using wordTrace_append hprefix tailTrace_336276
  have hstable : (prefixWord ++ tailWord_336276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336276).length < 2 ^ (prefixWord ++ tailWord_336276).sum := by decide
  have hdescent : baseEnd_336276 < baseStart_336276 := by decide
  rcases family_descends (prefixWord ++ tailWord_336276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336289 : List Nat := [1, 2, 3, 5, 2, 1, 1, 4]
def baseStart_336289 : Nat := 118140960795 + 336289 * 2 ^ 59
def prefixEnd_336289 : Nat := 4983230072969 + 3 ^ 40 * 336289 * 2
def baseEnd_336289 : Nat := 102327641967371852705743

theorem tailTrace_336289 : CollatzResearch.WordTrace tailWord_336289 prefixEnd_336289 102327641967371852705743 := by
  unfold tailWord_336289
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265467478689861433787921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8176978319126574289191947 12265467478689861433787921)
  ·
    refine ⟨9199100609017396075340941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12265467478689861433787921 9199100609017396075340941)
    ·
      refine ⟨3449662728381523528252853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9199100609017396075340941 3449662728381523528252853)
      ·
        refine ⟨323405880785767830773705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3449662728381523528252853 323405880785767830773705)
        ·
          refine ⟨242554410589325873080279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323405880785767830773705 242554410589325873080279)
          ·
            refine ⟨363831615883988809620419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242554410589325873080279 363831615883988809620419)
            ·
              refine ⟨545747423825983214430629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363831615883988809620419 545747423825983214430629)
              ·
                refine ⟨102327641967371852705743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545747423825983214430629 102327641967371852705743)
                ·
                  rfl

theorem cell19_336289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 4].length) (baseStart_336289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336289 prefixEnd_336289 := by exact prefixLift 336289
  have htrace : WordTrace (prefixWord ++ tailWord_336289) baseStart_336289 baseEnd_336289 := by
    simpa [prefixWord, tailWord_336289, baseEnd_336289] using wordTrace_append hprefix tailTrace_336289
  have hstable : (prefixWord ++ tailWord_336289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336289).length < 2 ^ (prefixWord ++ tailWord_336289).sum := by decide
  have hdescent : baseEnd_336289 < baseStart_336289 := by decide
  rcases family_descends (prefixWord ++ tailWord_336289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336386 : List Nat := [3, 4, 1, 2, 2, 2, 5]
def baseStart_336386 : Nat := 118140960795 + 336386 * 2 ^ 59
def prefixEnd_336386 : Nat := 4983230072969 + 3 ^ 40 * 336386 * 2
def baseEnd_336386 : Nat := 34119052532034789516641

theorem tailTrace_336386 : CollatzResearch.WordTrace tailWord_336386 prefixEnd_336386 34119052532034789516641 := by
  unfold tailWord_336386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067251339834611750017253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8179336906225631333379341 3067251339834611750017253)
  ·
    refine ⟨575109626218989703128235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3067251339834611750017253 575109626218989703128235)
    ·
      refine ⟨862664439328484554692353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575109626218989703128235 862664439328484554692353)
      ·
        refine ⟨646998329496363416019265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 862664439328484554692353 646998329496363416019265)
        ·
          refine ⟨485248747122272562014449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646998329496363416019265 485248747122272562014449)
          ·
            refine ⟨363936560341704421510837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485248747122272562014449 363936560341704421510837)
            ·
              refine ⟨34119052532034789516641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 363936560341704421510837 34119052532034789516641)
              ·
                rfl

theorem cell19_336386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_336386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336386 prefixEnd_336386 := by exact prefixLift 336386
  have htrace : WordTrace (prefixWord ++ tailWord_336386) baseStart_336386 baseEnd_336386 := by
    simpa [prefixWord, tailWord_336386, baseEnd_336386] using wordTrace_append hprefix tailTrace_336386
  have hstable : (prefixWord ++ tailWord_336386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336386).length < 2 ^ (prefixWord ++ tailWord_336386).sum := by decide
  have hdescent : baseEnd_336386 < baseStart_336386 := by decide
  rcases family_descends (prefixWord ++ tailWord_336386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336388 : List Nat := [2, 3, 2, 3, 1, 3, 5]
def baseStart_336388 : Nat := 118140960795 + 336388 * 2 ^ 59
def prefixEnd_336388 : Nat := 4983230072969 + 3 ^ 40 * 336388 * 2
def baseEnd_336388 : Nat := 34119255388589652168491

theorem tailTrace_336388 : CollatzResearch.WordTrace tailWord_336388 prefixEnd_336388 34119255388589652168491 := by
  unfold tailWord_336388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134539152665600670820909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8179385536887467561094545 6134539152665600670820909)
  ·
    refine ⟨2300452182249600251557841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6134539152665600670820909 2300452182249600251557841)
    ·
      refine ⟨1725339136687200188668381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2300452182249600251557841 1725339136687200188668381)
      ·
        refine ⟨647002176257700070750643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1725339136687200188668381 647002176257700070750643)
        ·
          refine ⟨970503264386550106125965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647002176257700070750643 970503264386550106125965)
          ·
            refine ⟨363938724144956289797237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 970503264386550106125965 363938724144956289797237)
            ·
              refine ⟨34119255388589652168491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 363938724144956289797237 34119255388589652168491)
              ·
                rfl

theorem cell19_336388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_336388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336388 prefixEnd_336388 := by exact prefixLift 336388
  have htrace : WordTrace (prefixWord ++ tailWord_336388) baseStart_336388 baseEnd_336388 := by
    simpa [prefixWord, tailWord_336388, baseEnd_336388] using wordTrace_append hprefix tailTrace_336388
  have hstable : (prefixWord ++ tailWord_336388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336388).length < 2 ^ (prefixWord ++ tailWord_336388).sum := by decide
  have hdescent : baseEnd_336388 < baseStart_336388 := by decide
  rcases family_descends (prefixWord ++ tailWord_336388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336502 : List Nat := [5, 1, 1, 2, 3, 1, 6]
def baseStart_336502 : Nat := 118140960795 + 336502 * 2 ^ 59
def prefixEnd_336502 : Nat := 4983230072969 + 3 ^ 40 * 336502 * 2
def baseEnd_336502 : Nat := 34130818212216823323943

theorem tailTrace_336502 : CollatzResearch.WordTrace tailWord_336502 prefixEnd_336502 34130818212216823323943 := by
  unfold tailWord_336502
  simp only [CollatzResearch.WordTrace]
  refine ⟨767077264182387425705735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8182157484612132540861173 767077264182387425705735)
  ·
    refine ⟨1150615896273581138558603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767077264182387425705735 1150615896273581138558603)
    ·
      refine ⟨1725923844410371707837905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150615896273581138558603 1725923844410371707837905)
      ·
        refine ⟨1294442883307778780878429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1725923844410371707837905 1294442883307778780878429)
        ·
          refine ⟨485416081240417042829411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1294442883307778780878429 485416081240417042829411)
          ·
            refine ⟨728124121860625564244117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485416081240417042829411 728124121860625564244117)
            ·
              refine ⟨34130818212216823323943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 728124121860625564244117 34130818212216823323943)
              ·
                rfl

theorem cell19_336502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_336502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336502 prefixEnd_336502 := by exact prefixLift 336502
  have htrace : WordTrace (prefixWord ++ tailWord_336502) baseStart_336502 baseEnd_336502 := by
    simpa [prefixWord, tailWord_336502, baseEnd_336502] using wordTrace_append hprefix tailTrace_336502
  have hstable : (prefixWord ++ tailWord_336502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336502).length < 2 ^ (prefixWord ++ tailWord_336502).sum := by decide
  have hdescent : baseEnd_336502 < baseStart_336502 := by decide
  rcases family_descends (prefixWord ++ tailWord_336502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336540 : List Nat := [2, 2, 3, 2, 2, 1, 4, 3]
def baseStart_336540 : Nat := 118140960795 + 336540 * 2 ^ 59
def prefixEnd_336540 : Nat := 4983230072969 + 3 ^ 40 * 336540 * 2
def baseEnd_336540 : Nat := 102404017460277641127281

theorem tailTrace_336540 : CollatzResearch.WordTrace tailWord_336540 prefixEnd_336540 102404017460277641127281 := by
  unfold tailWord_336540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137311100390265650587537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8183081467187020867450049 6137311100390265650587537)
  ·
    refine ⟨4602983325292699237940653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6137311100390265650587537 4602983325292699237940653)
    ·
      refine ⟨1726118746984762214227745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4602983325292699237940653 1726118746984762214227745)
      ·
        refine ⟨1294589060238571660670809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1726118746984762214227745 1294589060238571660670809)
        ·
          refine ⟨970941795178928745503107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294589060238571660670809 970941795178928745503107)
          ·
            refine ⟨1456412692768393118254661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970941795178928745503107 1456412692768393118254661)
            ·
              refine ⟨273077379894073709672749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1456412692768393118254661 273077379894073709672749)
              ·
                refine ⟨102404017460277641127281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273077379894073709672749 102404017460277641127281)
                ·
                  rfl

theorem cell19_336540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_336540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336540 prefixEnd_336540 := by exact prefixLift 336540
  have htrace : WordTrace (prefixWord ++ tailWord_336540) baseStart_336540 baseEnd_336540 := by
    simpa [prefixWord, tailWord_336540, baseEnd_336540] using wordTrace_append hprefix tailTrace_336540
  have hstable : (prefixWord ++ tailWord_336540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336540).length < 2 ^ (prefixWord ++ tailWord_336540).sum := by decide
  have hdescent : baseEnd_336540 < baseStart_336540 := by decide
  rcases family_descends (prefixWord ++ tailWord_336540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336563 : List Nat := [1, 1, 1, 2, 3, 4, 7]
def baseStart_336563 : Nat := 118140960795 + 336563 * 2 ^ 59
def prefixEnd_336563 : Nat := 4983230072969 + 3 ^ 40 * 336563 * 2
def baseEnd_336563 : Nat := 34137005337140134205369

theorem tailTrace_336563 : CollatzResearch.WordTrace tailWord_336563 prefixEnd_336563 34137005337140134205369 := by
  unfold tailWord_336563
  simp only [CollatzResearch.WordTrace]
  refine ⟨12275461079697206229262343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8183640719798137486174895 12275461079697206229262343)
  ·
    refine ⟨18413191619545809343893515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12275461079697206229262343 18413191619545809343893515)
    ·
      refine ⟨27619787429318714015840273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18413191619545809343893515 27619787429318714015840273)
      ·
        refine ⟨20714840571989035511880205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27619787429318714015840273 20714840571989035511880205)
        ·
          refine ⟨7768065214495888316955077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20714840571989035511880205 7768065214495888316955077)
          ·
            refine ⟨1456512227717979059429077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7768065214495888316955077 1456512227717979059429077)
            ·
              refine ⟨34137005337140134205369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1456512227717979059429077 34137005337140134205369)
              ·
                rfl

theorem cell19_336563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_336563 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336563 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336563 prefixEnd_336563 := by exact prefixLift 336563
  have htrace : WordTrace (prefixWord ++ tailWord_336563) baseStart_336563 baseEnd_336563 := by
    simpa [prefixWord, tailWord_336563, baseEnd_336563] using wordTrace_append hprefix tailTrace_336563
  have hstable : (prefixWord ++ tailWord_336563).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336563).length < 2 ^ (prefixWord ++ tailWord_336563).sum := by decide
  have hdescent : baseEnd_336563 < baseStart_336563 := by decide
  rcases family_descends (prefixWord ++ tailWord_336563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336580 : List Nat := [2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_336580 : Nat := 118140960795 + 336580 * 2 ^ 59
def prefixEnd_336580 : Nat := 4983230072969 + 3 ^ 40 * 336580 * 2
def baseEnd_336580 : Nat := 102416188853569400238283

theorem tailTrace_336580 : CollatzResearch.WordTrace tailWord_336580 prefixEnd_336580 102416188853569400238283 := by
  unfold tailWord_336580
  simp only [CollatzResearch.WordTrace]
  refine ⟨6138040560317809066315597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8184054080423745421754129 6138040560317809066315597)
  ·
    refine ⟨2301765210119178399868349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6138040560317809066315597 2301765210119178399868349)
    ·
      refine ⟨863161953794691899950631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2301765210119178399868349 863161953794691899950631)
      ·
        refine ⟨1294742930692037849925947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863161953794691899950631 1294742930692037849925947)
        ·
          refine ⟨1942114396038056774888921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294742930692037849925947 1942114396038056774888921)
          ·
            refine ⟨1456585797028542581166691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1942114396038056774888921 1456585797028542581166691)
            ·
              refine ⟨2184878695542813871750037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456585797028542581166691 2184878695542813871750037)
              ·
                refine ⟨102416188853569400238283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2184878695542813871750037 102416188853569400238283)
                ·
                  rfl

theorem cell19_336580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_336580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336580 prefixEnd_336580 := by exact prefixLift 336580
  have htrace : WordTrace (prefixWord ++ tailWord_336580) baseStart_336580 baseEnd_336580 := by
    simpa [prefixWord, tailWord_336580, baseEnd_336580] using wordTrace_append hprefix tailTrace_336580
  have hstable : (prefixWord ++ tailWord_336580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336580).length < 2 ^ (prefixWord ++ tailWord_336580).sum := by decide
  have hdescent : baseEnd_336580 < baseStart_336580 := by decide
  rcases family_descends (prefixWord ++ tailWord_336580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336601 : List Nat := [1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_336601 : Nat := 118140960795 + 336601 * 2 ^ 59
def prefixEnd_336601 : Nat := 4983230072969 + 3 ^ 40 * 336601 * 2
def baseEnd_336601 : Nat := 102422578835047573771559

theorem tailTrace_336601 : CollatzResearch.WordTrace tailWord_336601 prefixEnd_336601 102422578835047573771559 := by
  unfold tailWord_336601
  simp only [CollatzResearch.WordTrace]
  refine ⟨12276847053559538719145657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8184564702373025812763771 12276847053559538719145657)
  ·
    refine ⟨9207635290169654039359243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12276847053559538719145657 9207635290169654039359243)
    ·
      refine ⟨13811452935254481059038865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9207635290169654039359243 13811452935254481059038865)
      ·
        refine ⟨10358589701440860794279149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13811452935254481059038865 10358589701440860794279149)
        ·
          refine ⟨3884471138040322797854681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10358589701440860794279149 3884471138040322797854681)
          ·
            refine ⟨2913353353530242098391011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3884471138040322797854681 2913353353530242098391011)
            ·
              refine ⟨4370030030295363147586517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913353353530242098391011 4370030030295363147586517)
              ·
                refine ⟨102422578835047573771559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4370030030295363147586517 102422578835047573771559)
                ·
                  rfl

theorem cell19_336601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_336601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336601 prefixEnd_336601 := by exact prefixLift 336601
  have htrace : WordTrace (prefixWord ++ tailWord_336601) baseStart_336601 baseEnd_336601 := by
    simpa [prefixWord, tailWord_336601, baseEnd_336601] using wordTrace_append hprefix tailTrace_336601
  have hstable : (prefixWord ++ tailWord_336601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336601).length < 2 ^ (prefixWord ++ tailWord_336601).sum := by decide
  have hdescent : baseEnd_336601 < baseStart_336601 := by decide
  rcases family_descends (prefixWord ++ tailWord_336601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336629 : List Nat := [1, 3, 6, 1, 2, 1, 1, 4]
def baseStart_336629 : Nat := 118140960795 + 336629 * 2 ^ 59
def prefixEnd_336629 : Nat := 4983230072969 + 3 ^ 40 * 336629 * 2
def baseEnd_336629 : Nat := 102431098810351805149261

theorem tailTrace_336629 : CollatzResearch.WordTrace tailWord_336629 prefixEnd_336629 102431098810351805149261 := by
  unfold tailWord_336629
  simp only [CollatzResearch.WordTrace]
  refine ⟨12277868297458099501164941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8185245531638733000776627 12277868297458099501164941)
  ·
    refine ⟨4604200611546787312936853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12277868297458099501164941 4604200611546787312936853)
    ·
      refine ⟨215821903666255655293915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4604200611546787312936853 215821903666255655293915)
      ·
        refine ⟨323732855499383482940873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215821903666255655293915 323732855499383482940873)
        ·
          refine ⟨242799641624537612205655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323732855499383482940873 242799641624537612205655)
          ·
            refine ⟨364199462436806418308483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242799641624537612205655 364199462436806418308483)
            ·
              refine ⟨546299193655209627462725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364199462436806418308483 546299193655209627462725)
              ·
                refine ⟨102431098810351805149261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 546299193655209627462725 102431098810351805149261)
                ·
                  rfl

theorem cell19_336629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 4].length) (baseStart_336629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336629 prefixEnd_336629 := by exact prefixLift 336629
  have htrace : WordTrace (prefixWord ++ tailWord_336629) baseStart_336629 baseEnd_336629 := by
    simpa [prefixWord, tailWord_336629, baseEnd_336629] using wordTrace_append hprefix tailTrace_336629
  have hstable : (prefixWord ++ tailWord_336629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336629).length < 2 ^ (prefixWord ++ tailWord_336629).sum := by decide
  have hdescent : baseEnd_336629 < baseStart_336629 := by decide
  rcases family_descends (prefixWord ++ tailWord_336629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336677 : List Nat := [1, 3, 1, 2, 3, 1, 8]
def baseStart_336677 : Nat := 118140960795 + 336677 * 2 ^ 59
def prefixEnd_336677 : Nat := 4983230072969 + 3 ^ 40 * 336677 * 2
def baseEnd_336677 : Nat := 34148568160767305360821

theorem tailTrace_336677 : CollatzResearch.WordTrace tailWord_336677 prefixEnd_336677 34148568160767305360821 := by
  unfold tailWord_336677
  simp only [CollatzResearch.WordTrace]
  refine ⟨12279619001284203698912285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8186412667522802465941523 12279619001284203698912285)
  ·
    refine ⟨4604857125481576387092107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12279619001284203698912285 4604857125481576387092107)
    ·
      refine ⟨6907285688222364580638161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4604857125481576387092107 6907285688222364580638161)
      ·
        refine ⟨5180464266166773435478621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6907285688222364580638161 5180464266166773435478621)
        ·
          refine ⟨1942674099812540038304483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5180464266166773435478621 1942674099812540038304483)
          ·
            refine ⟨2914011149718810057456725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942674099812540038304483 2914011149718810057456725)
            ·
              refine ⟨34148568160767305360821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2914011149718810057456725 34148568160767305360821)
              ·
                rfl

theorem cell19_336677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_336677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336677 prefixEnd_336677 := by exact prefixLift 336677
  have htrace : WordTrace (prefixWord ++ tailWord_336677) baseStart_336677 baseEnd_336677 := by
    simpa [prefixWord, tailWord_336677, baseEnd_336677] using wordTrace_append hprefix tailTrace_336677
  have hstable : (prefixWord ++ tailWord_336677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336677).length < 2 ^ (prefixWord ++ tailWord_336677).sum := by decide
  have hdescent : baseEnd_336677 < baseStart_336677 := by decide
  rcases family_descends (prefixWord ++ tailWord_336677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336696 : List Nat := [2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_336696 : Nat := 118140960795 + 336696 * 2 ^ 59
def prefixEnd_336696 : Nat := 4983230072969 + 3 ^ 40 * 336696 * 2
def baseEnd_336696 : Nat := 102451485894115501660189

theorem tailTrace_336696 : CollatzResearch.WordTrace tailWord_336696 prefixEnd_336696 102451485894115501660189 := by
  unfold tailWord_336696
  simp only [CollatzResearch.WordTrace]
  refine ⟨6140155994107684971926971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8186874658810246629235961 6140155994107684971926971)
  ·
    refine ⟨9210233991161527457890457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6140155994107684971926971 9210233991161527457890457)
    ·
      refine ⟨6907675493371145593417843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9210233991161527457890457 6907675493371145593417843)
      ·
        refine ⟨10361513240056718390126765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6907675493371145593417843 10361513240056718390126765)
        ·
          refine ⟨3885567465021269396297537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10361513240056718390126765 3885567465021269396297537)
          ·
            refine ⟨2914175598765952047223153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3885567465021269396297537 2914175598765952047223153)
            ·
              refine ⟨2185631699074464035417365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2914175598765952047223153 2185631699074464035417365)
              ·
                refine ⟨102451485894115501660189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2185631699074464035417365 102451485894115501660189)
                ·
                  rfl

theorem cell19_336696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_336696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336696 prefixEnd_336696 := by exact prefixLift 336696
  have htrace : WordTrace (prefixWord ++ tailWord_336696) baseStart_336696 baseEnd_336696 := by
    simpa [prefixWord, tailWord_336696, baseEnd_336696] using wordTrace_append hprefix tailTrace_336696
  have hstable : (prefixWord ++ tailWord_336696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336696).length < 2 ^ (prefixWord ++ tailWord_336696).sum := by decide
  have hdescent : baseEnd_336696 < baseStart_336696 := by decide
  rcases family_descends (prefixWord ++ tailWord_336696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336713 : List Nat := [1, 2, 1, 1, 2, 5, 4, 3]
def baseStart_336713 : Nat := 118140960795 + 336713 * 2 ^ 59
def prefixEnd_336713 : Nat := 4983230072969 + 3 ^ 40 * 336713 * 2
def baseEnd_336713 : Nat := 102456658736264499282365

theorem tailTrace_336713 : CollatzResearch.WordTrace tailWord_336713 prefixEnd_336713 102456658736264499282365 := by
  unfold tailWord_336713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12280932029153781847222793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8187288019435854564815195 12280932029153781847222793)
  ·
    refine ⟨9210699021865336385417095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12280932029153781847222793 9210699021865336385417095)
    ·
      refine ⟨13816048532798004578125643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9210699021865336385417095 13816048532798004578125643)
      ·
        refine ⟨20724072799197006867188465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13816048532798004578125643 20724072799197006867188465)
        ·
          refine ⟨15543054599397755150391349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20724072799197006867188465 15543054599397755150391349)
          ·
            refine ⟨1457161368693539545349189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15543054599397755150391349 1457161368693539545349189)
            ·
              refine ⟨273217756630038664752973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1457161368693539545349189 273217756630038664752973)
              ·
                refine ⟨102456658736264499282365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273217756630038664752973 102456658736264499282365)
                ·
                  rfl

theorem cell19_336713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_336713 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336713 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336713 prefixEnd_336713 := by exact prefixLift 336713
  have htrace : WordTrace (prefixWord ++ tailWord_336713) baseStart_336713 baseEnd_336713 := by
    simpa [prefixWord, tailWord_336713, baseEnd_336713] using wordTrace_append hprefix tailTrace_336713
  have hstable : (prefixWord ++ tailWord_336713).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336713).length < 2 ^ (prefixWord ++ tailWord_336713).sum := by decide
  have hdescent : baseEnd_336713 < baseStart_336713 := by decide
  rcases family_descends (prefixWord ++ tailWord_336713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336732 : List Nat := [2, 2, 4, 2, 1, 1, 7]
def baseStart_336732 : Nat := 118140960795 + 336732 * 2 ^ 59
def prefixEnd_336732 : Nat := 4983230072969 + 3 ^ 40 * 336732 * 2
def baseEnd_336732 : Nat := 34154146716026028286697

theorem tailTrace_336732 : CollatzResearch.WordTrace tailWord_336732 prefixEnd_336732 34154146716026028286697 := by
  unfold tailWord_336732
  simp only [CollatzResearch.WordTrace]
  refine ⟨6140812508042474046082225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8187750010723298728109633 6140812508042474046082225)
  ·
    refine ⟨4605609381031855534561669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6140812508042474046082225 4605609381031855534561669)
    ·
      refine ⟨863551758943472912730313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4605609381031855534561669 863551758943472912730313)
      ·
        refine ⟨647663819207604684547735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 863551758943472912730313 647663819207604684547735)
        ·
          refine ⟨971495728811407026821603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647663819207604684547735 971495728811407026821603)
          ·
            refine ⟨1457243593217110540232405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971495728811407026821603 1457243593217110540232405)
            ·
              refine ⟨34154146716026028286697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1457243593217110540232405 34154146716026028286697)
              ·
                rfl

theorem cell19_336732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_336732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336732 prefixEnd_336732 := by exact prefixLift 336732
  have htrace : WordTrace (prefixWord ++ tailWord_336732) baseStart_336732 baseEnd_336732 := by
    simpa [prefixWord, tailWord_336732, baseEnd_336732] using wordTrace_append hprefix tailTrace_336732
  have hstable : (prefixWord ++ tailWord_336732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336732).length < 2 ^ (prefixWord ++ tailWord_336732).sum := by decide
  have hdescent : baseEnd_336732 < baseStart_336732 := by decide
  rcases family_descends (prefixWord ++ tailWord_336732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336753 : List Nat := [1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_336753 : Nat := 118140960795 + 336753 * 2 ^ 59
def prefixEnd_336753 : Nat := 4983230072969 + 3 ^ 40 * 336753 * 2
def baseEnd_336753 : Nat := 102468830129556258393367

theorem tailTrace_336753 : CollatzResearch.WordTrace tailWord_336753 prefixEnd_336753 102468830129556258393367 := by
  unfold tailWord_336753
  simp only [CollatzResearch.WordTrace]
  refine ⟨12282390949008868678678913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8188260632672579119119275 12282390949008868678678913)
  ·
    refine ⟨9211793211756651509009185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12282390949008868678678913 9211793211756651509009185)
    ·
      refine ⟨6908844908817488631756889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9211793211756651509009185 6908844908817488631756889)
      ·
        refine ⟨5181633681613116473817667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6908844908817488631756889 5181633681613116473817667)
        ·
          refine ⟨7772450522419674710726501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181633681613116473817667 7772450522419674710726501)
          ·
            refine ⟨1457334472953689008261219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7772450522419674710726501 1457334472953689008261219)
            ·
              refine ⟨2186001709430533512391829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457334472953689008261219 2186001709430533512391829)
              ·
                refine ⟨102468830129556258393367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2186001709430533512391829 102468830129556258393367)
                ·
                  rfl

theorem cell19_336753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_336753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336753 prefixEnd_336753 := by exact prefixLift 336753
  have htrace : WordTrace (prefixWord ++ tailWord_336753) baseStart_336753 baseEnd_336753 := by
    simpa [prefixWord, tailWord_336753, baseEnd_336753] using wordTrace_append hprefix tailTrace_336753
  have hstable : (prefixWord ++ tailWord_336753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336753).length < 2 ^ (prefixWord ++ tailWord_336753).sum := by decide
  have hdescent : baseEnd_336753 < baseStart_336753 := by decide
  rcases family_descends (prefixWord ++ tailWord_336753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336867 : List Nat := [1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_336867 : Nat := 118140960795 + 336867 * 2 ^ 59
def prefixEnd_336867 : Nat := 4983230072969 + 3 ^ 40 * 336867 * 2
def baseEnd_336867 : Nat := 102503518600437771859723

theorem tailTrace_336867 : CollatzResearch.WordTrace tailWord_336867 prefixEnd_336867 102503518600437771859723 := by
  unfold tailWord_336867
  simp only [CollatzResearch.WordTrace]
  refine ⟨12286548870595866148328855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8191032580397244098885903 12286548870595866148328855)
  ·
    refine ⟨18429823305893799222493283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12286548870595866148328855 18429823305893799222493283)
    ·
      refine ⟨27644734958840698833739925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18429823305893799222493283 27644734958840698833739925)
      ·
        refine ⟨1295846951195657757831559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27644734958840698833739925 1295846951195657757831559)
        ·
          refine ⟨1943770426793486636747339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295846951195657757831559 1943770426793486636747339)
          ·
            refine ⟨2915655640190229955121009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943770426793486636747339 2915655640190229955121009)
            ·
              refine ⟨2186741730142672466340757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2915655640190229955121009 2186741730142672466340757)
              ·
                refine ⟨102503518600437771859723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2186741730142672466340757 102503518600437771859723)
                ·
                  rfl

theorem cell19_336867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_336867 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336867 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336867 prefixEnd_336867 := by exact prefixLift 336867
  have htrace : WordTrace (prefixWord ++ tailWord_336867) baseStart_336867 baseEnd_336867 := by
    simpa [prefixWord, tailWord_336867, baseEnd_336867] using wordTrace_append hprefix tailTrace_336867
  have hstable : (prefixWord ++ tailWord_336867).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336867).length < 2 ^ (prefixWord ++ tailWord_336867).sum := by decide
  have hdescent : baseEnd_336867 < baseStart_336867 := by decide
  rcases family_descends (prefixWord ++ tailWord_336867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336882 : List Nat := [3, 2, 1, 5, 1, 1, 1, 5]
def baseStart_336882 : Nat := 118140960795 + 336882 * 2 ^ 59
def prefixEnd_336882 : Nat := 4983230072969 + 3 ^ 40 * 336882 * 2
def baseEnd_336882 : Nat := 102508082872922181526349

theorem tailTrace_336882 : CollatzResearch.WordTrace tailWord_336882 prefixEnd_336882 102508082872922181526349 := by
  unfold tailWord_336882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071773991385380927531225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8191397310361015806749933 3071773991385380927531225)
  ·
    refine ⟨2303830493539035695648419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3071773991385380927531225 2303830493539035695648419)
    ·
      refine ⟨3455745740308553543472629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2303830493539035695648419 3455745740308553543472629)
      ·
        refine ⟨323976163153926894700559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3455745740308553543472629 323976163153926894700559)
        ·
          refine ⟨485964244730890342050839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323976163153926894700559 485964244730890342050839)
          ·
            refine ⟨728946367096335513076259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485964244730890342050839 728946367096335513076259)
            ·
              refine ⟨1093419550644503269614389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728946367096335513076259 1093419550644503269614389)
              ·
                refine ⟨102508082872922181526349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1093419550644503269614389 102508082872922181526349)
                ·
                  rfl

theorem cell19_336882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_336882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_336882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_336882 prefixEnd_336882 := by exact prefixLift 336882
  have htrace : WordTrace (prefixWord ++ tailWord_336882) baseStart_336882 baseEnd_336882 := by
    simpa [prefixWord, tailWord_336882, baseEnd_336882] using wordTrace_append hprefix tailTrace_336882
  have hstable : (prefixWord ++ tailWord_336882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336882).length < 2 ^ (prefixWord ++ tailWord_336882).sum := by decide
  have hdescent : baseEnd_336882 < baseStart_336882 := by decide
  rcases family_descends (prefixWord ++ tailWord_336882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337055 : List Nat := [1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_337055 : Nat := 118140960795 + 337055 * 2 ^ 59
def prefixEnd_337055 : Nat := 4983230072969 + 3 ^ 40 * 337055 * 2
def baseEnd_337055 : Nat := 102560724148909039681433

theorem tailTrace_337055 : CollatzResearch.WordTrace tailWord_337055 prefixEnd_337055 102560724148909039681433 := by
  unfold tailWord_337055
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293405793914774256172619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8195603862609849504115079 12293405793914774256172619)
  ·
    refine ⟨18440108690872161384258929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12293405793914774256172619 18440108690872161384258929)
    ·
      refine ⟨13830081518154121038194197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18440108690872161384258929 13830081518154121038194197)
      ·
        refine ⟨648285071163474423665353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13830081518154121038194197 648285071163474423665353)
        ·
          refine ⟨486213803372605817749015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648285071163474423665353 486213803372605817749015)
          ·
            refine ⟨729320705058908726623523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486213803372605817749015 729320705058908726623523)
            ·
              refine ⟨1093981057588363089935285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729320705058908726623523 1093981057588363089935285)
              ·
                refine ⟨102560724148909039681433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1093981057588363089935285 102560724148909039681433)
                ·
                  rfl

theorem cell19_337055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_337055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337055 prefixEnd_337055 := by exact prefixLift 337055
  have htrace : WordTrace (prefixWord ++ tailWord_337055) baseStart_337055 baseEnd_337055 := by
    simpa [prefixWord, tailWord_337055, baseEnd_337055] using wordTrace_append hprefix tailTrace_337055
  have hstable : (prefixWord ++ tailWord_337055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337055).length < 2 ^ (prefixWord ++ tailWord_337055).sum := by decide
  have hdescent : baseEnd_337055 < baseStart_337055 := by decide
  rcases family_descends (prefixWord ++ tailWord_337055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337057 : List Nat := [1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_337057 : Nat := 118140960795 + 337057 * 2 ^ 59
def prefixEnd_337057 : Nat := 4983230072969 + 3 ^ 40 * 337057 * 2
def baseEnd_337057 : Nat := 102561332718573627636983

theorem tailTrace_337057 : CollatzResearch.WordTrace tailWord_337057 prefixEnd_337057 102561332718573627636983 := by
  unfold tailWord_337057
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293478739907528597745425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8195652493271685731830283 12293478739907528597745425)
  ·
    refine ⟨9220109054930646448309069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12293478739907528597745425 9220109054930646448309069)
    ·
      refine ⟨3457540895598992418115901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9220109054930646448309069 3457540895598992418115901)
      ·
        refine ⟨1296577835849622156793463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3457540895598992418115901 1296577835849622156793463)
        ·
          refine ⟨1944866753774433235190195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296577835849622156793463 1944866753774433235190195)
          ·
            refine ⟨2917300130661649852785293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944866753774433235190195 2917300130661649852785293)
            ·
              refine ⟨1093987548998118694794485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2917300130661649852785293 1093987548998118694794485)
              ·
                refine ⟨102561332718573627636983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1093987548998118694794485 102561332718573627636983)
                ·
                  rfl

theorem cell19_337057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_337057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337057 prefixEnd_337057 := by exact prefixLift 337057
  have htrace : WordTrace (prefixWord ++ tailWord_337057) baseStart_337057 baseEnd_337057 := by
    simpa [prefixWord, tailWord_337057, baseEnd_337057] using wordTrace_append hprefix tailTrace_337057
  have hstable : (prefixWord ++ tailWord_337057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337057).length < 2 ^ (prefixWord ++ tailWord_337057).sum := by decide
  have hdescent : baseEnd_337057 < baseStart_337057 := by decide
  rcases family_descends (prefixWord ++ tailWord_337057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337133 : List Nat := [1, 5, 1, 2, 2, 8]
def baseStart_337133 : Nat := 118140960795 + 337133 * 2 ^ 59
def prefixEnd_337133 : Nat := 4983230072969 + 3 ^ 40 * 337133 * 2
def baseEnd_337133 : Nat := 11398273151758663327543

theorem tailTrace_337133 : CollatzResearch.WordTrace tailWord_337133 prefixEnd_337133 11398273151758663327543 := by
  unfold tailWord_337133
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296250687632193577512053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8197500458421462385008035 12296250687632193577512053)
  ·
    refine ⟨1152773501965518147891755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12296250687632193577512053 1152773501965518147891755)
    ·
      refine ⟨1729160252948277221837633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152773501965518147891755 1729160252948277221837633)
      ·
        refine ⟨1296870189711207916378225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1729160252948277221837633 1296870189711207916378225)
        ·
          refine ⟨972652642283405937283669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296870189711207916378225 972652642283405937283669)
          ·
            refine ⟨11398273151758663327543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 972652642283405937283669 11398273151758663327543)
            ·
              rfl

theorem cell19_337133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 8].length) (baseStart_337133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337133 prefixEnd_337133 := by exact prefixLift 337133
  have htrace : WordTrace (prefixWord ++ tailWord_337133) baseStart_337133 baseEnd_337133 := by
    simpa [prefixWord, tailWord_337133, baseEnd_337133] using wordTrace_append hprefix tailTrace_337133
  have hstable : (prefixWord ++ tailWord_337133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337133).length < 2 ^ (prefixWord ++ tailWord_337133).sum := by decide
  have hdescent : baseEnd_337133 < baseStart_337133 := by decide
  rcases family_descends (prefixWord ++ tailWord_337133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337135 : List Nat := [1, 1, 2, 1, 14]
def baseStart_337135 : Nat := 118140960795 + 337135 * 2 ^ 59
def prefixEnd_337135 : Nat := 4983230072969 + 3 ^ 40 * 337135 * 2
def baseEnd_337135 : Nat := 3799446923536761403831

theorem tailTrace_337135 : CollatzResearch.WordTrace tailWord_337135 prefixEnd_337135 3799446923536761403831 := by
  unfold tailWord_337135
  simp only [CollatzResearch.WordTrace]
  refine ⟨12296323633624947919084859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8197549089083298612723239 12296323633624947919084859)
  ·
    refine ⟨18444485450437421878627289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12296323633624947919084859 18444485450437421878627289)
    ·
      refine ⟨13833364087828066408970467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18444485450437421878627289 13833364087828066408970467)
      ·
        refine ⟨20750046131742099613455701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13833364087828066408970467 20750046131742099613455701)
        ·
          refine ⟨3799446923536761403831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 20750046131742099613455701 3799446923536761403831)
          ·
            rfl

theorem cell19_337135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 14].length) (baseStart_337135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337135 prefixEnd_337135 := by exact prefixLift 337135
  have htrace : WordTrace (prefixWord ++ tailWord_337135) baseStart_337135 baseEnd_337135 := by
    simpa [prefixWord, tailWord_337135, baseEnd_337135] using wordTrace_append hprefix tailTrace_337135
  have hstable : (prefixWord ++ tailWord_337135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337135).length < 2 ^ (prefixWord ++ tailWord_337135).sum := by decide
  have hdescent : baseEnd_337135 < baseStart_337135 := by decide
  rcases family_descends (prefixWord ++ tailWord_337135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337148 : List Nat := [2, 2, 2, 1, 6, 1, 1, 4]
def baseStart_337148 : Nat := 118140960795 + 337148 * 2 ^ 59
def prefixEnd_337148 : Nat := 4983230072969 + 3 ^ 40 * 337148 * 2
def baseEnd_337148 : Nat := 102589022638312379614513

theorem tailTrace_337148 : CollatzResearch.WordTrace tailWord_337148 prefixEnd_337148 102589022638312379614513 := by
  unfold tailWord_337148
  simp only [CollatzResearch.WordTrace]
  refine ⟨6148398891288925569654049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8197865188385234092872065 6148398891288925569654049)
  ·
    refine ⟨4611299168466694177240537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6148398891288925569654049 4611299168466694177240537)
    ·
      refine ⟨3458474376350020632930403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4611299168466694177240537 3458474376350020632930403)
      ·
        refine ⟨5187711564525030949395605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3458474376350020632930403 5187711564525030949395605)
        ·
          refine ⟨243173979587110825752919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5187711564525030949395605 243173979587110825752919)
          ·
            refine ⟨364760969380666238629379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243173979587110825752919 364760969380666238629379)
            ·
              refine ⟨547141454070999357944069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364760969380666238629379 547141454070999357944069)
              ·
                refine ⟨102589022638312379614513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547141454070999357944069 102589022638312379614513)
                ·
                  rfl

theorem cell19_337148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_337148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337148 prefixEnd_337148 := by exact prefixLift 337148
  have htrace : WordTrace (prefixWord ++ tailWord_337148) baseStart_337148 baseEnd_337148 := by
    simpa [prefixWord, tailWord_337148, baseEnd_337148] using wordTrace_append hprefix tailTrace_337148
  have hstable : (prefixWord ++ tailWord_337148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337148).length < 2 ^ (prefixWord ++ tailWord_337148).sum := by decide
  have hdescent : baseEnd_337148 < baseStart_337148 := by decide
  rcases family_descends (prefixWord ++ tailWord_337148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337150 : List Nat := [4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_337150 : Nat := 118140960795 + 337150 * 2 ^ 59
def prefixEnd_337150 : Nat := 4983230072969 + 3 ^ 40 * 337150 * 2
def baseEnd_337150 : Nat := 102589631207976967570063

theorem tailTrace_337150 : CollatzResearch.WordTrace tailWord_337150 prefixEnd_337150 102589631207976967570063 := by
  unfold tailWord_337150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537108841071325685110113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8197913819047070320587269 1537108841071325685110113)
  ·
    refine ⟨1152831630803494263832585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1537108841071325685110113 1152831630803494263832585)
    ·
      refine ⟨864623723102620697874439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1152831630803494263832585 864623723102620697874439)
      ·
        refine ⟨1296935584653931046811659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864623723102620697874439 1296935584653931046811659)
        ·
          refine ⟨1945403376980896570217489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296935584653931046811659 1945403376980896570217489)
          ·
            refine ⟨1459052532735672427663117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1945403376980896570217489 1459052532735672427663117)
            ·
              refine ⟨547144699775877160373669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1459052532735672427663117 547144699775877160373669)
              ·
                refine ⟨102589631207976967570063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547144699775877160373669 102589631207976967570063)
                ·
                  rfl

theorem cell19_337150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_337150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337150 prefixEnd_337150 := by exact prefixLift 337150
  have htrace : WordTrace (prefixWord ++ tailWord_337150) baseStart_337150 baseEnd_337150 := by
    simpa [prefixWord, tailWord_337150, baseEnd_337150] using wordTrace_append hprefix tailTrace_337150
  have hstable : (prefixWord ++ tailWord_337150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337150).length < 2 ^ (prefixWord ++ tailWord_337150).sum := by decide
  have hdescent : baseEnd_337150 < baseStart_337150 := by decide
  rcases family_descends (prefixWord ++ tailWord_337150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337222 : List Nat := [6, 1, 1, 3, 1, 1, 1, 5]
def baseStart_337222 : Nat := 118140960795 + 337222 * 2 ^ 59
def prefixEnd_337222 : Nat := 4983230072969 + 3 ^ 40 * 337222 * 2
def baseEnd_337222 : Nat := 102611539715902133969867

theorem tailTrace_337222 : CollatzResearch.WordTrace tailWord_337222 prefixEnd_337222 102611539715902133969867 := by
  unfold tailWord_337222
  simp only [CollatzResearch.WordTrace]
  refine ⟨384359274509680055546935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8199664522873174518334613 384359274509680055546935)
  ·
    refine ⟨576538911764520083320403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384359274509680055546935 576538911764520083320403)
    ·
      refine ⟨864808367646780124980605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576538911764520083320403 864808367646780124980605)
      ·
        refine ⟨324303137867542546867727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 864808367646780124980605 324303137867542546867727)
        ·
          refine ⟨486454706801313820301591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324303137867542546867727 486454706801313820301591)
          ·
            refine ⟨729682060201970730452387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486454706801313820301591 729682060201970730452387)
            ·
              refine ⟨1094523090302956095678581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729682060201970730452387 1094523090302956095678581)
              ·
                refine ⟨102611539715902133969867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1094523090302956095678581 102611539715902133969867)
                ·
                  rfl

theorem cell19_337222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_337222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337222 prefixEnd_337222 := by exact prefixLift 337222
  have htrace : WordTrace (prefixWord ++ tailWord_337222) baseStart_337222 baseEnd_337222 := by
    simpa [prefixWord, tailWord_337222, baseEnd_337222] using wordTrace_append hprefix tailTrace_337222
  have hstable : (prefixWord ++ tailWord_337222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337222).length < 2 ^ (prefixWord ++ tailWord_337222).sum := by decide
  have hdescent : baseEnd_337222 < baseStart_337222 := by decide
  rcases family_descends (prefixWord ++ tailWord_337222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337228 : List Nat := [2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_337228 : Nat := 118140960795 + 337228 * 2 ^ 59
def prefixEnd_337228 : Nat := 4983230072969 + 3 ^ 40 * 337228 * 2
def baseEnd_337228 : Nat := 102613365424895897836517

theorem tailTrace_337228 : CollatzResearch.WordTrace tailWord_337228 prefixEnd_337228 102613365424895897836517 := by
  unfold tailWord_337228
  simp only [CollatzResearch.WordTrace]
  refine ⟨6149857811144012401110169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8199810414858683201480225 6149857811144012401110169)
  ·
    refine ⟨4612393358358009300832627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6149857811144012401110169 4612393358358009300832627)
    ·
      refine ⟨6918590037537013951248941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4612393358358009300832627 6918590037537013951248941)
      ·
        refine ⟨2594471264076380231718353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6918590037537013951248941 2594471264076380231718353)
        ·
          refine ⟨1945853448057285173788765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2594471264076380231718353 1945853448057285173788765)
          ·
            refine ⟨729695043021481940170787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1945853448057285173788765 729695043021481940170787)
            ·
              refine ⟨1094542564532222910256181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729695043021481940170787 1094542564532222910256181)
              ·
                refine ⟨102613365424895897836517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1094542564532222910256181 102613365424895897836517)
                ·
                  rfl

theorem cell19_337228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_337228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337228 prefixEnd_337228 := by exact prefixLift 337228
  have htrace : WordTrace (prefixWord ++ tailWord_337228) baseStart_337228 baseEnd_337228 := by
    simpa [prefixWord, tailWord_337228, baseEnd_337228] using wordTrace_append hprefix tailTrace_337228
  have hstable : (prefixWord ++ tailWord_337228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337228).length < 2 ^ (prefixWord ++ tailWord_337228).sum := by decide
  have hdescent : baseEnd_337228 < baseStart_337228 := by decide
  rcases family_descends (prefixWord ++ tailWord_337228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337262 : List Nat := [4, 1, 2, 4, 1, 1, 2, 4]
def baseStart_337262 : Nat := 118140960795 + 337262 * 2 ^ 59
def prefixEnd_337262 : Nat := 4983230072969 + 3 ^ 40 * 337262 * 2
def baseEnd_337262 : Nat := 102623711109193893080869

theorem tailTrace_337262 : CollatzResearch.WordTrace tailWord_337262 prefixEnd_337262 102623711109193893080869 := by
  unfold tailWord_337262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537619463020606076119755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8200637136109899072638693 1537619463020606076119755)
  ·
    refine ⟨2306429194530909114179633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1537619463020606076119755 2306429194530909114179633)
    ·
      refine ⟨1729821895898181835634725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2306429194530909114179633 1729821895898181835634725)
      ·
        refine ⟨324341605480909094181511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1729821895898181835634725 324341605480909094181511)
        ·
          refine ⟨486512408221363641272267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324341605480909094181511 486512408221363641272267)
          ·
            refine ⟨729768612332045461908401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486512408221363641272267 729768612332045461908401)
            ·
              refine ⟨547326459249034096431301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729768612332045461908401 547326459249034096431301)
              ·
                refine ⟨102623711109193893080869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547326459249034096431301 102623711109193893080869)
                ·
                  rfl

theorem cell19_337262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_337262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337262 prefixEnd_337262 := by exact prefixLift 337262
  have htrace : WordTrace (prefixWord ++ tailWord_337262) baseStart_337262 baseEnd_337262 := by
    simpa [prefixWord, tailWord_337262, baseEnd_337262] using wordTrace_append hprefix tailTrace_337262
  have hstable : (prefixWord ++ tailWord_337262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337262).length < 2 ^ (prefixWord ++ tailWord_337262).sum := by decide
  have hdescent : baseEnd_337262 < baseStart_337262 := by decide
  rcases family_descends (prefixWord ++ tailWord_337262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337266 : List Nat := [3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_337266 : Nat := 118140960795 + 337266 * 2 ^ 59
def prefixEnd_337266 : Nat := 4983230072969 + 3 ^ 40 * 337266 * 2
def baseEnd_337266 : Nat := 102624928248523068991969

theorem tailTrace_337266 : CollatzResearch.WordTrace tailWord_337266 prefixEnd_337266 102624928248523068991969 := by
  unfold tailWord_337266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3075275399037589323025913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8200734397433571528069101 3075275399037589323025913)
  ·
    refine ⟨2306456549278191992269435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3075275399037589323025913 2306456549278191992269435)
    ·
      refine ⟨3459684823917287988404153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306456549278191992269435 3459684823917287988404153)
      ·
        refine ⟨2594763617937965991303115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3459684823917287988404153 2594763617937965991303115)
        ·
          refine ⟨3892145426906948986954673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594763617937965991303115 3892145426906948986954673)
          ·
            refine ⟨2919109070180211740216005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3892145426906948986954673 2919109070180211740216005)
            ·
              refine ⟨547332950658789701290501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2919109070180211740216005 547332950658789701290501)
              ·
                refine ⟨102624928248523068991969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547332950658789701290501 102624928248523068991969)
                ·
                  rfl

theorem cell19_337266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_337266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337266 prefixEnd_337266 := by exact prefixLift 337266
  have htrace : WordTrace (prefixWord ++ tailWord_337266) baseStart_337266 baseEnd_337266 := by
    simpa [prefixWord, tailWord_337266, baseEnd_337266] using wordTrace_append hprefix tailTrace_337266
  have hstable : (prefixWord ++ tailWord_337266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337266).length < 2 ^ (prefixWord ++ tailWord_337266).sum := by decide
  have hdescent : baseEnd_337266 < baseStart_337266 := by decide
  rcases family_descends (prefixWord ++ tailWord_337266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337302 : List Nat := [5, 3, 1, 10]
def baseStart_337302 : Nat := 118140960795 + 337302 * 2 ^ 59
def prefixEnd_337302 : Nat := 4983230072969 + 3 ^ 40 * 337302 * 2
def baseEnd_337302 : Nat := 1267109660524514224591

theorem tailTrace_337302 : CollatzResearch.WordTrace tailWord_337302 prefixEnd_337302 1267109660524514224591 := by
  unfold tailWord_337302
  simp only [CollatzResearch.WordTrace]
  refine ⟨768900914001245965025885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8201609749346623626942773 768900914001245965025885)
  ·
    refine ⟨288337842750467236884707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 768900914001245965025885 288337842750467236884707)
    ·
      refine ⟨432506764125700855327061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288337842750467236884707 432506764125700855327061)
      ·
        refine ⟨1267109660524514224591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 432506764125700855327061 1267109660524514224591)
        ·
          rfl

theorem cell19_337302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 10].length) (baseStart_337302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337302 prefixEnd_337302 := by exact prefixLift 337302
  have htrace : WordTrace (prefixWord ++ tailWord_337302) baseStart_337302 baseEnd_337302 := by
    simpa [prefixWord, tailWord_337302, baseEnd_337302] using wordTrace_append hprefix tailTrace_337302
  have hstable : (prefixWord ++ tailWord_337302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337302).length < 2 ^ (prefixWord ++ tailWord_337302).sum := by decide
  have hdescent : baseEnd_337302 < baseStart_337302 := by decide
  rcases family_descends (prefixWord ++ tailWord_337302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337304 : List Nat := [2, 1, 2, 5, 2, 7]
def baseStart_337304 : Nat := 118140960795 + 337304 * 2 ^ 59
def prefixEnd_337304 : Nat := 4983230072969 + 3 ^ 40 * 337304 * 2
def baseEnd_337304 : Nat := 11404054563572248905269

theorem tailTrace_337304 : CollatzResearch.WordTrace tailWord_337304 prefixEnd_337304 11404054563572248905269 := by
  unfold tailWord_337304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6151243785006344890993483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8201658380008459854657977 6151243785006344890993483)
  ·
    refine ⟨9226865677509517336490225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6151243785006344890993483 9226865677509517336490225)
    ·
      refine ⟨6920149258132138002367669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9226865677509517336490225 6920149258132138002367669)
      ·
        refine ⟨648763992949887937721969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6920149258132138002367669 648763992949887937721969)
        ·
          refine ⟨486572994712415953291477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648763992949887937721969 486572994712415953291477)
          ·
            refine ⟨11404054563572248905269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 486572994712415953291477 11404054563572248905269)
            ·
              rfl

theorem cell19_337304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 7].length) (baseStart_337304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337304 prefixEnd_337304 := by exact prefixLift 337304
  have htrace : WordTrace (prefixWord ++ tailWord_337304) baseStart_337304 baseEnd_337304 := by
    simpa [prefixWord, tailWord_337304, baseEnd_337304] using wordTrace_append hprefix tailTrace_337304
  have hstable : (prefixWord ++ tailWord_337304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337304).length < 2 ^ (prefixWord ++ tailWord_337304).sum := by decide
  have hdescent : baseEnd_337304 < baseStart_337304 := by decide
  rcases family_descends (prefixWord ++ tailWord_337304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337344 : List Nat := [2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_337344 : Nat := 118140960795 + 337344 * 2 ^ 59
def prefixEnd_337344 : Nat := 4983230072969 + 3 ^ 40 * 337344 * 2
def baseEnd_337344 : Nat := 102648662465441999258423

theorem tailTrace_337344 : CollatzResearch.WordTrace tailWord_337344 prefixEnd_337344 102648662465441999258423 := by
  unfold tailWord_337344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6151973244933888306721543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8202630993245184408962057 6151973244933888306721543)
  ·
    refine ⟨9227959867400832460082315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6151973244933888306721543 9227959867400832460082315)
    ·
      refine ⟨13841939801101248690123473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9227959867400832460082315 13841939801101248690123473)
      ·
        refine ⟨10381454850825936517592605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13841939801101248690123473 10381454850825936517592605)
        ·
          refine ⟨3893045569059726194097227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10381454850825936517592605 3893045569059726194097227)
          ·
            refine ⟨5839568353589589291145841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893045569059726194097227 5839568353589589291145841)
            ·
              refine ⟨4379676265192191968359381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5839568353589589291145841 4379676265192191968359381)
              ·
                refine ⟨102648662465441999258423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4379676265192191968359381 102648662465441999258423)
                ·
                  rfl

theorem cell19_337344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_337344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337344 prefixEnd_337344 := by exact prefixLift 337344
  have htrace : WordTrace (prefixWord ++ tailWord_337344) baseStart_337344 baseEnd_337344 := by
    simpa [prefixWord, tailWord_337344, baseEnd_337344] using wordTrace_append hprefix tailTrace_337344
  have hstable : (prefixWord ++ tailWord_337344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337344).length < 2 ^ (prefixWord ++ tailWord_337344).sum := by decide
  have hdescent : baseEnd_337344 < baseStart_337344 := by decide
  rcases family_descends (prefixWord ++ tailWord_337344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337397 : List Nat := [1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_337397 : Nat := 118140960795 + 337397 * 2 ^ 59
def prefixEnd_337397 : Nat := 4983230072969 + 3 ^ 40 * 337397 * 2
def baseEnd_337397 : Nat := 102664789561553580080501

theorem tailTrace_337397 : CollatzResearch.WordTrace tailWord_337397 prefixEnd_337397 102664789561553580080501 := by
  unfold tailWord_337397
  simp only [CollatzResearch.WordTrace]
  refine ⟨12305879558675766665122445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8203919705783844443414963 12305879558675766665122445)
  ·
    refine ⟨4614704834503412499420917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12305879558675766665122445 4614704834503412499420917)
    ·
      refine ⟨432628578234694921820711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4614704834503412499420917 432628578234694921820711)
      ·
        refine ⟨648942867352042382731067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432628578234694921820711 648942867352042382731067)
        ·
          refine ⟨973414301028063574096601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648942867352042382731067 973414301028063574096601)
          ·
            refine ⟨730060725771047680572451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973414301028063574096601 730060725771047680572451)
            ·
              refine ⟨1095091088656571520858677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730060725771047680572451 1095091088656571520858677)
              ·
                refine ⟨102664789561553580080501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1095091088656571520858677 102664789561553580080501)
                ·
                  rfl

theorem cell19_337397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_337397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337397 prefixEnd_337397 := by exact prefixLift 337397
  have htrace : WordTrace (prefixWord ++ tailWord_337397) baseStart_337397 baseEnd_337397 := by
    simpa [prefixWord, tailWord_337397, baseEnd_337397] using wordTrace_append hprefix tailTrace_337397
  have hstable : (prefixWord ++ tailWord_337397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337397).length < 2 ^ (prefixWord ++ tailWord_337397).sum := by decide
  have hdescent : baseEnd_337397 < baseStart_337397 := by decide
  rcases family_descends (prefixWord ++ tailWord_337397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337418 : List Nat := [3, 1, 2, 2, 2, 4, 5]
def baseStart_337418 : Nat := 118140960795 + 337418 * 2 ^ 59
def prefixEnd_337418 : Nat := 4983230072969 + 3 ^ 40 * 337418 * 2
def baseEnd_337418 : Nat := 34223726514343917871259

theorem tailTrace_337418 : CollatzResearch.WordTrace tailWord_337418 prefixEnd_337418 34223726514343917871259 := by
  unfold tailWord_337418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076661372899921812909227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8204430327733124834424605 3076661372899921812909227)
  ·
    refine ⟨4614992059349882719363841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076661372899921812909227 4614992059349882719363841)
    ·
      refine ⟨3461244044512412039522881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4614992059349882719363841 3461244044512412039522881)
      ·
        refine ⟨2595933033384309029642161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3461244044512412039522881 2595933033384309029642161)
        ·
          refine ⟨1946949775038231772231621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595933033384309029642161 1946949775038231772231621)
          ·
            refine ⟨365053082819668457293429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1946949775038231772231621 365053082819668457293429)
            ·
              refine ⟨34223726514343917871259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 365053082819668457293429 34223726514343917871259)
              ·
                rfl

theorem cell19_337418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_337418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337418 prefixEnd_337418 := by exact prefixLift 337418
  have htrace : WordTrace (prefixWord ++ tailWord_337418) baseStart_337418 baseEnd_337418 := by
    simpa [prefixWord, tailWord_337418, baseEnd_337418] using wordTrace_append hprefix tailTrace_337418
  have hstable : (prefixWord ++ tailWord_337418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337418).length < 2 ^ (prefixWord ++ tailWord_337418).sum := by decide
  have hdescent : baseEnd_337418 < baseStart_337418 := by decide
  rcases family_descends (prefixWord ++ tailWord_337418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337437 : List Nat := [1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_337437 : Nat := 118140960795 + 337437 * 2 ^ 59
def prefixEnd_337437 : Nat := 4983230072969 + 3 ^ 40 * 337437 * 2
def baseEnd_337437 : Nat := 102676960954845339191503

theorem tailTrace_337437 : CollatzResearch.WordTrace tailWord_337437 prefixEnd_337437 102676960954845339191503 := by
  unfold tailWord_337437
  simp only [CollatzResearch.WordTrace]
  refine ⟨12307338478530853496578565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8204892319020568997719043 12307338478530853496578565)
  ·
    refine ⟨2307625964724535030608481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12307338478530853496578565 2307625964724535030608481)
    ·
      refine ⟨1730719473543401272956361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2307625964724535030608481 1730719473543401272956361)
      ·
        refine ⟨1298039605157550954717271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1730719473543401272956361 1298039605157550954717271)
        ·
          refine ⟨1947059407736326432075907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298039605157550954717271 1947059407736326432075907)
          ·
            refine ⟨2920589111604489648113861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947059407736326432075907 2920589111604489648113861)
            ·
              refine ⟨547610458425841809021349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2920589111604489648113861 547610458425841809021349)
              ·
                refine ⟨102676960954845339191503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547610458425841809021349 102676960954845339191503)
                ·
                  rfl

theorem cell19_337437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_337437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337437 prefixEnd_337437 := by exact prefixLift 337437
  have htrace : WordTrace (prefixWord ++ tailWord_337437) baseStart_337437 baseEnd_337437 := by
    simpa [prefixWord, tailWord_337437, baseEnd_337437] using wordTrace_append hprefix tailTrace_337437
  have hstable : (prefixWord ++ tailWord_337437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337437).length < 2 ^ (prefixWord ++ tailWord_337437).sum := by decide
  have hdescent : baseEnd_337437 < baseStart_337437 := by decide
  rcases family_descends (prefixWord ++ tailWord_337437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337439 : List Nat := [1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_337439 : Nat := 118140960795 + 337439 * 2 ^ 59
def prefixEnd_337439 : Nat := 4983230072969 + 3 ^ 40 * 337439 * 2
def baseEnd_337439 : Nat := 102677569524509927147053

theorem tailTrace_337439 : CollatzResearch.WordTrace tailWord_337439 prefixEnd_337439 102677569524509927147053 := by
  unfold tailWord_337439
  simp only [CollatzResearch.WordTrace]
  refine ⟨12307411424523607838151371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8204940949682405225434247 12307411424523607838151371)
  ·
    refine ⟨18461117136785411757227057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12307411424523607838151371 18461117136785411757227057)
    ·
      refine ⟨13845837852589058817920293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18461117136785411757227057 13845837852589058817920293)
      ·
        refine ⟨2596094597360448528360055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13845837852589058817920293 2596094597360448528360055)
        ·
          refine ⟨3894141896040672792540083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596094597360448528360055 3894141896040672792540083)
          ·
            refine ⟨5841212844061009188810125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894141896040672792540083 5841212844061009188810125)
            ·
              refine ⟨2190454816522878445803797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5841212844061009188810125 2190454816522878445803797)
              ·
                refine ⟨102677569524509927147053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2190454816522878445803797 102677569524509927147053)
                ·
                  rfl

theorem cell19_337439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_337439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337439 prefixEnd_337439 := by exact prefixLift 337439
  have htrace : WordTrace (prefixWord ++ tailWord_337439) baseStart_337439 baseEnd_337439 := by
    simpa [prefixWord, tailWord_337439, baseEnd_337439] using wordTrace_append hprefix tailTrace_337439
  have hstable : (prefixWord ++ tailWord_337439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337439).length < 2 ^ (prefixWord ++ tailWord_337439).sum := by decide
  have hdescent : baseEnd_337439 < baseStart_337439 := by decide
  rcases family_descends (prefixWord ++ tailWord_337439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337566 : List Nat := [4, 3, 1, 1, 1, 4, 2, 3]
def baseStart_337566 : Nat := 118140960795 + 337566 * 2 ^ 59
def prefixEnd_337566 : Nat := 4983230072969 + 3 ^ 40 * 337566 * 2
def baseEnd_337566 : Nat := 102716213698211262324485

theorem tailTrace_337566 : CollatzResearch.WordTrace tailWord_337566 prefixEnd_337566 102716213698211262324485 := by
  unfold tailWord_337566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1539005436882938566003069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8208028996709005685349701 1539005436882938566003069)
  ·
    refine ⟨577127038831101962251151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1539005436882938566003069 577127038831101962251151)
    ·
      refine ⟨865690558246652943376727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577127038831101962251151 865690558246652943376727)
      ·
        refine ⟨1298535837369979415065091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865690558246652943376727 1298535837369979415065091)
        ·
          refine ⟨1947803756054969122597637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298535837369979415065091 1947803756054969122597637)
          ·
            refine ⟨365213204260306710487057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1947803756054969122597637 365213204260306710487057)
            ·
              refine ⟨273909903195230032865293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365213204260306710487057 273909903195230032865293)
              ·
                refine ⟨102716213698211262324485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273909903195230032865293 102716213698211262324485)
                ·
                  rfl

theorem cell19_337566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_337566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337566 prefixEnd_337566 := by exact prefixLift 337566
  have htrace : WordTrace (prefixWord ++ tailWord_337566) baseStart_337566 baseEnd_337566 := by
    simpa [prefixWord, tailWord_337566, baseEnd_337566] using wordTrace_append hprefix tailTrace_337566
  have hstable : (prefixWord ++ tailWord_337566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337566).length < 2 ^ (prefixWord ++ tailWord_337566).sum := by decide
  have hdescent : baseEnd_337566 < baseStart_337566 := by decide
  rcases family_descends (prefixWord ++ tailWord_337566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337568 : List Nat := [2, 1, 1, 4, 3, 3, 2, 3]
def baseStart_337568 : Nat := 118140960795 + 337568 * 2 ^ 59
def prefixEnd_337568 : Nat := 4983230072969 + 3 ^ 40 * 337568 * 2
def baseEnd_337568 : Nat := 102716822267875850280035

theorem tailTrace_337568 : CollatzResearch.WordTrace tailWord_337568 prefixEnd_337568 102716822267875850280035 := by
  unfold tailWord_337568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156058220528131434798679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8208077627370841913064905 6156058220528131434798679)
  ·
    refine ⟨9234087330792197152198019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6156058220528131434798679 9234087330792197152198019)
    ·
      refine ⟨13851130996188295728297029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9234087330792197152198019 13851130996188295728297029)
      ·
        refine ⟨2597087061785305449055693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13851130996188295728297029 2597087061785305449055693)
        ·
          refine ⟨973907648169489543395885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2597087061785305449055693 973907648169489543395885)
          ·
            refine ⟨365215368063558578773457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 973907648169489543395885 365215368063558578773457)
            ·
              refine ⟨273911526047668934080093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365215368063558578773457 273911526047668934080093)
              ·
                refine ⟨102716822267875850280035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273911526047668934080093 102716822267875850280035)
                ·
                  rfl

theorem cell19_337568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_337568 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337568 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337568 prefixEnd_337568 := by exact prefixLift 337568
  have htrace : WordTrace (prefixWord ++ tailWord_337568) baseStart_337568 baseEnd_337568 := by
    simpa [prefixWord, tailWord_337568, baseEnd_337568] using wordTrace_append hprefix tailTrace_337568
  have hstable : (prefixWord ++ tailWord_337568).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337568).length < 2 ^ (prefixWord ++ tailWord_337568).sum := by decide
  have hdescent : baseEnd_337568 < baseStart_337568 := by decide
  rcases family_descends (prefixWord ++ tailWord_337568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337591 : List Nat := [1, 1, 3, 1, 5, 1, 7]
def baseStart_337591 : Nat := 118140960795 + 337591 * 2 ^ 59
def prefixEnd_337591 : Nat := 4983230072969 + 3 ^ 40 * 337591 * 2
def baseEnd_337591 : Nat := 34241273606339537256287

theorem tailTrace_337591 : CollatzResearch.WordTrace tailWord_337591 prefixEnd_337591 34241273606339537256287 := by
  unfold tailWord_337591
  simp only [CollatzResearch.WordTrace]
  refine ⟨12312955319972937797684627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8208636879981958531789751 12312955319972937797684627)
  ·
    refine ⟨18469432979959406696526941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12312955319972937797684627 18469432979959406696526941)
    ·
      refine ⟨6926037367484777511197603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18469432979959406696526941 6926037367484777511197603)
      ·
        refine ⟨10389056051227166266796405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6926037367484777511197603 10389056051227166266796405)
        ·
          refine ⟨973974004802546837512163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10389056051227166266796405 973974004802546837512163)
          ·
            refine ⟨1460961007203820256268245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973974004802546837512163 1460961007203820256268245)
            ·
              refine ⟨34241273606339537256287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1460961007203820256268245 34241273606339537256287)
              ·
                rfl

theorem cell19_337591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_337591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337591 prefixEnd_337591 := by exact prefixLift 337591
  have htrace : WordTrace (prefixWord ++ tailWord_337591) baseStart_337591 baseEnd_337591 := by
    simpa [prefixWord, tailWord_337591, baseEnd_337591] using wordTrace_append hprefix tailTrace_337591
  have hstable : (prefixWord ++ tailWord_337591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337591).length < 2 ^ (prefixWord ++ tailWord_337591).sum := by decide
  have hdescent : baseEnd_337591 < baseStart_337591 := by decide
  rcases family_descends (prefixWord ++ tailWord_337591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337602 : List Nat := [3, 5, 1, 2, 1, 1, 2, 4]
def baseStart_337602 : Nat := 118140960795 + 337602 * 2 ^ 59
def prefixEnd_337602 : Nat := 4983230072969 + 3 ^ 40 * 337602 * 2
def baseEnd_337602 : Nat := 102727167952173845524387

theorem tailTrace_337602 : CollatzResearch.WordTrace tailWord_337602 prefixEnd_337602 102727167952173845524387 := by
  unfold tailWord_337602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3078339130733271669083765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8208904348622057784223373 3078339130733271669083765)
  ·
    refine ⟨288594293506244218976603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3078339130733271669083765 288594293506244218976603)
    ·
      refine ⟨432891440259366328464905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288594293506244218976603 432891440259366328464905)
      ·
        refine ⟨324668580194524746348679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432891440259366328464905 324668580194524746348679)
        ·
          refine ⟨487002870291787119523019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324668580194524746348679 487002870291787119523019)
          ·
            refine ⟨730504305437680679284529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487002870291787119523019 730504305437680679284529)
            ·
              refine ⟨547878229078260509463397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730504305437680679284529 547878229078260509463397)
              ·
                refine ⟨102727167952173845524387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547878229078260509463397 102727167952173845524387)
                ·
                  rfl

theorem cell19_337602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_337602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337602 prefixEnd_337602 := by exact prefixLift 337602
  have htrace : WordTrace (prefixWord ++ tailWord_337602) baseStart_337602 baseEnd_337602 := by
    simpa [prefixWord, tailWord_337602, baseEnd_337602] using wordTrace_append hprefix tailTrace_337602
  have hstable : (prefixWord ++ tailWord_337602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337602).length < 2 ^ (prefixWord ++ tailWord_337602).sum := by decide
  have hdescent : baseEnd_337602 < baseStart_337602 := by decide
  rcases family_descends (prefixWord ++ tailWord_337602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337667 : List Nat := [1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_337667 : Nat := 118140960795 + 337667 * 2 ^ 59
def prefixEnd_337667 : Nat := 4983230072969 + 3 ^ 40 * 337667 * 2
def baseEnd_337667 : Nat := 102746946466272954079765

theorem tailTrace_337667 : CollatzResearch.WordTrace tailWord_337667 prefixEnd_337667 102746946466272954079765 := by
  unfold tailWord_337667
  simp only [CollatzResearch.WordTrace]
  refine ⟨12315727267697602777451255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8210484845131735184967503 12315727267697602777451255)
  ·
    refine ⟨18473590901546404166176883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12315727267697602777451255 18473590901546404166176883)
    ·
      refine ⟨27710386352319606249265325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18473590901546404166176883 27710386352319606249265325)
      ·
        refine ⟨10391394882119852343474497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27710386352319606249265325 10391394882119852343474497)
        ·
          refine ⟨7793546161589889257605873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10391394882119852343474497 7793546161589889257605873)
          ·
            refine ⟨5845159621192416943204405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7793546161589889257605873 5845159621192416943204405)
            ·
              refine ⟨547983714486789088425413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5845159621192416943204405 547983714486789088425413)
              ·
                refine ⟨102746946466272954079765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547983714486789088425413 102746946466272954079765)
                ·
                  rfl

theorem cell19_337667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_337667 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337667 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337667 prefixEnd_337667 := by exact prefixLift 337667
  have htrace : WordTrace (prefixWord ++ tailWord_337667) baseStart_337667 baseEnd_337667 := by
    simpa [prefixWord, tailWord_337667, baseEnd_337667] using wordTrace_append hprefix tailTrace_337667
  have hstable : (prefixWord ++ tailWord_337667).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337667).length < 2 ^ (prefixWord ++ tailWord_337667).sum := by decide
  have hdescent : baseEnd_337667 < baseStart_337667 := by decide
  rcases family_descends (prefixWord ++ tailWord_337667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337832 : List Nat := [2, 1, 6, 2, 1, 2, 1, 4]
def baseStart_337832 : Nat := 118140960795 + 337832 * 2 ^ 59
def prefixEnd_337832 : Nat := 4983230072969 + 3 ^ 40 * 337832 * 2
def baseEnd_337832 : Nat := 102797153463601460412649

theorem tailTrace_337832 : CollatzResearch.WordTrace tailWord_337832 prefixEnd_337832 102797153463601460412649 := by
  unfold tailWord_337832
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160872656049917978603875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8214496874733223971471833 6160872656049917978603875)
  ·
    refine ⟨9241308984074876967905813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6160872656049917978603875 9241308984074876967905813)
    ·
      refine ⟨433186358628509857870585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9241308984074876967905813 433186358628509857870585)
      ·
        refine ⟨324889768971382393402939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433186358628509857870585 324889768971382393402939)
        ·
          refine ⟨487334653457073590104409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324889768971382393402939 487334653457073590104409)
          ·
            refine ⟨365500990092805192578307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487334653457073590104409 365500990092805192578307)
            ·
              refine ⟨548251485139207788867461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365500990092805192578307 548251485139207788867461)
              ·
                refine ⟨102797153463601460412649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 548251485139207788867461 102797153463601460412649)
                ·
                  rfl

theorem cell19_337832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_337832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337832 prefixEnd_337832 := by exact prefixLift 337832
  have htrace : WordTrace (prefixWord ++ tailWord_337832) baseStart_337832 baseEnd_337832 := by
    simpa [prefixWord, tailWord_337832, baseEnd_337832] using wordTrace_append hprefix tailTrace_337832
  have hstable : (prefixWord ++ tailWord_337832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337832).length < 2 ^ (prefixWord ++ tailWord_337832).sum := by decide
  have hdescent : baseEnd_337832 < baseStart_337832 := by decide
  rcases family_descends (prefixWord ++ tailWord_337832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337874 : List Nat := [3, 2, 2, 3, 2, 1, 6]
def baseStart_337874 : Nat := 118140960795 + 337874 * 2 ^ 59
def prefixEnd_337874 : Nat := 4983230072969 + 3 ^ 40 * 337874 * 2
def baseEnd_337874 : Nat := 34269977808852602493067

theorem tailTrace_337874 : CollatzResearch.WordTrace tailWord_337874 prefixEnd_337874 34269977808852602493067 := by
  unfold tailWord_337874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080819294486919282559169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8215518118631784753491117 3080819294486919282559169)
  ·
    refine ⟨2310614470865189461919377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3080819294486919282559169 2310614470865189461919377)
    ·
      refine ⟨1732960853148892096439533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2310614470865189461919377 1732960853148892096439533)
      ·
        refine ⟨649860319930834536164825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1732960853148892096439533 649860319930834536164825)
        ·
          refine ⟨487395239948125902123619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649860319930834536164825 487395239948125902123619)
          ·
            refine ⟨731092859922188853185429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487395239948125902123619 731092859922188853185429)
            ·
              refine ⟨34269977808852602493067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 731092859922188853185429 34269977808852602493067)
              ·
                rfl

theorem cell19_337874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_337874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337874 prefixEnd_337874 := by exact prefixLift 337874
  have htrace : WordTrace (prefixWord ++ tailWord_337874) baseStart_337874 baseEnd_337874 := by
    simpa [prefixWord, tailWord_337874, baseEnd_337874] using wordTrace_append hprefix tailTrace_337874
  have hstable : (prefixWord ++ tailWord_337874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337874).length < 2 ^ (prefixWord ++ tailWord_337874).sum := by decide
  have hdescent : baseEnd_337874 < baseStart_337874 := by decide
  rcases family_descends (prefixWord ++ tailWord_337874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337876 : List Nat := [2, 4, 1, 2, 1, 1, 8]
def baseStart_337876 : Nat := 118140960795 + 337876 * 2 ^ 59
def prefixEnd_337876 : Nat := 4983230072969 + 3 ^ 40 * 337876 * 2
def baseEnd_337876 : Nat := 34270180665407465144917

theorem tailTrace_337876 : CollatzResearch.WordTrace tailWord_337876 prefixEnd_337876 34270180665407465144917 := by
  unfold tailWord_337876
  simp only [CollatzResearch.WordTrace]
  refine ⟨6161675061970215735904741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8215566749293620981206321 6161675061970215735904741)
  ·
    refine ⟨1155314074119415450482139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6161675061970215735904741 1155314074119415450482139)
    ·
      refine ⟨1732971111179123175723209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155314074119415450482139 1732971111179123175723209)
      ·
        refine ⟨1299728333384342381792407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1732971111179123175723209 1299728333384342381792407)
        ·
          refine ⟨1949592500076513572688611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299728333384342381792407 1949592500076513572688611)
          ·
            refine ⟨2924388750114770359032917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949592500076513572688611 2924388750114770359032917)
            ·
              refine ⟨34270180665407465144917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2924388750114770359032917 34270180665407465144917)
              ·
                rfl

theorem cell19_337876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_337876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_337876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_337876 prefixEnd_337876 := by exact prefixLift 337876
  have htrace : WordTrace (prefixWord ++ tailWord_337876) baseStart_337876 baseEnd_337876 := by
    simpa [prefixWord, tailWord_337876, baseEnd_337876] using wordTrace_append hprefix tailTrace_337876
  have hstable : (prefixWord ++ tailWord_337876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337876).length < 2 ^ (prefixWord ++ tailWord_337876).sum := by decide
  have hdescent : baseEnd_337876 < baseStart_337876 := by decide
  rcases family_descends (prefixWord ++ tailWord_337876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338066 : List Nat := [3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_338066 : Nat := 118140960795 + 338066 * 2 ^ 59
def prefixEnd_338066 : Nat := 4983230072969 + 3 ^ 40 * 338066 * 2
def baseEnd_338066 : Nat := 102868356114358251212011

theorem tailTrace_338066 : CollatzResearch.WordTrace tailWord_338066 prefixEnd_338066 102868356114358251212011 := by
  unfold tailWord_338066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082569998313023480306513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8220186662168062614150701 3082569998313023480306513)
  ·
    refine ⟨2311927498734767610229885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3082569998313023480306513 2311927498734767610229885)
    ·
      refine ⟨866972812025537853836207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2311927498734767610229885 866972812025537853836207)
      ·
        refine ⟨1300459218038306780754311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866972812025537853836207 1300459218038306780754311)
        ·
          refine ⟨1950688827057460171131467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300459218038306780754311 1950688827057460171131467)
          ·
            refine ⟨2926033240586190256697201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950688827057460171131467 2926033240586190256697201)
            ·
              refine ⟨2194524930439642692522901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926033240586190256697201 2194524930439642692522901)
              ·
                refine ⟨102868356114358251212011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2194524930439642692522901 102868356114358251212011)
                ·
                  rfl

theorem cell19_338066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_338066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338066 prefixEnd_338066 := by exact prefixLift 338066
  have htrace : WordTrace (prefixWord ++ tailWord_338066) baseStart_338066 baseEnd_338066 := by
    simpa [prefixWord, tailWord_338066, baseEnd_338066] using wordTrace_append hprefix tailTrace_338066
  have hstable : (prefixWord ++ tailWord_338066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338066).length < 2 ^ (prefixWord ++ tailWord_338066).sum := by decide
  have hdescent : baseEnd_338066 < baseStart_338066 := by decide
  rcases family_descends (prefixWord ++ tailWord_338066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338106 : List Nat := [3, 1, 1, 1, 2, 2, 9]
def baseStart_338106 : Nat := 118140960795 + 338106 * 2 ^ 59
def prefixEnd_338106 : Nat := 4983230072969 + 3 ^ 40 * 338106 * 2
def baseEnd_338106 : Nat := 34293509169216670107671

theorem tailTrace_338106 : CollatzResearch.WordTrace tailWord_338106 prefixEnd_338106 34293509169216670107671 := by
  unfold tailWord_338106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082934728276795188170543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8221159275404787168454781 3082934728276795188170543)
  ·
    refine ⟨4624402092415192782255815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3082934728276795188170543 4624402092415192782255815)
    ·
      refine ⟨6936603138622789173383723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624402092415192782255815 6936603138622789173383723)
      ·
        refine ⟨10404904707934183760075585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6936603138622789173383723 10404904707934183760075585)
        ·
          refine ⟨7803678530950637820056689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10404904707934183760075585 7803678530950637820056689)
          ·
            refine ⟨5852758898212978365042517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7803678530950637820056689 5852758898212978365042517)
            ·
              refine ⟨34293509169216670107671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5852758898212978365042517 34293509169216670107671)
              ·
                rfl

theorem cell19_338106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_338106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338106 prefixEnd_338106 := by exact prefixLift 338106
  have htrace : WordTrace (prefixWord ++ tailWord_338106) baseStart_338106 baseEnd_338106 := by
    simpa [prefixWord, tailWord_338106, baseEnd_338106] using wordTrace_append hprefix tailTrace_338106
  have hstable : (prefixWord ++ tailWord_338106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338106).length < 2 ^ (prefixWord ++ tailWord_338106).sum := by decide
  have hdescent : baseEnd_338106 < baseStart_338106 := by decide
  rcases family_descends (prefixWord ++ tailWord_338106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338144 : List Nat := [2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_338144 : Nat := 118140960795 + 338144 * 2 ^ 59
def prefixEnd_338144 : Nat := 4983230072969 + 3 ^ 40 * 338144 * 2
def baseEnd_338144 : Nat := 102892090331277181478465

theorem tailTrace_338144 : CollatzResearch.WordTrace tailWord_338144 prefixEnd_338144 102892090331277181478465 := by
  unfold tailWord_338144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6166562443484756621282743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8222083257979675495043657 6166562443484756621282743)
  ·
    refine ⟨9249843665227134931924115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6166562443484756621282743 9249843665227134931924115)
    ·
      refine ⟨13874765497840702397886173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9249843665227134931924115 13874765497840702397886173)
      ·
        refine ⟨5203037061690263399207315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13874765497840702397886173 5203037061690263399207315)
        ·
          refine ⟨7804555592535395098810973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203037061690263399207315 7804555592535395098810973)
          ·
            refine ⟨2926708347200773162054115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7804555592535395098810973 2926708347200773162054115)
            ·
              refine ⟨4390062520801159743081173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926708347200773162054115 4390062520801159743081173)
              ·
                refine ⟨102892090331277181478465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4390062520801159743081173 102892090331277181478465)
                ·
                  rfl

theorem cell19_338144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_338144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338144 prefixEnd_338144 := by exact prefixLift 338144
  have htrace : WordTrace (prefixWord ++ tailWord_338144) baseStart_338144 baseEnd_338144 := by
    simpa [prefixWord, tailWord_338144, baseEnd_338144] using wordTrace_append hprefix tailTrace_338144
  have hstable : (prefixWord ++ tailWord_338144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338144).length < 2 ^ (prefixWord ++ tailWord_338144).sum := by decide
  have hdescent : baseEnd_338144 < baseStart_338144 := by decide
  rcases family_descends (prefixWord ++ tailWord_338144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338178 : List Nat := [3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_338178 : Nat := 118140960795 + 338178 * 2 ^ 59
def prefixEnd_338178 : Nat := 4983230072969 + 3 ^ 40 * 338178 * 2
def baseEnd_338178 : Nat := 102902436015575176722817

theorem tailTrace_338178 : CollatzResearch.WordTrace tailWord_338178 prefixEnd_338178 102902436015575176722817 := by
  unfold tailWord_338178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3083591242211584262325797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8222909979230891366202125 3083591242211584262325797)
  ·
    refine ⟨578173357914672049186087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3083591242211584262325797 578173357914672049186087)
    ·
      refine ⟨867260036872008073779131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578173357914672049186087 867260036872008073779131)
      ·
        refine ⟨1300890055308012110668697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867260036872008073779131 1300890055308012110668697)
        ·
          refine ⟨975667541481009083001523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300890055308012110668697 975667541481009083001523)
          ·
            refine ⟨1463501312221513624502285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975667541481009083001523 1463501312221513624502285)
            ·
              refine ⟨548812992083067609188357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1463501312221513624502285 548812992083067609188357)
              ·
                refine ⟨102902436015575176722817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 548812992083067609188357 102902436015575176722817)
                ·
                  rfl

theorem cell19_338178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_338178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338178 prefixEnd_338178 := by exact prefixLift 338178
  have htrace : WordTrace (prefixWord ++ tailWord_338178) baseStart_338178 baseEnd_338178 := by
    simpa [prefixWord, tailWord_338178, baseEnd_338178] using wordTrace_append hprefix tailTrace_338178
  have hstable : (prefixWord ++ tailWord_338178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338178).length < 2 ^ (prefixWord ++ tailWord_338178).sum := by decide
  have hdescent : baseEnd_338178 < baseStart_338178 := by decide
  rcases family_descends (prefixWord ++ tailWord_338178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338239 : List Nat := [1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_338239 : Nat := 118140960795 + 338239 * 2 ^ 59
def prefixEnd_338239 : Nat := 4983230072969 + 3 ^ 40 * 338239 * 2
def baseEnd_338239 : Nat := 102920997390345109367095

theorem tailTrace_338239 : CollatzResearch.WordTrace tailWord_338239 prefixEnd_338239 102920997390345109367095 := by
  unfold tailWord_338239
  simp only [CollatzResearch.WordTrace]
  refine ⟨12336589821625344467273771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8224393214416896311515847 12336589821625344467273771)
  ·
    refine ⟨18504884732438016700910657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12336589821625344467273771 18504884732438016700910657)
    ·
      refine ⟨13878663549328512525682993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18504884732438016700910657 13878663549328512525682993)
      ·
        refine ⟨10408997661996384394262245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13878663549328512525682993 10408997661996384394262245)
        ·
          refine ⟨1951687061624322073924171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10408997661996384394262245 1951687061624322073924171)
          ·
            refine ⟨2927530592436483110886257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951687061624322073924171 2927530592436483110886257)
            ·
              refine ⟨2195647944327362333164693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927530592436483110886257 2195647944327362333164693)
              ·
                refine ⟨102920997390345109367095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2195647944327362333164693 102920997390345109367095)
                ·
                  rfl

theorem cell19_338239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_338239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338239 prefixEnd_338239 := by exact prefixLift 338239
  have htrace : WordTrace (prefixWord ++ tailWord_338239) baseStart_338239 baseEnd_338239 := by
    simpa [prefixWord, tailWord_338239, baseEnd_338239] using wordTrace_append hprefix tailTrace_338239
  have hstable : (prefixWord ++ tailWord_338239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338239).length < 2 ^ (prefixWord ++ tailWord_338239).sum := by decide
  have hdescent : baseEnd_338239 < baseStart_338239 := by decide
  rcases family_descends (prefixWord ++ tailWord_338239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338256 : List Nat := [2, 1, 1, 1, 1, 6, 4, 3]
def baseStart_338256 : Nat := 118140960795 + 338256 * 2 ^ 59
def prefixEnd_338256 : Nat := 4983230072969 + 3 ^ 40 * 338256 * 2
def baseEnd_338256 : Nat := 102926170232494106989271

theorem tailTrace_338256 : CollatzResearch.WordTrace tailWord_338256 prefixEnd_338256 102926170232494106989271 := by
  unfold tailWord_338256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168604931281878185321311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8224806575042504247095081 6168604931281878185321311)
  ·
    refine ⟨9252907396922817277981967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6168604931281878185321311 9252907396922817277981967)
    ·
      refine ⟨13879361095384225916972951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9252907396922817277981967 13879361095384225916972951)
      ·
        refine ⟨20819041643076338875459427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13879361095384225916972951 20819041643076338875459427)
        ·
          refine ⟨31228562464614508313189141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20819041643076338875459427 31228562464614508313189141)
          ·
            refine ⟨1463838865528805077180741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31228562464614508313189141 1463838865528805077180741)
            ·
              refine ⟨274469787286650951971389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1463838865528805077180741 274469787286650951971389)
              ·
                refine ⟨102926170232494106989271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274469787286650951971389 102926170232494106989271)
                ·
                  rfl

theorem cell19_338256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_338256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338256 prefixEnd_338256 := by exact prefixLift 338256
  have htrace : WordTrace (prefixWord ++ tailWord_338256) baseStart_338256 baseEnd_338256 := by
    simpa [prefixWord, tailWord_338256, baseEnd_338256] using wordTrace_append hprefix tailTrace_338256
  have hstable : (prefixWord ++ tailWord_338256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338256).length < 2 ^ (prefixWord ++ tailWord_338256).sum := by decide
  have hdescent : baseEnd_338256 < baseStart_338256 := by decide
  rcases family_descends (prefixWord ++ tailWord_338256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338277 : List Nat := [1, 3, 1, 3, 1, 3, 7]
def baseStart_338277 : Nat := 118140960795 + 338277 * 2 ^ 59
def prefixEnd_338277 : Nat := 4983230072969 + 3 ^ 40 * 338277 * 2
def baseEnd_338277 : Nat := 34310853404657426840849

theorem tailTrace_338277 : CollatzResearch.WordTrace tailWord_338277 prefixEnd_338277 34310853404657426840849 := by
  unfold tailWord_338277
  simp only [CollatzResearch.WordTrace]
  refine ⟨12337975795487676957157085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8225317196991784638104723 12337975795487676957157085)
  ·
    refine ⟨4626740923307878858933907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12337975795487676957157085 4626740923307878858933907)
    ·
      refine ⟨6940111384961818288400861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4626740923307878858933907 6940111384961818288400861)
      ·
        refine ⟨2602541769360681858150323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6940111384961818288400861 2602541769360681858150323)
        ·
          refine ⟨3903812654041022787225485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602541769360681858150323 3903812654041022787225485)
          ·
            refine ⟨1463929745265383545209557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3903812654041022787225485 1463929745265383545209557)
            ·
              refine ⟨34310853404657426840849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1463929745265383545209557 34310853404657426840849)
              ·
                rfl

theorem cell19_338277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_338277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338277 prefixEnd_338277 := by exact prefixLift 338277
  have htrace : WordTrace (prefixWord ++ tailWord_338277) baseStart_338277 baseEnd_338277 := by
    simpa [prefixWord, tailWord_338277, baseEnd_338277] using wordTrace_append hprefix tailTrace_338277
  have hstable : (prefixWord ++ tailWord_338277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338277).length < 2 ^ (prefixWord ++ tailWord_338277).sum := by decide
  have hdescent : baseEnd_338277 < baseStart_338277 := by decide
  rcases family_descends (prefixWord ++ tailWord_338277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338315 : List Nat := [1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_338315 : Nat := 118140960795 + 338315 * 2 ^ 59
def prefixEnd_338315 : Nat := 4983230072969 + 3 ^ 40 * 338315 * 2
def baseEnd_338315 : Nat := 102944123037599451677999

theorem tailTrace_338315 : CollatzResearch.WordTrace tailWord_338315 prefixEnd_338315 102944123037599451677999 := by
  unfold tailWord_338315
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339361769350009447040399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8226241179566672964693599 12339361769350009447040399)
  ·
    refine ⟨18509042654025014170560599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12339361769350009447040399 18509042654025014170560599)
    ·
      refine ⟨27763563981037521255840899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18509042654025014170560599 27763563981037521255840899)
      ·
        refine ⟨41645345971556281883761349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27763563981037521255840899 41645345971556281883761349)
        ·
          refine ⟨7808502369666802853205253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41645345971556281883761349 7808502369666802853205253)
          ·
            refine ⟨1464094194312525534975985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7808502369666802853205253 1464094194312525534975985)
            ·
              refine ⟨1098070645734394151231989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1464094194312525534975985 1098070645734394151231989)
              ·
                refine ⟨102944123037599451677999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1098070645734394151231989 102944123037599451677999)
                ·
                  rfl

theorem cell19_338315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_338315 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338315 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338315 prefixEnd_338315 := by exact prefixLift 338315
  have htrace : WordTrace (prefixWord ++ tailWord_338315) baseStart_338315 baseEnd_338315 := by
    simpa [prefixWord, tailWord_338315, baseEnd_338315] using wordTrace_append hprefix tailTrace_338315
  have hstable : (prefixWord ++ tailWord_338315).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338315).length < 2 ^ (prefixWord ++ tailWord_338315).sum := by decide
  have hdescent : baseEnd_338315 < baseStart_338315 := by decide
  rcases family_descends (prefixWord ++ tailWord_338315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338326 : List Nat := [5, 3, 1, 2, 2, 6]
def baseStart_338326 : Nat := 118140960795 + 338326 * 2 ^ 59
def prefixEnd_338326 : Nat := 4983230072969 + 3 ^ 40 * 338326 * 2
def baseEnd_338326 : Nat := 11438607796750520603725

theorem tailTrace_338326 : CollatzResearch.WordTrace tailWord_338326 prefixEnd_338326 11438607796750520603725 := by
  unfold tailWord_338326
  simp only [CollatzResearch.WordTrace]
  refine ⟨771235185769384895355677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8226508648206772217127221 771235185769384895355677)
  ·
    refine ⟨289213194663519335758379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 771235185769384895355677 289213194663519335758379)
    ·
      refine ⟨433819791995279003637569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289213194663519335758379 433819791995279003637569)
      ·
        refine ⟨325364843996459252728177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433819791995279003637569 325364843996459252728177)
        ·
          refine ⟨244023632997344439546133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325364843996459252728177 244023632997344439546133)
          ·
            refine ⟨11438607796750520603725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 244023632997344439546133 11438607796750520603725)
            ·
              rfl

theorem cell19_338326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 6].length) (baseStart_338326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338326 prefixEnd_338326 := by exact prefixLift 338326
  have htrace : WordTrace (prefixWord ++ tailWord_338326) baseStart_338326 baseEnd_338326 := by
    simpa [prefixWord, tailWord_338326, baseEnd_338326] using wordTrace_append hprefix tailTrace_338326
  have hstable : (prefixWord ++ tailWord_338326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338326).length < 2 ^ (prefixWord ++ tailWord_338326).sum := by decide
  have hdescent : baseEnd_338326 < baseStart_338326 := by decide
  rcases family_descends (prefixWord ++ tailWord_338326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338421 : List Nat := [1, 3, 5, 1, 3, 1, 2, 3]
def baseStart_338421 : Nat := 118140960795 + 338421 * 2 ^ 59
def prefixEnd_338421 : Nat := 4983230072969 + 3 ^ 40 * 338421 * 2
def baseEnd_338421 : Nat := 102976377229822613322155

theorem tailTrace_338421 : CollatzResearch.WordTrace tailWord_338421 prefixEnd_338421 102976377229822613322155 := by
  unfold tailWord_338421
  simp only [CollatzResearch.WordTrace]
  refine ⟨12343227906965989550399117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8228818604643993033599411 12343227906965989550399117)
  ·
    refine ⟨4628710465112246081399669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12343227906965989550399117 4628710465112246081399669)
    ·
      refine ⟨433941606104273070131219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4628710465112246081399669 433941606104273070131219)
      ·
        refine ⟨650912409156409605196829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433941606104273070131219 650912409156409605196829)
        ·
          refine ⟨244092153433653601948811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 650912409156409605196829 244092153433653601948811)
          ·
            refine ⟨366138230150480402923217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244092153433653601948811 366138230150480402923217)
            ·
              refine ⟨274603672612860302192413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366138230150480402923217 274603672612860302192413)
              ·
                refine ⟨102976377229822613322155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274603672612860302192413 102976377229822613322155)
                ·
                  rfl

theorem cell19_338421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 3].length) (baseStart_338421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338421 prefixEnd_338421 := by exact prefixLift 338421
  have htrace : WordTrace (prefixWord ++ tailWord_338421) baseStart_338421 baseEnd_338421 := by
    simpa [prefixWord, tailWord_338421, baseEnd_338421] using wordTrace_append hprefix tailTrace_338421
  have hstable : (prefixWord ++ tailWord_338421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338421).length < 2 ^ (prefixWord ++ tailWord_338421).sum := by decide
  have hdescent : baseEnd_338421 < baseStart_338421 := by decide
  rcases family_descends (prefixWord ++ tailWord_338421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338429 : List Nat := [1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_338429 : Nat := 118140960795 + 338429 * 2 ^ 59
def prefixEnd_338429 : Nat := 4983230072969 + 3 ^ 40 * 338429 * 2
def baseEnd_338429 : Nat := 102978811508480965144355

theorem tailTrace_338429 : CollatzResearch.WordTrace tailWord_338429 prefixEnd_338429 102978811508480965144355 := by
  unfold tailWord_338429
  simp only [CollatzResearch.WordTrace]
  refine ⟨12343519690937006916690341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8229013127291337944460227 12343519690937006916690341)
  ·
    refine ⟨2314409942050688796879439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12343519690937006916690341 2314409942050688796879439)
    ·
      refine ⟨3471614913076033195319159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314409942050688796879439 3471614913076033195319159)
      ·
        refine ⟨5207422369614049792978739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471614913076033195319159 5207422369614049792978739)
        ·
          refine ⟨7811133554421074689468109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5207422369614049792978739 7811133554421074689468109)
          ·
            refine ⟨2929175082907903008550541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7811133554421074689468109 2929175082907903008550541)
            ·
              refine ⟨1098440656090463628206453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2929175082907903008550541 1098440656090463628206453)
              ·
                refine ⟨102978811508480965144355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1098440656090463628206453 102978811508480965144355)
                ·
                  rfl

theorem cell19_338429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_338429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338429 prefixEnd_338429 := by exact prefixLift 338429
  have htrace : WordTrace (prefixWord ++ tailWord_338429) baseStart_338429 baseEnd_338429 := by
    simpa [prefixWord, tailWord_338429, baseEnd_338429] using wordTrace_append hprefix tailTrace_338429
  have hstable : (prefixWord ++ tailWord_338429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338429).length < 2 ^ (prefixWord ++ tailWord_338429).sum := by decide
  have hdescent : baseEnd_338429 < baseStart_338429 := by decide
  rcases family_descends (prefixWord ++ tailWord_338429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338446 : List Nat := [4, 1, 1, 2, 3, 3, 5]
def baseStart_338446 : Nat := 118140960795 + 338446 * 2 ^ 59
def prefixEnd_338446 : Nat := 4983230072969 + 3 ^ 40 * 338446 * 2
def baseEnd_338446 : Nat := 34327994783543320922177

theorem tailTrace_338446 : CollatzResearch.WordTrace tailWord_338446 prefixEnd_338446 34327994783543320922177 := by
  unfold tailWord_338446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543017466484427352507399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8229426487916945880039461 1543017466484427352507399)
  ·
    refine ⟨2314526199726641028761099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1543017466484427352507399 2314526199726641028761099)
    ·
      refine ⟨3471789299589961543141649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314526199726641028761099 3471789299589961543141649)
      ·
        refine ⟨2603841974692471157356237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3471789299589961543141649 2603841974692471157356237)
        ·
          refine ⟨976440740509676684008589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2603841974692471157356237 976440740509676684008589)
          ·
            refine ⟨366165277691128756503221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 976440740509676684008589 366165277691128756503221)
            ·
              refine ⟨34327994783543320922177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 366165277691128756503221 34327994783543320922177)
              ·
                rfl

theorem cell19_338446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_338446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338446 prefixEnd_338446 := by exact prefixLift 338446
  have htrace : WordTrace (prefixWord ++ tailWord_338446) baseStart_338446 baseEnd_338446 := by
    simpa [prefixWord, tailWord_338446, baseEnd_338446] using wordTrace_append hprefix tailTrace_338446
  have hstable : (prefixWord ++ tailWord_338446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338446).length < 2 ^ (prefixWord ++ tailWord_338446).sum := by decide
  have hdescent : baseEnd_338446 < baseStart_338446 := by decide
  rcases family_descends (prefixWord ++ tailWord_338446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338467 : List Nat := [1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_338467 : Nat := 118140960795 + 338467 * 2 ^ 59
def prefixEnd_338467 : Nat := 4983230072969 + 3 ^ 40 * 338467 * 2
def baseEnd_338467 : Nat := 102990374332108136299807

theorem tailTrace_338467 : CollatzResearch.WordTrace tailWord_338467 prefixEnd_338467 102990374332108136299807 := by
  unfold tailWord_338467
  simp only [CollatzResearch.WordTrace]
  refine ⟨12344905664799339406573655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8229937109866226271049103 12344905664799339406573655)
  ·
    refine ⟨18517358497199009109860483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12344905664799339406573655 18517358497199009109860483)
    ·
      refine ⟨27776037745798513664790725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18517358497199009109860483 27776037745798513664790725)
      ·
        refine ⟨5208007077337221312148261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27776037745798513664790725 5208007077337221312148261)
        ·
          refine ⟨976501327000728996027799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5208007077337221312148261 976501327000728996027799)
          ·
            refine ⟨1464751990501093494041699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976501327000728996027799 1464751990501093494041699)
            ·
              refine ⟨2197127985751640241062549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464751990501093494041699 2197127985751640241062549)
              ·
                refine ⟨102990374332108136299807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2197127985751640241062549 102990374332108136299807)
                ·
                  rfl

theorem cell19_338467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_338467 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338467 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338467 prefixEnd_338467 := by exact prefixLift 338467
  have htrace : WordTrace (prefixWord ++ tailWord_338467) baseStart_338467 baseEnd_338467 := by
    simpa [prefixWord, tailWord_338467, baseEnd_338467] using wordTrace_append hprefix tailTrace_338467
  have hstable : (prefixWord ++ tailWord_338467).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338467).length < 2 ^ (prefixWord ++ tailWord_338467).sum := by decide
  have hdescent : baseEnd_338467 < baseStart_338467 := by decide
  rcases family_descends (prefixWord ++ tailWord_338467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338636 : List Nat := [2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_338636 : Nat := 118140960795 + 338636 * 2 ^ 59
def prefixEnd_338636 : Nat := 4983230072969 + 3 ^ 40 * 338636 * 2
def baseEnd_338636 : Nat := 103041798468765818543791

theorem tailTrace_338636 : CollatzResearch.WordTrace tailWord_338636 prefixEnd_338636 103041798468765818543791 := by
  unfold tailWord_338636
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175534800593540634737881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8234046400791387512983841 6175534800593540634737881)
  ·
    refine ⟨4631651100445155476053411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6175534800593540634737881 4631651100445155476053411)
    ·
      refine ⟨6947476650667733214080117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4631651100445155476053411 6947476650667733214080117)
      ·
        refine ⟨651325936000099988820011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6947476650667733214080117 651325936000099988820011)
        ·
          refine ⟨976988904000149983230017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651325936000099988820011 976988904000149983230017)
          ·
            refine ⟨732741678000112487422513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 976988904000149983230017 732741678000112487422513)
            ·
              refine ⟨549556258500084365566885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732741678000112487422513 549556258500084365566885)
              ·
                refine ⟨103041798468765818543791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 549556258500084365566885 103041798468765818543791)
                ·
                  rfl

theorem cell19_338636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_338636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338636 prefixEnd_338636 := by exact prefixLift 338636
  have htrace : WordTrace (prefixWord ++ tailWord_338636) baseStart_338636 baseEnd_338636 := by
    simpa [prefixWord, tailWord_338636, baseEnd_338636] using wordTrace_append hprefix tailTrace_338636
  have hstable : (prefixWord ++ tailWord_338636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338636).length < 2 ^ (prefixWord ++ tailWord_338636).sum := by decide
  have hdescent : baseEnd_338636 < baseStart_338636 := by decide
  rcases family_descends (prefixWord ++ tailWord_338636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338638 : List Nat := [4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_338638 : Nat := 118140960795 + 338638 * 2 ^ 59
def prefixEnd_338638 : Nat := 4983230072969 + 3 ^ 40 * 338638 * 2
def baseEnd_338638 : Nat := 103042407038430406499341

theorem tailTrace_338638 : CollatzResearch.WordTrace tailWord_338638 prefixEnd_338638 103042407038430406499341 := by
  unfold tailWord_338638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543892818397479451381071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8234095031453223740699045 1543892818397479451381071)
  ·
    refine ⟨2315839227596219177071607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1543892818397479451381071 2315839227596219177071607)
    ·
      refine ⟨3473758841394328765607411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2315839227596219177071607 3473758841394328765607411)
      ·
        refine ⟨5210638262091493148411117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473758841394328765607411 5210638262091493148411117)
        ·
          refine ⟨1953989348284309930654169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5210638262091493148411117 1953989348284309930654169)
          ·
            refine ⟨1465492011213232447990627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1953989348284309930654169 1465492011213232447990627)
            ·
              refine ⟨2198238016819848671985941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465492011213232447990627 2198238016819848671985941)
              ·
                refine ⟨103042407038430406499341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2198238016819848671985941 103042407038430406499341)
                ·
                  rfl

theorem cell19_338638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_338638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338638 prefixEnd_338638 := by exact prefixLift 338638
  have htrace : WordTrace (prefixWord ++ tailWord_338638) baseStart_338638 baseEnd_338638 := by
    simpa [prefixWord, tailWord_338638, baseEnd_338638] using wordTrace_append hprefix tailTrace_338638
  have hstable : (prefixWord ++ tailWord_338638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338638).length < 2 ^ (prefixWord ++ tailWord_338638).sum := by decide
  have hdescent : baseEnd_338638 < baseStart_338638 := by decide
  rcases family_descends (prefixWord ++ tailWord_338638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338657 : List Nat := [1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_338657 : Nat := 118140960795 + 338657 * 2 ^ 59
def prefixEnd_338657 : Nat := 4983230072969 + 3 ^ 40 * 338657 * 2
def baseEnd_338657 : Nat := 103048188450243992077067

theorem tailTrace_338657 : CollatzResearch.WordTrace tailWord_338657 prefixEnd_338657 103048188450243992077067 := by
  unfold tailWord_338657
  simp only [CollatzResearch.WordTrace]
  refine ⟨12351835534111001855990225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8234557022740667903993483 12351835534111001855990225)
  ·
    refine ⟨9263876650583251391992669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12351835534111001855990225 9263876650583251391992669)
    ·
      refine ⟨3473953743968719271997251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9263876650583251391992669 3473953743968719271997251)
      ·
        refine ⟨5210930615953078907995877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473953743968719271997251 5210930615953078907995877)
        ·
          refine ⟨977049490491202295249227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5210930615953078907995877 977049490491202295249227)
          ·
            refine ⟨1465574235736803442873841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977049490491202295249227 1465574235736803442873841)
            ·
              refine ⟨1099180676802602582155381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465574235736803442873841 1099180676802602582155381)
              ·
                refine ⟨103048188450243992077067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1099180676802602582155381 103048188450243992077067)
                ·
                  rfl

theorem cell19_338657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_338657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338657 prefixEnd_338657 := by exact prefixLift 338657
  have htrace : WordTrace (prefixWord ++ tailWord_338657) baseStart_338657 baseEnd_338657 := by
    simpa [prefixWord, tailWord_338657, baseEnd_338657] using wordTrace_append hprefix tailTrace_338657
  have hstable : (prefixWord ++ tailWord_338657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338657).length < 2 ^ (prefixWord ++ tailWord_338657).sum := by decide
  have hdescent : baseEnd_338657 < baseStart_338657 := by decide
  rcases family_descends (prefixWord ++ tailWord_338657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338765 : List Nat := [1, 6, 1, 2, 2, 2, 2, 3]
def baseStart_338765 : Nat := 118140960795 + 338765 * 2 ^ 59
def prefixEnd_338765 : Nat := 4983230072969 + 3 ^ 40 * 338765 * 2
def baseEnd_338765 : Nat := 103081051212131741676773

theorem tailTrace_338765 : CollatzResearch.WordTrace tailWord_338765 prefixEnd_338765 103081051212131741676773 := by
  unfold tailWord_338765
  simp only [CollatzResearch.WordTrace]
  refine ⟨12355774617719736300921749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8237183078479824200614499 12355774617719736300921749)
  ·
    refine ⟨579176935205612639105707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12355774617719736300921749 579176935205612639105707)
    ·
      refine ⟨868765402808418958658561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579176935205612639105707 868765402808418958658561)
      ·
        refine ⟨651574052106314218993921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 868765402808418958658561 651574052106314218993921)
        ·
          refine ⟨488680539079735664245441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651574052106314218993921 488680539079735664245441)
          ·
            refine ⟨366510404309801748184081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488680539079735664245441 366510404309801748184081)
            ·
              refine ⟨274882803232351311138061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366510404309801748184081 274882803232351311138061)
              ·
                refine ⟨103081051212131741676773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274882803232351311138061 103081051212131741676773)
                ·
                  rfl

theorem cell19_338765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_338765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338765 prefixEnd_338765 := by exact prefixLift 338765
  have htrace : WordTrace (prefixWord ++ tailWord_338765) baseStart_338765 baseEnd_338765 := by
    simpa [prefixWord, tailWord_338765, baseEnd_338765] using wordTrace_append hprefix tailTrace_338765
  have hstable : (prefixWord ++ tailWord_338765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338765).length < 2 ^ (prefixWord ++ tailWord_338765).sum := by decide
  have hdescent : baseEnd_338765 < baseStart_338765 := by decide
  rcases family_descends (prefixWord ++ tailWord_338765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338786 : List Nat := [3, 3, 2, 1, 4, 1, 5]
def baseStart_338786 : Nat := 118140960795 + 338786 * 2 ^ 59
def prefixEnd_338786 : Nat := 4983230072969 + 3 ^ 40 * 338786 * 2
def baseEnd_338786 : Nat := 34362480397869971736683

theorem tailTrace_338786 : CollatzResearch.WordTrace tailWord_338786 prefixEnd_338786 34362480397869971736683 := by
  unfold tailWord_338786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089135137660914221859053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8237693700429104591624141 3089135137660914221859053)
  ·
    refine ⟨1158425676622842833197145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3089135137660914221859053 1158425676622842833197145)
    ·
      refine ⟨868819257467132124897859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1158425676622842833197145 868819257467132124897859)
      ·
        refine ⟨1303228886200698187346789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868819257467132124897859 1303228886200698187346789)
        ·
          refine ⟨244355416162630910127523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1303228886200698187346789 244355416162630910127523)
          ·
            refine ⟨366533124243946365191285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244355416162630910127523 366533124243946365191285)
            ·
              refine ⟨34362480397869971736683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 366533124243946365191285 34362480397869971736683)
              ·
                rfl

theorem cell19_338786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_338786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338786 prefixEnd_338786 := by exact prefixLift 338786
  have htrace : WordTrace (prefixWord ++ tailWord_338786) baseStart_338786 baseEnd_338786 := by
    simpa [prefixWord, tailWord_338786, baseEnd_338786] using wordTrace_append hprefix tailTrace_338786
  have hstable : (prefixWord ++ tailWord_338786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338786).length < 2 ^ (prefixWord ++ tailWord_338786).sum := by decide
  have hdescent : baseEnd_338786 < baseStart_338786 := by decide
  rcases family_descends (prefixWord ++ tailWord_338786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338809 : List Nat := [1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_338809 : Nat := 118140960795 + 338809 * 2 ^ 59
def prefixEnd_338809 : Nat := 4983230072969 + 3 ^ 40 * 338809 * 2
def baseEnd_338809 : Nat := 103094439744752676698875

theorem tailTrace_338809 : CollatzResearch.WordTrace tailWord_338809 prefixEnd_338809 103094439744752676698875 := by
  unfold tailWord_338809
  simp only [CollatzResearch.WordTrace]
  refine ⟨12357379429560331815523481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8238252953040221210348987 12357379429560331815523481)
  ·
    refine ⟨9268034572170248861642611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12357379429560331815523481 9268034572170248861642611)
    ·
      refine ⟨13902051858255373292463917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9268034572170248861642611 13902051858255373292463917)
      ·
        refine ⟨5213269446845764984673969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13902051858255373292463917 5213269446845764984673969)
        ·
          refine ⟨3909952085134323738505477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5213269446845764984673969 3909952085134323738505477)
          ·
            refine ⟨733116015962685700969777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3909952085134323738505477 733116015962685700969777)
            ·
              refine ⟨549837011972014275727333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733116015962685700969777 549837011972014275727333)
              ·
                refine ⟨103094439744752676698875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 549837011972014275727333 103094439744752676698875)
                ·
                  rfl

theorem cell19_338809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_338809 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338809 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338809 prefixEnd_338809 := by exact prefixLift 338809
  have htrace : WordTrace (prefixWord ++ tailWord_338809) baseStart_338809 baseEnd_338809 := by
    simpa [prefixWord, tailWord_338809, baseEnd_338809] using wordTrace_append hprefix tailTrace_338809
  have hstable : (prefixWord ++ tailWord_338809).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338809).length < 2 ^ (prefixWord ++ tailWord_338809).sum := by decide
  have hdescent : baseEnd_338809 < baseStart_338809 := by decide
  rcases family_descends (prefixWord ++ tailWord_338809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338811 : List Nat := [1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_338811 : Nat := 118140960795 + 338811 * 2 ^ 59
def prefixEnd_338811 : Nat := 4983230072969 + 3 ^ 40 * 338811 * 2
def baseEnd_338811 : Nat := 103095048314417264654425

theorem tailTrace_338811 : CollatzResearch.WordTrace tailWord_338811 prefixEnd_338811 103095048314417264654425 := by
  unfold tailWord_338811
  simp only [CollatzResearch.WordTrace]
  refine ⟨12357452375553086157096287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8238301583702057438064191 12357452375553086157096287)
  ·
    refine ⟨18536178563329629235644431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12357452375553086157096287 18536178563329629235644431)
    ·
      refine ⟨27804267844994443853466647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18536178563329629235644431 27804267844994443853466647)
      ·
        refine ⟨41706401767491665780199971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27804267844994443853466647 41706401767491665780199971)
        ·
          refine ⟨62559602651237498670299957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41706401767491665780199971 62559602651237498670299957)
          ·
            refine ⟨5864962748553515500340621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62559602651237498670299957 5864962748553515500340621)
            ·
              refine ⟨2199361030707568312627733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5864962748553515500340621 2199361030707568312627733)
              ·
                refine ⟨103095048314417264654425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2199361030707568312627733 103095048314417264654425)
                ·
                  rfl

theorem cell19_338811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_338811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338811 prefixEnd_338811 := by exact prefixLift 338811
  have htrace : WordTrace (prefixWord ++ tailWord_338811) baseStart_338811 baseEnd_338811 := by
    simpa [prefixWord, tailWord_338811, baseEnd_338811] using wordTrace_append hprefix tailTrace_338811
  have hstable : (prefixWord ++ tailWord_338811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338811).length < 2 ^ (prefixWord ++ tailWord_338811).sum := by decide
  have hdescent : baseEnd_338811 < baseStart_338811 := by decide
  rcases family_descends (prefixWord ++ tailWord_338811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338887 : List Nat := [1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_338887 : Nat := 118140960795 + 338887 * 2 ^ 59
def prefixEnd_338887 : Nat := 4983230072969 + 3 ^ 40 * 338887 * 2
def baseEnd_338887 : Nat := 103118173961671606965329

theorem tailTrace_338887 : CollatzResearch.WordTrace tailWord_338887 prefixEnd_338887 103118173961671606965329 := by
  unfold tailWord_338887
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360224323277751136862915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8240149548851834091241943 12360224323277751136862915)
  ·
    refine ⟨18540336484916626705294373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12360224323277751136862915 18540336484916626705294373)
    ·
      refine ⟨3476313090921867507242695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18540336484916626705294373 3476313090921867507242695)
      ·
        refine ⟨5214469636382801260864043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476313090921867507242695 5214469636382801260864043)
        ·
          refine ⟨7821704454574201891296065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214469636382801260864043 7821704454574201891296065)
          ·
            refine ⟨5866278340930651418472049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7821704454574201891296065 5866278340930651418472049)
            ·
              refine ⟨4399708755697988563854037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5866278340930651418472049 4399708755697988563854037)
              ·
                refine ⟨103118173961671606965329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4399708755697988563854037 103118173961671606965329)
                ·
                  rfl

theorem cell19_338887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_338887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338887 prefixEnd_338887 := by exact prefixLift 338887
  have htrace : WordTrace (prefixWord ++ tailWord_338887) baseStart_338887 baseEnd_338887 := by
    simpa [prefixWord, tailWord_338887, baseEnd_338887] using wordTrace_append hprefix tailTrace_338887
  have hstable : (prefixWord ++ tailWord_338887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338887).length < 2 ^ (prefixWord ++ tailWord_338887).sum := by decide
  have hdescent : baseEnd_338887 < baseStart_338887 := by decide
  rcases family_descends (prefixWord ++ tailWord_338887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338902 : List Nat := [5, 2, 1, 1, 2, 2, 6]
def baseStart_338902 : Nat := 118140960795 + 338902 * 2 ^ 59
def prefixEnd_338902 : Nat := 4983230072969 + 3 ^ 40 * 338902 * 2
def baseEnd_338902 : Nat := 34374246078052005543985

theorem tailTrace_338902 : CollatzResearch.WordTrace tailWord_338902 prefixEnd_338902 34374246078052005543985 := by
  unfold tailWord_338902
  simp only [CollatzResearch.WordTrace]
  refine ⟨772548213638963043666185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8240514278815605799105973 772548213638963043666185)
  ·
    refine ⟨579411160229222282749639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 772548213638963043666185 579411160229222282749639)
    ·
      refine ⟨869116740343833424124459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579411160229222282749639 869116740343833424124459)
      ·
        refine ⟨1303675110515750136186689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869116740343833424124459 1303675110515750136186689)
        ·
          refine ⟨977756332886812602140017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1303675110515750136186689 977756332886812602140017)
          ·
            refine ⟨733317249665109451605013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977756332886812602140017 733317249665109451605013)
            ·
              refine ⟨34374246078052005543985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 733317249665109451605013 34374246078052005543985)
              ·
                rfl

theorem cell19_338902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_338902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338902 prefixEnd_338902 := by exact prefixLift 338902
  have htrace : WordTrace (prefixWord ++ tailWord_338902) baseStart_338902 baseEnd_338902 := by
    simpa [prefixWord, tailWord_338902, baseEnd_338902] using wordTrace_append hprefix tailTrace_338902
  have hstable : (prefixWord ++ tailWord_338902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338902).length < 2 ^ (prefixWord ++ tailWord_338902).sum := by decide
  have hdescent : baseEnd_338902 < baseStart_338902 := by decide
  rcases family_descends (prefixWord ++ tailWord_338902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338932 : List Nat := [2, 6, 2, 1, 1, 2, 2, 3]
def baseStart_338932 : Nat := 118140960795 + 338932 * 2 ^ 59
def prefixEnd_338932 : Nat := 4983230072969 + 3 ^ 40 * 338932 * 2
def baseEnd_338932 : Nat := 103131866779124835965207

theorem tailTrace_338932 : CollatzResearch.WordTrace tailWord_338932 prefixEnd_338932 103131866779124835965207 := by
  unfold tailWord_338932
  simp only [CollatzResearch.WordTrace]
  refine ⟨6180932804057361911125525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8241243738743149214834033 6180932804057361911125525)
  ·
    refine ⟨289731225190188839584009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6180932804057361911125525 289731225190188839584009)
    ·
      refine ⟨217298418892641629688007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289731225190188839584009 217298418892641629688007)
      ·
        refine ⟨325947628338962444532011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217298418892641629688007 325947628338962444532011)
        ·
          refine ⟨488921442508443666798017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325947628338962444532011 488921442508443666798017)
          ·
            refine ⟨366691081881332750098513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488921442508443666798017 366691081881332750098513)
            ·
              refine ⟨275018311410999562573885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366691081881332750098513 275018311410999562573885)
              ·
                refine ⟨103131866779124835965207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275018311410999562573885 103131866779124835965207)
                ·
                  rfl

theorem cell19_338932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_338932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338932 prefixEnd_338932 := by exact prefixLift 338932
  have htrace : WordTrace (prefixWord ++ tailWord_338932) baseStart_338932 baseEnd_338932 := by
    simpa [prefixWord, tailWord_338932, baseEnd_338932] using wordTrace_append hprefix tailTrace_338932
  have hstable : (prefixWord ++ tailWord_338932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338932).length < 2 ^ (prefixWord ++ tailWord_338932).sum := by decide
  have hdescent : baseEnd_338932 < baseStart_338932 := by decide
  rcases family_descends (prefixWord ++ tailWord_338932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338940 : List Nat := [2, 2, 2, 1, 2, 5, 2, 3]
def baseStart_338940 : Nat := 118140960795 + 338940 * 2 ^ 59
def prefixEnd_338940 : Nat := 4983230072969 + 3 ^ 40 * 338940 * 2
def baseEnd_338940 : Nat := 103134301057783187787407

theorem tailTrace_338940 : CollatzResearch.WordTrace tailWord_338940 prefixEnd_338940 103134301057783187787407 := by
  unfold tailWord_338940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181078696042870594271137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8241438261390494125694849 6181078696042870594271137)
  ·
    refine ⟨4635809022032152945703353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6181078696042870594271137 4635809022032152945703353)
    ·
      refine ⟨3476856766524114709277515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4635809022032152945703353 3476856766524114709277515)
      ·
        refine ⟨5215285149786172063916273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476856766524114709277515 5215285149786172063916273)
        ·
          refine ⟨3911463862339629047937205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5215285149786172063916273 3911463862339629047937205)
          ·
            refine ⟨366699737094340223244113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3911463862339629047937205 366699737094340223244113)
            ·
              refine ⟨275024802820755167433085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366699737094340223244113 275024802820755167433085)
              ·
                refine ⟨103134301057783187787407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275024802820755167433085 103134301057783187787407)
                ·
                  rfl

theorem cell19_338940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_338940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338940 prefixEnd_338940 := by exact prefixLift 338940
  have htrace : WordTrace (prefixWord ++ tailWord_338940) baseStart_338940 baseEnd_338940 := by
    simpa [prefixWord, tailWord_338940, baseEnd_338940] using wordTrace_append hprefix tailTrace_338940
  have hstable : (prefixWord ++ tailWord_338940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338940).length < 2 ^ (prefixWord ++ tailWord_338940).sum := by decide
  have hdescent : baseEnd_338940 < baseStart_338940 := by decide
  rcases family_descends (prefixWord ++ tailWord_338940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338980 : List Nat := [2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_338980 : Nat := 118140960795 + 338980 * 2 ^ 59
def prefixEnd_338980 : Nat := 4983230072969 + 3 ^ 40 * 338980 * 2
def baseEnd_338980 : Nat := 103146472451074946898409

theorem tailTrace_338980 : CollatzResearch.WordTrace tailWord_338980 prefixEnd_338980 103146472451074946898409 := by
  unfold tailWord_338980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181808155970414009999197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8242410874627218679998929 6181808155970414009999197)
  ·
    refine ⟨2318178058488905253749699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6181808155970414009999197 2318178058488905253749699)
    ·
      refine ⟨3477267087733357880624549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318178058488905253749699 3477267087733357880624549)
      ·
        refine ⟨651987578950004602617103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3477267087733357880624549 651987578950004602617103)
        ·
          refine ⟨977981368425006903925655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651987578950004602617103 977981368425006903925655)
          ·
            refine ⟨1466972052637510355888483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977981368425006903925655 1466972052637510355888483)
            ·
              refine ⟨2200458078956265533832725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466972052637510355888483 2200458078956265533832725)
              ·
                refine ⟨103146472451074946898409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2200458078956265533832725 103146472451074946898409)
                ·
                  rfl

theorem cell19_338980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_338980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_338980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_338980 prefixEnd_338980 := by exact prefixLift 338980
  have htrace : WordTrace (prefixWord ++ tailWord_338980) baseStart_338980 baseEnd_338980 := by
    simpa [prefixWord, tailWord_338980, baseEnd_338980] using wordTrace_append hprefix tailTrace_338980
  have hstable : (prefixWord ++ tailWord_338980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338980).length < 2 ^ (prefixWord ++ tailWord_338980).sum := by decide
  have hdescent : baseEnd_338980 < baseStart_338980 := by decide
  rcases family_descends (prefixWord ++ tailWord_338980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339054 : List Nat := [4, 1, 2, 2, 1, 3, 3, 3]
def baseStart_339054 : Nat := 118140960795 + 339054 * 2 ^ 59
def prefixEnd_339054 : Nat := 4983230072969 + 3 ^ 40 * 339054 * 2
def baseEnd_339054 : Nat := 103168989528664701253763

theorem tailTrace_339054 : CollatzResearch.WordTrace tailWord_339054 prefixEnd_339054 103168989528664701253763 := by
  unfold tailWord_339054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545789414209092332274027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8244210209115159105461477 1545789414209092332274027)
  ·
    refine ⟨2318684121313638498411041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545789414209092332274027 2318684121313638498411041)
    ·
      refine ⟨1739013090985228873808281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2318684121313638498411041 1739013090985228873808281)
      ·
        refine ⟨1304259818238921655356211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1739013090985228873808281 1304259818238921655356211)
        ·
          refine ⟨1956389727358382483034317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304259818238921655356211 1956389727358382483034317)
          ·
            refine ⟨733646147759393431137869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1956389727358382483034317 733646147759393431137869)
            ·
              refine ⟨275117305409772536676701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 733646147759393431137869 275117305409772536676701)
              ·
                refine ⟨103168989528664701253763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275117305409772536676701 103168989528664701253763)
                ·
                  rfl

theorem cell19_339054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_339054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339054 prefixEnd_339054 := by exact prefixLift 339054
  have htrace : WordTrace (prefixWord ++ tailWord_339054) baseStart_339054 baseEnd_339054 := by
    simpa [prefixWord, tailWord_339054, baseEnd_339054] using wordTrace_append hprefix tailTrace_339054
  have hstable : (prefixWord ++ tailWord_339054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339054).length < 2 ^ (prefixWord ++ tailWord_339054).sum := by decide
  have hdescent : baseEnd_339054 < baseStart_339054 := by decide
  rcases family_descends (prefixWord ++ tailWord_339054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339056 : List Nat := [2, 1, 1, 1, 5, 1, 5, 3]
def baseStart_339056 : Nat := 118140960795 + 339056 * 2 ^ 59
def prefixEnd_339056 : Nat := 4983230072969 + 3 ^ 40 * 339056 * 2
def baseEnd_339056 : Nat := 103169598098329289209313

theorem tailTrace_339056 : CollatzResearch.WordTrace tailWord_339056 prefixEnd_339056 103169598098329289209313 := by
  unfold tailWord_339056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183194129832746499882511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8244258839776995333176681 6183194129832746499882511)
  ·
    refine ⟨9274791194749119749823767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6183194129832746499882511 9274791194749119749823767)
    ·
      refine ⟨13912186792123679624735651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9274791194749119749823767 13912186792123679624735651)
      ·
        refine ⟨20868280188185519437103477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13912186792123679624735651 20868280188185519437103477)
        ·
          refine ⟨1956401267642392447228451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20868280188185519437103477 1956401267642392447228451)
          ·
            refine ⟨2934601901463588670842677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956401267642392447228451 2934601901463588670842677)
            ·
              refine ⟨275118928262211437891501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2934601901463588670842677 275118928262211437891501)
              ·
                refine ⟨103169598098329289209313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275118928262211437891501 103169598098329289209313)
                ·
                  rfl

theorem cell19_339056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_339056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339056 prefixEnd_339056 := by exact prefixLift 339056
  have htrace : WordTrace (prefixWord ++ tailWord_339056) baseStart_339056 baseEnd_339056 := by
    simpa [prefixWord, tailWord_339056, baseEnd_339056] using wordTrace_append hprefix tailTrace_339056
  have hstable : (prefixWord ++ tailWord_339056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339056).length < 2 ^ (prefixWord ++ tailWord_339056).sum := by decide
  have hdescent : baseEnd_339056 < baseStart_339056 := by decide
  rcases family_descends (prefixWord ++ tailWord_339056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339111 : List Nat := [1, 1, 6, 2, 1, 1, 4, 3]
def baseStart_339111 : Nat := 118140960795 + 339111 * 2 ^ 59
def prefixEnd_339111 : Nat := 4983230072969 + 3 ^ 40 * 339111 * 2
def baseEnd_339111 : Nat := 103186333764105457986941

theorem tailTrace_339111 : CollatzResearch.WordTrace tailWord_339111 prefixEnd_339111 103186333764105457986941 := by
  unfold tailWord_339111
  simp only [CollatzResearch.WordTrace]
  refine ⟨12368394274466237393017187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8245596182977491595344791 12368394274466237393017187)
  ·
    refine ⟨18552591411699356089525781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12368394274466237393017187 18552591411699356089525781)
    ·
      refine ⟨869652722423407316696521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18552591411699356089525781 869652722423407316696521)
      ·
        refine ⟨652239541817555487522391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 869652722423407316696521 652239541817555487522391)
        ·
          refine ⟨978359312726333231283587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652239541817555487522391 978359312726333231283587)
          ·
            refine ⟨1467538969089499846925381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978359312726333231283587 1467538969089499846925381)
            ·
              refine ⟨275163556704281221298509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1467538969089499846925381 275163556704281221298509)
              ·
                refine ⟨103186333764105457986941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275163556704281221298509 103186333764105457986941)
                ·
                  rfl

theorem cell19_339111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_339111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339111 prefixEnd_339111 := by exact prefixLift 339111
  have htrace : WordTrace (prefixWord ++ tailWord_339111) baseStart_339111 baseEnd_339111 := by
    simpa [prefixWord, tailWord_339111, baseEnd_339111] using wordTrace_append hprefix tailTrace_339111
  have hstable : (prefixWord ++ tailWord_339111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339111).length < 2 ^ (prefixWord ++ tailWord_339111).sum := by decide
  have hdescent : baseEnd_339111 < baseStart_339111 := by decide
  rcases family_descends (prefixWord ++ tailWord_339111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339126 : List Nat := [5, 1, 3, 2, 2, 1, 5]
def baseStart_339126 : Nat := 118140960795 + 339126 * 2 ^ 59
def prefixEnd_339126 : Nat := 4983230072969 + 3 ^ 40 * 339126 * 2
def baseEnd_339126 : Nat := 34396966012196622551189

theorem tailTrace_339126 : CollatzResearch.WordTrace tailWord_339126 prefixEnd_339126 34396966012196622551189 := by
  unfold tailWord_339126
  simp only [CollatzResearch.WordTrace]
  refine ⟨773058835588243434675827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8245960912941263303208821 773058835588243434675827)
  ·
    refine ⟨1159588253382365152013741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 773058835588243434675827 1159588253382365152013741)
    ·
      refine ⟨434845595018386932005153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1159588253382365152013741 434845595018386932005153)
      ·
        refine ⟨326134196263790199003865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434845595018386932005153 326134196263790199003865)
        ·
          refine ⟨244600647197842649252899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326134196263790199003865 244600647197842649252899)
          ·
            refine ⟨366900970796763973879349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244600647197842649252899 366900970796763973879349)
            ·
              refine ⟨34396966012196622551189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 366900970796763973879349 34396966012196622551189)
              ·
                rfl

theorem cell19_339126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_339126 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339126 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339126 prefixEnd_339126 := by exact prefixLift 339126
  have htrace : WordTrace (prefixWord ++ tailWord_339126) baseStart_339126 baseEnd_339126 := by
    simpa [prefixWord, tailWord_339126, baseEnd_339126] using wordTrace_append hprefix tailTrace_339126
  have hstable : (prefixWord ++ tailWord_339126).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339126).length < 2 ^ (prefixWord ++ tailWord_339126).sum := by decide
  have hdescent : baseEnd_339126 < baseStart_339126 := by decide
  rcases family_descends (prefixWord ++ tailWord_339126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339132 : List Nat := [2, 2, 2, 3, 2, 3, 5]
def baseStart_339132 : Nat := 118140960795 + 339132 * 2 ^ 59
def prefixEnd_339132 : Nat := 4983230072969 + 3 ^ 40 * 339132 * 2
def baseEnd_339132 : Nat := 34397574581861210506739

theorem tailTrace_339132 : CollatzResearch.WordTrace tailWord_339132 prefixEnd_339132 34397574581861210506739 := by
  unfold tailWord_339132
  simp only [CollatzResearch.WordTrace]
  refine ⟨6184580103695078989765825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8246106804926771986354433 6184580103695078989765825)
  ·
    refine ⟨4638435077771309242324369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6184580103695078989765825 4638435077771309242324369)
    ·
      refine ⟨3478826308328481931743277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4638435077771309242324369 3478826308328481931743277)
      ·
        refine ⟨1304559865623180724403729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3478826308328481931743277 1304559865623180724403729)
        ·
          refine ⟨978419899217385543302797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1304559865623180724403729 978419899217385543302797)
          ·
            refine ⟨366907462206519578738549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 978419899217385543302797 366907462206519578738549)
            ·
              refine ⟨34397574581861210506739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 366907462206519578738549 34397574581861210506739)
              ·
                rfl

theorem cell19_339132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_339132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339132 prefixEnd_339132 := by exact prefixLift 339132
  have htrace : WordTrace (prefixWord ++ tailWord_339132) baseStart_339132 baseEnd_339132 := by
    simpa [prefixWord, tailWord_339132, baseEnd_339132] using wordTrace_append hprefix tailTrace_339132
  have hstable : (prefixWord ++ tailWord_339132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339132).length < 2 ^ (prefixWord ++ tailWord_339132).sum := by decide
  have hdescent : baseEnd_339132 < baseStart_339132 := by decide
  rcases family_descends (prefixWord ++ tailWord_339132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339172 : List Nat := [2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_339172 : Nat := 118140960795 + 339172 * 2 ^ 59
def prefixEnd_339172 : Nat := 4983230072969 + 3 ^ 40 * 339172 * 2
def baseEnd_339172 : Nat := 103204895138875390631219

theorem tailTrace_339172 : CollatzResearch.WordTrace tailWord_339172 prefixEnd_339172 103204895138875390631219 := by
  unfold tailWord_339172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6185309563622622405493885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8247079418163496540658513 6185309563622622405493885)
  ·
    refine ⟨2319491086358483402060207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6185309563622622405493885 2319491086358483402060207)
    ·
      refine ⟨3479236629537725103090311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319491086358483402060207 3479236629537725103090311)
      ·
        refine ⟨5218854944306587654635467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479236629537725103090311 5218854944306587654635467)
        ·
          refine ⟨7828282416459881481953201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218854944306587654635467 7828282416459881481953201)
          ·
            refine ⟨5871211812344911111464901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7828282416459881481953201 5871211812344911111464901)
            ·
              refine ⟨1100852214814670833399669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5871211812344911111464901 1100852214814670833399669)
              ·
                refine ⟨103204895138875390631219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1100852214814670833399669 103204895138875390631219)
                ·
                  rfl

theorem cell19_339172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_339172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339172 prefixEnd_339172 := by exact prefixLift 339172
  have htrace : WordTrace (prefixWord ++ tailWord_339172) baseStart_339172 baseEnd_339172 := by
    simpa [prefixWord, tailWord_339172, baseEnd_339172] using wordTrace_append hprefix tailTrace_339172
  have hstable : (prefixWord ++ tailWord_339172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339172).length < 2 ^ (prefixWord ++ tailWord_339172).sum := by decide
  have hdescent : baseEnd_339172 < baseStart_339172 := by decide
  rcases family_descends (prefixWord ++ tailWord_339172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339303 : List Nat := [1, 1, 5, 1, 4, 2, 5]
def baseStart_339303 : Nat := 118140960795 + 339303 * 2 ^ 59
def prefixEnd_339303 : Nat := 4983230072969 + 3 ^ 40 * 339303 * 2
def baseEnd_339303 : Nat := 34414918817301967239917

theorem tailTrace_339303 : CollatzResearch.WordTrace tailWord_339303 prefixEnd_339303 34414918817301967239917 := by
  unfold tailWord_339303
  simp only [CollatzResearch.WordTrace]
  refine ⟨12375397089770654184006563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8250264726513769456004375 12375397089770654184006563)
  ·
    refine ⟨18563095634655981276009845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12375397089770654184006563 18563095634655981276009845)
    ·
      refine ⟨1740290215748998244625923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18563095634655981276009845 1740290215748998244625923)
      ·
        refine ⟨2610435323623497366938885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1740290215748998244625923 2610435323623497366938885)
        ·
          refine ⟨489456623179405756301041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2610435323623497366938885 489456623179405756301041)
          ·
            refine ⟨367092467384554317225781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489456623179405756301041 367092467384554317225781)
            ·
              refine ⟨34414918817301967239917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 367092467384554317225781 34414918817301967239917)
              ·
                rfl

theorem cell19_339303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_339303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339303 prefixEnd_339303 := by exact prefixLift 339303
  have htrace : WordTrace (prefixWord ++ tailWord_339303) baseStart_339303 baseEnd_339303 := by
    simpa [prefixWord, tailWord_339303, baseEnd_339303] using wordTrace_append hprefix tailTrace_339303
  have hstable : (prefixWord ++ tailWord_339303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339303).length < 2 ^ (prefixWord ++ tailWord_339303).sum := by decide
  have hdescent : baseEnd_339303 < baseStart_339303 := by decide
  rcases family_descends (prefixWord ++ tailWord_339303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339324 : List Nat := [2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_339324 : Nat := 118140960795 + 339324 * 2 ^ 59
def prefixEnd_339324 : Nat := 4983230072969 + 3 ^ 40 * 339324 * 2
def baseEnd_339324 : Nat := 103251146433384075253027

theorem tailTrace_339324 : CollatzResearch.WordTrace tailWord_339324 prefixEnd_339324 103251146433384075253027 := by
  unfold tailWord_339324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188081511347287385260513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8250775348463049847014017 6188081511347287385260513)
  ·
    refine ⟨4641061133510465538945385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6188081511347287385260513 4641061133510465538945385)
    ·
      refine ⟨3480795850132849154209039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4641061133510465538945385 3480795850132849154209039)
      ·
        refine ⟨5221193775199273731313559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480795850132849154209039 5221193775199273731313559)
        ·
          refine ⟨7831790662798910596970339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221193775199273731313559 7831790662798910596970339)
          ·
            refine ⟨11747685994198365895455509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7831790662798910596970339 11747685994198365895455509)
            ·
              refine ⟨550672780978048401349477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11747685994198365895455509 550672780978048401349477)
              ·
                refine ⟨103251146433384075253027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 550672780978048401349477 103251146433384075253027)
                ·
                  rfl

theorem cell19_339324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_339324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339324 prefixEnd_339324 := by exact prefixLift 339324
  have htrace : WordTrace (prefixWord ++ tailWord_339324) baseStart_339324 baseEnd_339324 := by
    simpa [prefixWord, tailWord_339324, baseEnd_339324] using wordTrace_append hprefix tailTrace_339324
  have hstable : (prefixWord ++ tailWord_339324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339324).length < 2 ^ (prefixWord ++ tailWord_339324).sum := by decide
  have hdescent : baseEnd_339324 < baseStart_339324 := by decide
  rcases family_descends (prefixWord ++ tailWord_339324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339358 : List Nat := [4, 3, 1, 2, 3, 6]
def baseStart_339358 : Nat := 118140960795 + 339358 * 2 ^ 59
def prefixEnd_339358 : Nat := 4983230072969 + 3 ^ 40 * 339358 * 2
def baseEnd_339358 : Nat := 11473499124186896721931

theorem tailTrace_339358 : CollatzResearch.WordTrace tailWord_339358 prefixEnd_339358 11473499124186896721931 := by
  unfold tailWord_339358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547175388071424822157341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8251602069714265718172485 1547175388071424822157341)
  ·
    refine ⟨580190770526784308309003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1547175388071424822157341 580190770526784308309003)
    ·
      refine ⟨870286155790176462463505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580190770526784308309003 870286155790176462463505)
      ·
        refine ⟨652714616842632346847629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 870286155790176462463505 652714616842632346847629)
        ·
          refine ⟨244767981315987130067861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 652714616842632346847629 244767981315987130067861)
          ·
            refine ⟨11473499124186896721931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 244767981315987130067861 11473499124186896721931)
            ·
              rfl

theorem cell19_339358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 6].length) (baseStart_339358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339358 prefixEnd_339358 := by exact prefixLift 339358
  have htrace : WordTrace (prefixWord ++ tailWord_339358) baseStart_339358 baseEnd_339358 := by
    simpa [prefixWord, tailWord_339358, baseEnd_339358] using wordTrace_append hprefix tailTrace_339358
  have hstable : (prefixWord ++ tailWord_339358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339358).length < 2 ^ (prefixWord ++ tailWord_339358).sum := by decide
  have hdescent : baseEnd_339358 < baseStart_339358 := by decide
  rcases family_descends (prefixWord ++ tailWord_339358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339362 : List Nat := [3, 3, 1, 2, 1, 9]
def baseStart_339362 : Nat := 118140960795 + 339362 * 2 ^ 59
def prefixEnd_339362 : Nat := 4983230072969 + 3 ^ 40 * 339362 * 2
def baseEnd_339362 : Nat := 11473634361890138489831

theorem tailTrace_339362 : CollatzResearch.WordTrace tailWord_339362 prefixEnd_339362 11473634361890138489831 := by
  unfold tailWord_339362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094387249139226815101085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8251699331037938173602893 3094387249139226815101085)
  ·
    refine ⟨1160395218427210055662907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3094387249139226815101085 1160395218427210055662907)
    ·
      refine ⟨1740592827640815083494361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1160395218427210055662907 1740592827640815083494361)
      ·
        refine ⟨1305444620730611312620771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1740592827640815083494361 1305444620730611312620771)
        ·
          refine ⟨1958166931095916968931157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305444620730611312620771 1958166931095916968931157)
          ·
            refine ⟨11473634361890138489831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1958166931095916968931157 11473634361890138489831)
            ·
              rfl

theorem cell19_339362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 9].length) (baseStart_339362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339362 prefixEnd_339362 := by exact prefixLift 339362
  have htrace : WordTrace (prefixWord ++ tailWord_339362) baseStart_339362 baseEnd_339362 := by
    simpa [prefixWord, tailWord_339362, baseEnd_339362] using wordTrace_append hprefix tailTrace_339362
  have hstable : (prefixWord ++ tailWord_339362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339362).length < 2 ^ (prefixWord ++ tailWord_339362).sum := by decide
  have hdescent : baseEnd_339362 < baseStart_339362 := by decide
  rcases family_descends (prefixWord ++ tailWord_339362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339396 : List Nat := [2, 3, 3, 2, 1, 2, 3, 3]
def baseStart_339396 : Nat := 118140960795 + 339396 * 2 ^ 59
def prefixEnd_339396 : Nat := 4983230072969 + 3 ^ 40 * 339396 * 2
def baseEnd_339396 : Nat := 103273054941309241652831

theorem tailTrace_339396 : CollatzResearch.WordTrace tailWord_339396 prefixEnd_339396 103273054941309241652831 := by
  unfold tailWord_339396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189394539216865533571021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8252526052289154044761361 6189394539216865533571021)
  ·
    refine ⟨2321022952206324575089133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6189394539216865533571021 2321022952206324575089133)
    ·
      refine ⟨870383607077371715658425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2321022952206324575089133 870383607077371715658425)
      ·
        refine ⟨652787705308028786743819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 870383607077371715658425 652787705308028786743819)
        ·
          refine ⟨979181557962043180115729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652787705308028786743819 979181557962043180115729)
          ·
            refine ⟨734386168471532385086797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979181557962043180115729 734386168471532385086797)
            ·
              refine ⟨275394813176824644407549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 734386168471532385086797 275394813176824644407549)
              ·
                refine ⟨103273054941309241652831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275394813176824644407549 103273054941309241652831)
                ·
                  rfl

theorem cell19_339396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_339396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339396 prefixEnd_339396 := by exact prefixLift 339396
  have htrace : WordTrace (prefixWord ++ tailWord_339396) baseStart_339396 baseEnd_339396 := by
    simpa [prefixWord, tailWord_339396, baseEnd_339396] using wordTrace_append hprefix tailTrace_339396
  have hstable : (prefixWord ++ tailWord_339396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339396).length < 2 ^ (prefixWord ++ tailWord_339396).sum := by decide
  have hdescent : baseEnd_339396 < baseStart_339396 := by decide
  rcases family_descends (prefixWord ++ tailWord_339396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339438 : List Nat := [4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_339438 : Nat := 118140960795 + 339438 * 2 ^ 59
def prefixEnd_339438 : Nat := 4983230072969 + 3 ^ 40 * 339438 * 2
def baseEnd_339438 : Nat := 103285834904265588719383

theorem tailTrace_339438 : CollatzResearch.WordTrace tailWord_339438 prefixEnd_339438 103285834904265588719383 := by
  unfold tailWord_339438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547540118035196530021371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8253547296187714826780645 1547540118035196530021371)
  ·
    refine ⟨2321310177052794795032057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1547540118035196530021371 2321310177052794795032057)
    ·
      refine ⟨1740982632789596096274043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2321310177052794795032057 1740982632789596096274043)
      ·
        refine ⟨2611473949184394144411065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1740982632789596096274043 2611473949184394144411065)
        ·
          refine ⟨1958605461888295608308299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2611473949184394144411065 1958605461888295608308299)
          ·
            refine ⟨2937908192832443412462449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958605461888295608308299 2937908192832443412462449)
            ·
              refine ⟨2203431144624332559346837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2937908192832443412462449 2203431144624332559346837)
              ·
                refine ⟨103285834904265588719383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2203431144624332559346837 103285834904265588719383)
                ·
                  rfl

theorem cell19_339438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_339438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339438 prefixEnd_339438 := by exact prefixLift 339438
  have htrace : WordTrace (prefixWord ++ tailWord_339438) baseStart_339438 baseEnd_339438 := by
    simpa [prefixWord, tailWord_339438, baseEnd_339438] using wordTrace_append hprefix tailTrace_339438
  have hstable : (prefixWord ++ tailWord_339438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339438).length < 2 ^ (prefixWord ++ tailWord_339438).sum := by decide
  have hdescent : baseEnd_339438 < baseStart_339438 := by decide
  rcases family_descends (prefixWord ++ tailWord_339438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339533 : List Nat := [1, 6, 1, 1, 10]
def baseStart_339533 : Nat := 118140960795 + 339533 * 2 ^ 59
def prefixEnd_339533 : Nat := 4983230072969 + 3 ^ 40 * 339533 * 2
def baseEnd_339533 : Nat := 3826471924567908022519

theorem tailTrace_339533 : CollatzResearch.WordTrace tailWord_339533 prefixEnd_339533 3826471924567908022519 := by
  unfold tailWord_339533
  simp only [CollatzResearch.WordTrace]
  refine ⟨12383785878937403464879253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8255857252624935643252835 12383785878937403464879253)
  ·
    refine ⟨580489963075190787416215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12383785878937403464879253 580489963075190787416215)
    ·
      refine ⟨870734944612786181124323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580489963075190787416215 870734944612786181124323)
      ·
        refine ⟨1306102416919179271686485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870734944612786181124323 1306102416919179271686485)
        ·
          refine ⟨3826471924567908022519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1306102416919179271686485 3826471924567908022519)
          ·
            rfl

theorem cell19_339533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 10].length) (baseStart_339533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339533 prefixEnd_339533 := by exact prefixLift 339533
  have htrace : WordTrace (prefixWord ++ tailWord_339533) baseStart_339533 baseEnd_339533 := by
    simpa [prefixWord, tailWord_339533, baseEnd_339533] using wordTrace_append hprefix tailTrace_339533
  have hstable : (prefixWord ++ tailWord_339533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339533).length < 2 ^ (prefixWord ++ tailWord_339533).sum := by decide
  have hdescent : baseEnd_339533 < baseStart_339533 := by decide
  rcases family_descends (prefixWord ++ tailWord_339533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339666 : List Nat := [3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_339666 : Nat := 118140960795 + 339666 * 2 ^ 59
def prefixEnd_339666 : Nat := 4983230072969 + 3 ^ 40 * 339666 * 2
def baseEnd_339666 : Nat := 103355211846028615652095

theorem tailTrace_339666 : CollatzResearch.WordTrace tailWord_339666 prefixEnd_339666 103355211846028615652095 := by
  unfold tailWord_339666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3097159196863891794867713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8259091191637044786313901 3097159196863891794867713)
  ·
    refine ⟨2322869397647918846150785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3097159196863891794867713 2322869397647918846150785)
    ·
      refine ⟨1742152048235939134613089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2322869397647918846150785 1742152048235939134613089)
      ·
        refine ⟨1306614036176954350959817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1742152048235939134613089 1306614036176954350959817)
        ·
          refine ⟨979960527132715763219863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1306614036176954350959817 979960527132715763219863)
          ·
            refine ⟨1469940790699073644829795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979960527132715763219863 1469940790699073644829795)
            ·
              refine ⟨2204911186048610467244693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469940790699073644829795 2204911186048610467244693)
              ·
                refine ⟨103355211846028615652095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2204911186048610467244693 103355211846028615652095)
                ·
                  rfl

theorem cell19_339666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_339666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339666 prefixEnd_339666 := by exact prefixLift 339666
  have htrace : WordTrace (prefixWord ++ tailWord_339666) baseStart_339666 baseEnd_339666 := by
    simpa [prefixWord, tailWord_339666, baseEnd_339666] using wordTrace_append hprefix tailTrace_339666
  have hstable : (prefixWord ++ tailWord_339666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339666).length < 2 ^ (prefixWord ++ tailWord_339666).sum := by decide
  have hdescent : baseEnd_339666 < baseStart_339666 := by decide
  rcases family_descends (prefixWord ++ tailWord_339666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339719 : List Nat := [1, 1, 4, 4, 3, 1, 1, 4]
def baseStart_339719 : Nat := 118140960795 + 339719 * 2 ^ 59
def prefixEnd_339719 : Nat := 4983230072969 + 3 ^ 40 * 339719 * 2
def baseEnd_339719 : Nat := 103371338942140196474173

theorem tailTrace_339719 : CollatzResearch.WordTrace tailWord_339719 prefixEnd_339719 103371338942140196474173 := by
  unfold tailWord_339719
  simp only [CollatzResearch.WordTrace]
  refine ⟨12390569856263557231150211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8260379904175704820766807 12390569856263557231150211)
  ·
    refine ⟨18585854784395335846725317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12390569856263557231150211 18585854784395335846725317)
    ·
      refine ⟨3484847772074125471260997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18585854784395335846725317 3484847772074125471260997)
      ·
        refine ⟨653408957263898525861437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3484847772074125471260997 653408957263898525861437)
        ·
          refine ⟨245028358973961947198039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 653408957263898525861437 245028358973961947198039)
          ·
            refine ⟨367542538460942920797059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245028358973961947198039 367542538460942920797059)
            ·
              refine ⟨551313807691414381195589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367542538460942920797059 551313807691414381195589)
              ·
                refine ⟨103371338942140196474173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551313807691414381195589 103371338942140196474173)
                ·
                  rfl

theorem cell19_339719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4].length) (baseStart_339719 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339719 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339719 prefixEnd_339719 := by exact prefixLift 339719
  have htrace : WordTrace (prefixWord ++ tailWord_339719) baseStart_339719 baseEnd_339719 := by
    simpa [prefixWord, tailWord_339719, baseEnd_339719] using wordTrace_append hprefix tailTrace_339719
  have hstable : (prefixWord ++ tailWord_339719).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339719).length < 2 ^ (prefixWord ++ tailWord_339719).sum := by decide
  have hdescent : baseEnd_339719 < baseStart_339719 := by decide
  rcases family_descends (prefixWord ++ tailWord_339719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339797 : List Nat := [1, 3, 2, 2, 2, 4, 2, 3]
def baseStart_339797 : Nat := 118140960795 + 339797 * 2 ^ 59
def prefixEnd_339797 : Nat := 4983230072969 + 3 ^ 40 * 339797 * 2
def baseEnd_339797 : Nat := 103395073159059126740627

theorem tailTrace_339797 : CollatzResearch.WordTrace tailWord_339797 prefixEnd_339797 103395073159059126740627 := by
  unfold tailWord_339797
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393414749980976552489645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8262276499987317701659763 12393414749980976552489645)
  ·
    refine ⟨4647530531242866207183617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12393414749980976552489645 4647530531242866207183617)
    ·
      refine ⟨3485647898432149655387713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4647530531242866207183617 3485647898432149655387713)
      ·
        refine ⟨2614235923824112241540785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3485647898432149655387713 2614235923824112241540785)
        ·
          refine ⟨1960676942868084181155589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2614235923824112241540785 1960676942868084181155589)
          ·
            refine ⟨367626926787765783966673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1960676942868084181155589 367626926787765783966673)
            ·
              refine ⟨275720195090824337975005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367626926787765783966673 275720195090824337975005)
              ·
                refine ⟨103395073159059126740627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275720195090824337975005 103395073159059126740627)
                ·
                  rfl

theorem cell19_339797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_339797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339797 prefixEnd_339797 := by exact prefixLift 339797
  have htrace : WordTrace (prefixWord ++ tailWord_339797) baseStart_339797 baseEnd_339797 := by
    simpa [prefixWord, tailWord_339797, baseEnd_339797] using wordTrace_append hprefix tailTrace_339797
  have hstable : (prefixWord ++ tailWord_339797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339797).length < 2 ^ (prefixWord ++ tailWord_339797).sum := by decide
  have hdescent : baseEnd_339797 < baseStart_339797 := by decide
  rcases family_descends (prefixWord ++ tailWord_339797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339799 : List Nat := [1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_339799 : Nat := 118140960795 + 339799 * 2 ^ 59
def prefixEnd_339799 : Nat := 4983230072969 + 3 ^ 40 * 339799 * 2
def baseEnd_339799 : Nat := 103395681728723714696177

theorem tailTrace_339799 : CollatzResearch.WordTrace tailWord_339799 prefixEnd_339799 103395681728723714696177 := by
  unfold tailWord_339799
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393487695973730894062451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8262325130649153929374967 12393487695973730894062451)
  ·
    refine ⟨18590231543960596341093677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12393487695973730894062451 18590231543960596341093677)
    ·
      refine ⟨6971336828985223627910129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18590231543960596341093677 6971336828985223627910129)
      ·
        refine ⟨5228502621738917720932597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6971336828985223627910129 5228502621738917720932597)
        ·
          refine ⟨490172120788023536337431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5228502621738917720932597 490172120788023536337431)
          ·
            refine ⟨735258181182035304506147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490172120788023536337431 735258181182035304506147)
            ·
              refine ⟨1102887271773052956759221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735258181182035304506147 1102887271773052956759221)
              ·
                refine ⟨103395681728723714696177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1102887271773052956759221 103395681728723714696177)
                ·
                  rfl

theorem cell19_339799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_339799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339799 prefixEnd_339799 := by exact prefixLift 339799
  have htrace : WordTrace (prefixWord ++ tailWord_339799) baseStart_339799 baseEnd_339799 := by
    simpa [prefixWord, tailWord_339799, baseEnd_339799] using wordTrace_append hprefix tailTrace_339799
  have hstable : (prefixWord ++ tailWord_339799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339799).length < 2 ^ (prefixWord ++ tailWord_339799).sum := by decide
  have hdescent : baseEnd_339799 < baseStart_339799 := by decide
  rcases family_descends (prefixWord ++ tailWord_339799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339801 : List Nat := [1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_339801 : Nat := 118140960795 + 339801 * 2 ^ 59
def prefixEnd_339801 : Nat := 4983230072969 + 3 ^ 40 * 339801 * 2
def baseEnd_339801 : Nat := 103396290298388302651727

theorem tailTrace_339801 : CollatzResearch.WordTrace tailWord_339801 prefixEnd_339801 103396290298388302651727 := by
  unfold tailWord_339801
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393560641966485235635257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8262373761310990157090171 12393560641966485235635257)
  ·
    refine ⟨9295170481474863926726443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12393560641966485235635257 9295170481474863926726443)
    ·
      refine ⟨13942755722212295890089665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9295170481474863926726443 13942755722212295890089665)
      ·
        refine ⟨10457066791659221917567249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13942755722212295890089665 10457066791659221917567249)
        ·
          refine ⟨7842800093744416438175437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10457066791659221917567249 7842800093744416438175437)
          ·
            refine ⟨2941050035154156164315789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7842800093744416438175437 2941050035154156164315789)
            ·
              refine ⟨1102893763182808561618421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2941050035154156164315789 1102893763182808561618421)
              ·
                refine ⟨103396290298388302651727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1102893763182808561618421 103396290298388302651727)
                ·
                  rfl

theorem cell19_339801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_339801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339801 prefixEnd_339801 := by exact prefixLift 339801
  have htrace : WordTrace (prefixWord ++ tailWord_339801) baseStart_339801 baseEnd_339801 := by
    simpa [prefixWord, tailWord_339801, baseEnd_339801] using wordTrace_append hprefix tailTrace_339801
  have hstable : (prefixWord ++ tailWord_339801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339801).length < 2 ^ (prefixWord ++ tailWord_339801).sum := by decide
  have hdescent : baseEnd_339801 < baseStart_339801 := by decide
  rcases family_descends (prefixWord ++ tailWord_339801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339820 : List Nat := [2, 2, 1, 1, 4, 2, 7]
def baseStart_339820 : Nat := 118140960795 + 339820 * 2 ^ 59
def prefixEnd_339820 : Nat := 4983230072969 + 3 ^ 40 * 339820 * 2
def baseEnd_339820 : Nat := 34467357236733962743151

theorem tailTrace_339820 : CollatzResearch.WordTrace tailWord_339820 prefixEnd_339820 34467357236733962743151 := by
  unfold tailWord_339820
  simp only [CollatzResearch.WordTrace]
  refine ⟨6197126814448825740288457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8262835752598434320384609 6197126814448825740288457)
  ·
    refine ⟨4647845110836619305216343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6197126814448825740288457 4647845110836619305216343)
    ·
      refine ⟨6971767666254928957824515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4647845110836619305216343 6971767666254928957824515)
      ·
        refine ⟨10457651499382393436736773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971767666254928957824515 10457651499382393436736773)
        ·
          refine ⟨1960809656134198769388145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10457651499382393436736773 1960809656134198769388145)
          ·
            refine ⟨1470607242100649077041109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1960809656134198769388145 1470607242100649077041109)
            ·
              refine ⟨34467357236733962743151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1470607242100649077041109 34467357236733962743151)
              ·
                rfl

theorem cell19_339820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_339820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339820 prefixEnd_339820 := by exact prefixLift 339820
  have htrace : WordTrace (prefixWord ++ tailWord_339820) baseStart_339820 baseEnd_339820 := by
    simpa [prefixWord, tailWord_339820, baseEnd_339820] using wordTrace_append hprefix tailTrace_339820
  have hstable : (prefixWord ++ tailWord_339820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339820).length < 2 ^ (prefixWord ++ tailWord_339820).sum := by decide
  have hdescent : baseEnd_339820 < baseStart_339820 := by decide
  rcases family_descends (prefixWord ++ tailWord_339820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339886 : List Nat := [4, 1, 5, 1, 2, 1, 1, 4]
def baseStart_339886 : Nat := 118140960795 + 339886 * 2 ^ 59
def prefixEnd_339886 : Nat := 4983230072969 + 3 ^ 40 * 339886 * 2
def baseEnd_339886 : Nat := 103422154509133290762607

theorem tailTrace_339886 : CollatzResearch.WordTrace tailWord_339886 prefixEnd_339886 103422154509133290762607 := by
  unfold tailWord_339886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549582605832318094059939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8264440564439029834986341 1549582605832318094059939)
  ·
    refine ⟨2324373908748477141089909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1549582605832318094059939 2324373908748477141089909)
    ·
      refine ⟨217910053945169731977179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2324373908748477141089909 217910053945169731977179)
      ·
        refine ⟨326865080917754597965769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217910053945169731977179 326865080917754597965769)
        ·
          refine ⟨245148810688315948474327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326865080917754597965769 245148810688315948474327)
          ·
            refine ⟨367723216032473922711491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245148810688315948474327 367723216032473922711491)
            ·
              refine ⟨551584824048710884067237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367723216032473922711491 551584824048710884067237)
              ·
                refine ⟨103422154509133290762607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551584824048710884067237 103422154509133290762607)
                ·
                  rfl

theorem cell19_339886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_339886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339886 prefixEnd_339886 := by exact prefixLift 339886
  have htrace : WordTrace (prefixWord ++ tailWord_339886) baseStart_339886 baseEnd_339886 := by
    simpa [prefixWord, tailWord_339886, baseEnd_339886] using wordTrace_append hprefix tailTrace_339886
  have hstable : (prefixWord ++ tailWord_339886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339886).length < 2 ^ (prefixWord ++ tailWord_339886).sum := by decide
  have hdescent : baseEnd_339886 < baseStart_339886 := by decide
  rcases family_descends (prefixWord ++ tailWord_339886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339966 : List Nat := [4, 2, 2, 2, 1, 3, 2, 3]
def baseStart_339966 : Nat := 118140960795 + 339966 * 2 ^ 59
def prefixEnd_339966 : Nat := 4983230072969 + 3 ^ 40 * 339966 * 2
def baseEnd_339966 : Nat := 103446497295716808984611

theorem tailTrace_339966 : CollatzResearch.WordTrace tailWord_339966 prefixEnd_339966 103446497295716808984611 := by
  unfold tailWord_339966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549947335796089801923969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8266385790912478943594501 1549947335796089801923969)
  ·
    refine ⟨1162460501847067351442977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1549947335796089801923969 1162460501847067351442977)
    ·
      refine ⟨871845376385300513582233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1162460501847067351442977 871845376385300513582233)
      ·
        refine ⟨653884032288975385186675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871845376385300513582233 653884032288975385186675)
        ·
          refine ⟨980826048433463077780013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653884032288975385186675 980826048433463077780013)
          ·
            refine ⟨367809768162548654167505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980826048433463077780013 367809768162548654167505)
            ·
              refine ⟨275857326121911490625629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367809768162548654167505 275857326121911490625629)
              ·
                refine ⟨103446497295716808984611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275857326121911490625629 103446497295716808984611)
                ·
                  rfl

theorem cell19_339966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_339966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339966 prefixEnd_339966 := by exact prefixLift 339966
  have htrace : WordTrace (prefixWord ++ tailWord_339966) baseStart_339966 baseEnd_339966 := by
    simpa [prefixWord, tailWord_339966, baseEnd_339966] using wordTrace_append hprefix tailTrace_339966
  have hstable : (prefixWord ++ tailWord_339966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339966).length < 2 ^ (prefixWord ++ tailWord_339966).sum := by decide
  have hdescent : baseEnd_339966 < baseStart_339966 := by decide
  rcases family_descends (prefixWord ++ tailWord_339966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339989 : List Nat := [1, 3, 2, 1, 5, 2, 5]
def baseStart_339989 : Nat := 118140960795 + 339989 * 2 ^ 59
def prefixEnd_339989 : Nat := 4983230072969 + 3 ^ 40 * 339989 * 2
def baseEnd_339989 : Nat := 34484498615619856824479

theorem tailTrace_339989 : CollatzResearch.WordTrace tailWord_339989 prefixEnd_339989 34484498615619856824479 := by
  unfold tailWord_339989
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400417565285393343479021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8266945043523595562319347 12400417565285393343479021)
  ·
    refine ⟨4650156586982022503804633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12400417565285393343479021 4650156586982022503804633)
    ·
      refine ⟨3487617440236516877853475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4650156586982022503804633 3487617440236516877853475)
      ·
        refine ⟨5231426160354775316780213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3487617440236516877853475 5231426160354775316780213)
        ·
          refine ⟨490446202533260185948145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5231426160354775316780213 490446202533260185948145)
          ·
            refine ⟨367834651899945139461109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490446202533260185948145 367834651899945139461109)
            ·
              refine ⟨34484498615619856824479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 367834651899945139461109 34484498615619856824479)
              ·
                rfl

theorem cell19_339989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_339989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_339989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_339989 prefixEnd_339989 := by exact prefixLift 339989
  have htrace : WordTrace (prefixWord ++ tailWord_339989) baseStart_339989 baseEnd_339989 := by
    simpa [prefixWord, tailWord_339989, baseEnd_339989] using wordTrace_append hprefix tailTrace_339989
  have hstable : (prefixWord ++ tailWord_339989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339989).length < 2 ^ (prefixWord ++ tailWord_339989).sum := by decide
  have hdescent : baseEnd_339989 < baseStart_339989 := by decide
  rcases family_descends (prefixWord ++ tailWord_339989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340029 : List Nat := [1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_340029 : Nat := 118140960795 + 340029 * 2 ^ 59
def prefixEnd_340029 : Nat := 4983230072969 + 3 ^ 40 * 340029 * 2
def baseEnd_340029 : Nat := 103465667240151329584439

theorem tailTrace_340029 : CollatzResearch.WordTrace tailWord_340029 prefixEnd_340029 103465667240151329584439 := by
  unfold tailWord_340029
  simp only [CollatzResearch.WordTrace]
  refine ⟨12401876485140480174935141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8267917656760320116623427 12401876485140480174935141)
  ·
    refine ⟨2325351840963840032800339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12401876485140480174935141 2325351840963840032800339)
    ·
      refine ⟨3488027761445760049200509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2325351840963840032800339 3488027761445760049200509)
      ·
        refine ⟨1308010410542160018450191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3488027761445760049200509 1308010410542160018450191)
        ·
          refine ⟨1962015615813240027675287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308010410542160018450191 1962015615813240027675287)
          ·
            refine ⟨2943023423719860041512931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962015615813240027675287 2943023423719860041512931)
            ·
              refine ⟨4414535135579790062269397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943023423719860041512931 4414535135579790062269397)
              ·
                refine ⟨103465667240151329584439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4414535135579790062269397 103465667240151329584439)
                ·
                  rfl

theorem cell19_340029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_340029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340029 prefixEnd_340029 := by exact prefixLift 340029
  have htrace : WordTrace (prefixWord ++ tailWord_340029) baseStart_340029 baseEnd_340029 := by
    simpa [prefixWord, tailWord_340029, baseEnd_340029] using wordTrace_append hprefix tailTrace_340029
  have hstable : (prefixWord ++ tailWord_340029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340029).length < 2 ^ (prefixWord ++ tailWord_340029).sum := by decide
  have hdescent : baseEnd_340029 < baseStart_340029 := by decide
  rcases family_descends (prefixWord ++ tailWord_340029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340067 : List Nat := [1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_340067 : Nat := 118140960795 + 340067 * 2 ^ 59
def prefixEnd_340067 : Nat := 4983230072969 + 3 ^ 40 * 340067 * 2
def baseEnd_340067 : Nat := 103477230063778500739891

theorem tailTrace_340067 : CollatzResearch.WordTrace tailWord_340067 prefixEnd_340067 103477230063778500739891 := by
  unfold tailWord_340067
  simp only [CollatzResearch.WordTrace]
  refine ⟨12403262459002812664818455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8268841639335208443212303 12403262459002812664818455)
  ·
    refine ⟨18604893688504218997227683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12403262459002812664818455 18604893688504218997227683)
    ·
      refine ⟨27907340532756328495841525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18604893688504218997227683 27907340532756328495841525)
      ·
        refine ⟨2616313174945905796485143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27907340532756328495841525 2616313174945905796485143)
        ·
          refine ⟨3924469762418858694727715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616313174945905796485143 3924469762418858694727715)
          ·
            refine ⟨5886704643628288042091573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924469762418858694727715 5886704643628288042091573)
            ·
              refine ⟨551878560340152003946085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5886704643628288042091573 551878560340152003946085)
              ·
                refine ⟨103477230063778500739891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551878560340152003946085 103477230063778500739891)
                ·
                  rfl

theorem cell19_340067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_340067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340067 prefixEnd_340067 := by exact prefixLift 340067
  have htrace : WordTrace (prefixWord ++ tailWord_340067) baseStart_340067 baseEnd_340067 := by
    simpa [prefixWord, tailWord_340067, baseEnd_340067] using wordTrace_append hprefix tailTrace_340067
  have hstable : (prefixWord ++ tailWord_340067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340067).length < 2 ^ (prefixWord ++ tailWord_340067).sum := by decide
  have hdescent : baseEnd_340067 < baseStart_340067 := by decide
  rcases family_descends (prefixWord ++ tailWord_340067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340124 : List Nat := [2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_340124 : Nat := 118140960795 + 340124 * 2 ^ 59
def prefixEnd_340124 : Nat := 4983230072969 + 3 ^ 40 * 340124 * 2
def baseEnd_340124 : Nat := 103494574299219257473069

theorem tailTrace_340124 : CollatzResearch.WordTrace tailWord_340124 prefixEnd_340124 103494574299219257473069 := by
  unfold tailWord_340124
  simp only [CollatzResearch.WordTrace]
  refine ⟨6202670709898155699821713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8270227613197540933095617 6202670709898155699821713)
  ·
    refine ⟨4652003032423616774866285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6202670709898155699821713 4652003032423616774866285)
    ·
      refine ⟨1744501137158856290574857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4652003032423616774866285 1744501137158856290574857)
      ·
        refine ⟨1308375852869142217931143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1744501137158856290574857 1308375852869142217931143)
        ·
          refine ⟨1962563779303713326896715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308375852869142217931143 1962563779303713326896715)
          ·
            refine ⟨2943845668955569990345073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962563779303713326896715 2943845668955569990345073)
            ·
              refine ⟨2207884251716677492758805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2943845668955569990345073 2207884251716677492758805)
              ·
                refine ⟨103494574299219257473069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2207884251716677492758805 103494574299219257473069)
                ·
                  rfl

theorem cell19_340124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_340124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340124 prefixEnd_340124 := by exact prefixLift 340124
  have htrace : WordTrace (prefixWord ++ tailWord_340124) baseStart_340124 baseEnd_340124 := by
    simpa [prefixWord, tailWord_340124, baseEnd_340124] using wordTrace_append hprefix tailTrace_340124
  have hstable : (prefixWord ++ tailWord_340124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340124).length < 2 ^ (prefixWord ++ tailWord_340124).sum := by decide
  have hdescent : baseEnd_340124 < baseStart_340124 := by decide
  rcases family_descends (prefixWord ++ tailWord_340124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340141 : List Nat := [1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_340141 : Nat := 118140960795 + 340141 * 2 ^ 59
def prefixEnd_340141 : Nat := 4983230072969 + 3 ^ 40 * 340141 * 2
def baseEnd_340141 : Nat := 103499747141368255095245

theorem tailTrace_340141 : CollatzResearch.WordTrace tailWord_340141 prefixEnd_340141 103499747141368255095245 := by
  unfold tailWord_340141
  simp only [CollatzResearch.WordTrace]
  refine ⟨12405961460734723303012277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8270640973823148868674851 12405961460734723303012277)
  ·
    refine ⟨1163058886943880309657401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12405961460734723303012277 1163058886943880309657401)
    ·
      refine ⟨872294165207910232243051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1163058886943880309657401 872294165207910232243051)
      ·
        refine ⟨1308441247811865348364577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872294165207910232243051 1308441247811865348364577)
        ·
          refine ⟨981330935858899011273433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308441247811865348364577 981330935858899011273433)
          ·
            refine ⟨735998201894174258455075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981330935858899011273433 735998201894174258455075)
            ·
              refine ⟨1103997302841261387682613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735998201894174258455075 1103997302841261387682613)
              ·
                refine ⟨103499747141368255095245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1103997302841261387682613 103499747141368255095245)
                ·
                  rfl

theorem cell19_340141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_340141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340141 prefixEnd_340141 := by exact prefixLift 340141
  have htrace : WordTrace (prefixWord ++ tailWord_340141) baseStart_340141 baseEnd_340141 := by
    simpa [prefixWord, tailWord_340141, baseEnd_340141] using wordTrace_append hprefix tailTrace_340141
  have hstable : (prefixWord ++ tailWord_340141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340141).length < 2 ^ (prefixWord ++ tailWord_340141).sum := by decide
  have hdescent : baseEnd_340141 < baseStart_340141 := by decide
  rcases family_descends (prefixWord ++ tailWord_340141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340158 : List Nat := [4, 2, 1, 1, 5, 1, 5]
def baseStart_340158 : Nat := 118140960795 + 340158 * 2 ^ 59
def prefixEnd_340158 : Nat := 4983230072969 + 3 ^ 40 * 340158 * 2
def baseEnd_340158 : Nat := 34501639994505750905807

theorem tailTrace_340158 : CollatzResearch.WordTrace tailWord_340158 prefixEnd_340158 34501639994505750905807 := by
  unfold tailWord_340158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1550822687709141900797641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8271054334448756804254085 1550822687709141900797641)
  ·
    refine ⟨1163117015781856425598231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1550822687709141900797641 1163117015781856425598231)
    ·
      refine ⟨1744675523672784638397347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1163117015781856425598231 1744675523672784638397347)
      ·
        refine ⟨2617013285509176957596021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744675523672784638397347 2617013285509176957596021)
        ·
          refine ⟨245344995516485339774627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2617013285509176957596021 245344995516485339774627)
          ·
            refine ⟨368017493274728009661941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245344995516485339774627 368017493274728009661941)
            ·
              refine ⟨34501639994505750905807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 368017493274728009661941 34501639994505750905807)
              ·
                rfl

theorem cell19_340158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_340158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340158 prefixEnd_340158 := by exact prefixLift 340158
  have htrace : WordTrace (prefixWord ++ tailWord_340158) baseStart_340158 baseEnd_340158 := by
    simpa [prefixWord, tailWord_340158, baseEnd_340158] using wordTrace_append hprefix tailTrace_340158
  have hstable : (prefixWord ++ tailWord_340158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340158).length < 2 ^ (prefixWord ++ tailWord_340158).sum := by decide
  have hdescent : baseEnd_340158 < baseStart_340158 := by decide
  rcases family_descends (prefixWord ++ tailWord_340158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340200 : List Nat := [2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_340200 : Nat := 118140960795 + 340200 * 2 ^ 59
def prefixEnd_340200 : Nat := 4983230072969 + 3 ^ 40 * 340200 * 2
def baseEnd_340200 : Nat := 103517699946473599783973

theorem tailTrace_340200 : CollatzResearch.WordTrace tailWord_340200 prefixEnd_340200 103517699946473599783973 := by
  unfold tailWord_340200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204056683760488189705027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8272075578347317586273369 6204056683760488189705027)
  ·
    refine ⟨9306085025640732284557541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6204056683760488189705027 9306085025640732284557541)
    ·
      refine ⟨1744890942307637303354539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9306085025640732284557541 1744890942307637303354539)
      ·
        refine ⟨2617336413461455955031809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744890942307637303354539 2617336413461455955031809)
        ·
          refine ⟨1963002310096091966273857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2617336413461455955031809 1963002310096091966273857)
          ·
            refine ⟨1472251732572068974705393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1963002310096091966273857 1472251732572068974705393)
            ·
              refine ⟨1104188799429051731029045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472251732572068974705393 1104188799429051731029045)
              ·
                refine ⟨103517699946473599783973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1104188799429051731029045 103517699946473599783973)
                ·
                  rfl

theorem cell19_340200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_340200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340200 prefixEnd_340200 := by exact prefixLift 340200
  have htrace : WordTrace (prefixWord ++ tailWord_340200) baseStart_340200 baseEnd_340200 := by
    simpa [prefixWord, tailWord_340200, baseEnd_340200] using wordTrace_append hprefix tailTrace_340200
  have hstable : (prefixWord ++ tailWord_340200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340200).length < 2 ^ (prefixWord ++ tailWord_340200).sum := by decide
  have hdescent : baseEnd_340200 < baseStart_340200 := by decide
  rcases family_descends (prefixWord ++ tailWord_340200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340253 : List Nat := [1, 4, 2, 3, 2, 1, 3, 3]
def baseStart_340253 : Nat := 118140960795 + 340253 * 2 ^ 59
def prefixEnd_340253 : Nat := 4983230072969 + 3 ^ 40 * 340253 * 2
def baseEnd_340253 : Nat := 103533827042585180606051

theorem tailTrace_340253 : CollatzResearch.WordTrace tailWord_340253 prefixEnd_340253 103533827042585180606051 := by
  unfold tailWord_340253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12410046436328966431089413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8273364290885977620726275 12410046436328966431089413)
  ·
    refine ⟨2326883706811681205829265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12410046436328966431089413 2326883706811681205829265)
    ·
      refine ⟨1745162780108760904371949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2326883706811681205829265 1745162780108760904371949)
      ·
        refine ⟨654436042540785339139481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1745162780108760904371949 654436042540785339139481)
        ·
          refine ⟨490827031905589004354611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654436042540785339139481 490827031905589004354611)
          ·
            refine ⟨736240547858383506531917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490827031905589004354611 736240547858383506531917)
            ·
              refine ⟨276090205446893814949469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 736240547858383506531917 276090205446893814949469)
              ·
                refine ⟨103533827042585180606051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276090205446893814949469 103533827042585180606051)
                ·
                  rfl

theorem cell19_340253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_340253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340253 prefixEnd_340253 := by exact prefixLift 340253
  have htrace : WordTrace (prefixWord ++ tailWord_340253) baseStart_340253 baseEnd_340253 := by
    simpa [prefixWord, tailWord_340253, baseEnd_340253] using wordTrace_append hprefix tailTrace_340253
  have hstable : (prefixWord ++ tailWord_340253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340253).length < 2 ^ (prefixWord ++ tailWord_340253).sum := by decide
  have hdescent : baseEnd_340253 < baseStart_340253 := by decide
  rcases family_descends (prefixWord ++ tailWord_340253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340255 : List Nat := [1, 1, 2, 4, 3, 2, 3, 3]
def baseStart_340255 : Nat := 118140960795 + 340255 * 2 ^ 59
def prefixEnd_340255 : Nat := 4983230072969 + 3 ^ 40 * 340255 * 2
def baseEnd_340255 : Nat := 103534435612249768561601

theorem tailTrace_340255 : CollatzResearch.WordTrace tailWord_340255 prefixEnd_340255 103534435612249768561601 := by
  unfold tailWord_340255
  simp only [CollatzResearch.WordTrace]
  refine ⟨12410119382321720772662219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8273412921547813848441479 12410119382321720772662219)
  ·
    refine ⟨18615179073482581158993329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12410119382321720772662219 18615179073482581158993329)
    ·
      refine ⟨13961384305111935869244997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18615179073482581158993329 13961384305111935869244997)
      ·
        refine ⟨2617759557208487975483437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13961384305111935869244997 2617759557208487975483437)
        ·
          refine ⟨981659833953182990806289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2617759557208487975483437 981659833953182990806289)
          ·
            refine ⟨736244875464887243104717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981659833953182990806289 736244875464887243104717)
            ·
              refine ⟨276091828299332716164269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 736244875464887243104717 276091828299332716164269)
              ·
                refine ⟨103534435612249768561601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276091828299332716164269 103534435612249768561601)
                ·
                  rfl

theorem cell19_340255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_340255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340255 prefixEnd_340255 := by exact prefixLift 340255
  have htrace : WordTrace (prefixWord ++ tailWord_340255) baseStart_340255 baseEnd_340255 := by
    simpa [prefixWord, tailWord_340255, baseEnd_340255] using wordTrace_append hprefix tailTrace_340255
  have hstable : (prefixWord ++ tailWord_340255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340255).length < 2 ^ (prefixWord ++ tailWord_340255).sum := by decide
  have hdescent : baseEnd_340255 < baseStart_340255 := by decide
  rcases family_descends (prefixWord ++ tailWord_340255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340297 : List Nat := [1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_340297 : Nat := 118140960795 + 340297 * 2 ^ 59
def prefixEnd_340297 : Nat := 4983230072969 + 3 ^ 40 * 340297 * 2
def baseEnd_340297 : Nat := 103547215575206115628153

theorem tailTrace_340297 : CollatzResearch.WordTrace tailWord_340297 prefixEnd_340297 103547215575206115628153 := by
  unfold tailWord_340297
  simp only [CollatzResearch.WordTrace]
  refine ⟨12411651248169561945691145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8274434165446374630460763 12411651248169561945691145)
  ·
    refine ⟨9308738436127171459268359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12411651248169561945691145 9308738436127171459268359)
    ·
      refine ⟨13963107654190757188902539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9308738436127171459268359 13963107654190757188902539)
      ·
        refine ⟨20944661481286135783353809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13963107654190757188902539 20944661481286135783353809)
        ·
          refine ⟨15708496110964601837515357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20944661481286135783353809 15708496110964601837515357)
          ·
            refine ⟨5890686041611725689068259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15708496110964601837515357 5890686041611725689068259)
            ·
              refine ⟨8836029062417588533602389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890686041611725689068259 8836029062417588533602389)
              ·
                refine ⟨103547215575206115628153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8836029062417588533602389 103547215575206115628153)
                ·
                  rfl

theorem cell19_340297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_340297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340297 prefixEnd_340297 := by exact prefixLift 340297
  have htrace : WordTrace (prefixWord ++ tailWord_340297) baseStart_340297 baseEnd_340297 := by
    simpa [prefixWord, tailWord_340297, baseEnd_340297] using wordTrace_append hprefix tailTrace_340297
  have hstable : (prefixWord ++ tailWord_340297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340297).length < 2 ^ (prefixWord ++ tailWord_340297).sum := by decide
  have hdescent : baseEnd_340297 < baseStart_340297 := by decide
  rcases family_descends (prefixWord ++ tailWord_340297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340405 : List Nat := [1, 3, 3, 2, 4, 1, 1, 4]
def baseStart_340405 : Nat := 118140960795 + 340405 * 2 ^ 59
def prefixEnd_340405 : Nat := 4983230072969 + 3 ^ 40 * 340405 * 2
def baseEnd_340405 : Nat := 103580078337093865227859

theorem tailTrace_340405 : CollatzResearch.WordTrace tailWord_340405 prefixEnd_340405 103580078337093865227859 := by
  unfold tailWord_340405
  simp only [CollatzResearch.WordTrace]
  refine ⟨12415590331778296390622669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8277060221185530927081779 12415590331778296390622669)
  ·
    refine ⟨4655846374416861146483501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12415590331778296390622669 4655846374416861146483501)
    ·
      refine ⟨1745942390406322929931313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4655846374416861146483501 1745942390406322929931313)
      ·
        refine ⟨1309456792804742197448485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1745942390406322929931313 1309456792804742197448485)
        ·
          refine ⟨245523148650889162021591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1309456792804742197448485 245523148650889162021591)
          ·
            refine ⟨368284722976333743032387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245523148650889162021591 368284722976333743032387)
            ·
              refine ⟨552427084464500614548581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368284722976333743032387 552427084464500614548581)
              ·
                refine ⟨103580078337093865227859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552427084464500614548581 103580078337093865227859)
                ·
                  rfl

theorem cell19_340405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 4].length) (baseStart_340405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340405 prefixEnd_340405 := by exact prefixLift 340405
  have htrace : WordTrace (prefixWord ++ tailWord_340405) baseStart_340405 baseEnd_340405 := by
    simpa [prefixWord, tailWord_340405, baseEnd_340405] using wordTrace_append hprefix tailTrace_340405
  have hstable : (prefixWord ++ tailWord_340405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340405).length < 2 ^ (prefixWord ++ tailWord_340405).sum := by decide
  have hdescent : baseEnd_340405 < baseStart_340405 := by decide
  rcases family_descends (prefixWord ++ tailWord_340405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340409 : List Nat := [1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_340409 : Nat := 118140960795 + 340409 * 2 ^ 59
def prefixEnd_340409 : Nat := 4983230072969 + 3 ^ 40 * 340409 * 2
def baseEnd_340409 : Nat := 103581295476423041138959

theorem tailTrace_340409 : CollatzResearch.WordTrace tailWord_340409 prefixEnd_340409 103581295476423041138959 := by
  unfold tailWord_340409
  simp only [CollatzResearch.WordTrace]
  refine ⟨12415736223763805073768281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8277157482509203382512187 12415736223763805073768281)
  ·
    refine ⟨9311802167822853805326211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12415736223763805073768281 9311802167822853805326211)
    ·
      refine ⟨13967703251734280707989317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9311802167822853805326211 13967703251734280707989317)
      ·
        refine ⟨2618944359700177632747997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13967703251734280707989317 2618944359700177632747997)
        ·
          refine ⟨982104134887566612280499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2618944359700177632747997 982104134887566612280499)
          ·
            refine ⟨1473156202331349918420749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982104134887566612280499 1473156202331349918420749)
            ·
              refine ⟨552433575874256219407781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1473156202331349918420749 552433575874256219407781)
              ·
                refine ⟨103581295476423041138959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552433575874256219407781 103581295476423041138959)
                ·
                  rfl

theorem cell19_340409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_340409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340409 prefixEnd_340409 := by exact prefixLift 340409
  have htrace : WordTrace (prefixWord ++ tailWord_340409) baseStart_340409 baseEnd_340409 := by
    simpa [prefixWord, tailWord_340409, baseEnd_340409] using wordTrace_append hprefix tailTrace_340409
  have hstable : (prefixWord ++ tailWord_340409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340409).length < 2 ^ (prefixWord ++ tailWord_340409).sum := by decide
  have hdescent : baseEnd_340409 < baseStart_340409 := by decide
  rcases family_descends (prefixWord ++ tailWord_340409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340449 : List Nat := [1, 2, 3, 1, 2, 2, 8]
def baseStart_340449 : Nat := 118140960795 + 340449 * 2 ^ 59
def prefixEnd_340449 : Nat := 4983230072969 + 3 ^ 40 * 340449 * 2
def baseEnd_340449 : Nat := 34531155623238266749987

theorem tailTrace_340449 : CollatzResearch.WordTrace tailWord_340449 prefixEnd_340449 34531155623238266749987 := by
  unfold tailWord_340449
  simp only [CollatzResearch.WordTrace]
  refine ⟨12417195143618891905224401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8278130095745927936816267 12417195143618891905224401)
  ·
    refine ⟨9312896357714168928918301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12417195143618891905224401 9312896357714168928918301)
    ·
      refine ⟨3492336134142813348344363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9312896357714168928918301 3492336134142813348344363)
      ·
        refine ⟨5238504201214220022516545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3492336134142813348344363 5238504201214220022516545)
        ·
          refine ⟨3928878150910665016887409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5238504201214220022516545 3928878150910665016887409)
          ·
            refine ⟨2946658613182998762665557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3928878150910665016887409 2946658613182998762665557)
            ·
              refine ⟨34531155623238266749987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2946658613182998762665557 34531155623238266749987)
              ·
                rfl

theorem cell19_340449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_340449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340449 prefixEnd_340449 := by exact prefixLift 340449
  have htrace : WordTrace (prefixWord ++ tailWord_340449) baseStart_340449 baseEnd_340449 := by
    simpa [prefixWord, tailWord_340449, baseEnd_340449] using wordTrace_append hprefix tailTrace_340449
  have hstable : (prefixWord ++ tailWord_340449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340449).length < 2 ^ (prefixWord ++ tailWord_340449).sum := by decide
  have hdescent : baseEnd_340449 < baseStart_340449 := by decide
  rcases family_descends (prefixWord ++ tailWord_340449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340485 : List Nat := [1, 3, 1, 1, 2, 2, 6, 3]
def baseStart_340485 : Nat := 118140960795 + 340485 * 2 ^ 59
def prefixEnd_340485 : Nat := 4983230072969 + 3 ^ 40 * 340485 * 2
def baseEnd_340485 : Nat := 103604421123677383449863

theorem tailTrace_340485 : CollatzResearch.WordTrace tailWord_340485 prefixEnd_340485 103604421123677383449863 := by
  unfold tailWord_340485
  simp only [CollatzResearch.WordTrace]
  refine ⟨12418508171488470053534909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8279005447658980035689939 12418508171488470053534909)
  ·
    refine ⟨4656940564308176270075591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12418508171488470053534909 4656940564308176270075591)
    ·
      refine ⟨6985410846462264405113387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4656940564308176270075591 6985410846462264405113387)
      ·
        refine ⟨10478116269693396607670081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6985410846462264405113387 10478116269693396607670081)
        ·
          refine ⟨7858587202270047455752561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10478116269693396607670081 7858587202270047455752561)
          ·
            refine ⟨5893940401702535591814421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7858587202270047455752561 5893940401702535591814421)
            ·
              refine ⟨276278456329806355866301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5893940401702535591814421 276278456329806355866301)
              ·
                refine ⟨103604421123677383449863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276278456329806355866301 103604421123677383449863)
                ·
                  rfl

theorem cell19_340485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_340485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340485 prefixEnd_340485 := by exact prefixLift 340485
  have htrace : WordTrace (prefixWord ++ tailWord_340485) baseStart_340485 baseEnd_340485 := by
    simpa [prefixWord, tailWord_340485, baseEnd_340485] using wordTrace_append hprefix tailTrace_340485
  have hstable : (prefixWord ++ tailWord_340485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340485).length < 2 ^ (prefixWord ++ tailWord_340485).sum := by decide
  have hdescent : baseEnd_340485 < baseStart_340485 := by decide
  rcases family_descends (prefixWord ++ tailWord_340485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340504 : List Nat := [2, 1, 2, 3, 3, 3, 5]
def baseStart_340504 : Nat := 118140960795 + 340504 * 2 ^ 59
def prefixEnd_340504 : Nat := 4983230072969 + 3 ^ 40 * 340504 * 2
def baseEnd_340504 : Nat := 34536734178496989675863

theorem tailTrace_340504 : CollatzResearch.WordTrace tailWord_340504 prefixEnd_340504 34536734178496989675863 := by
  unfold tailWord_340504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209600579209818149238283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8279467438946424198984377 6209600579209818149238283)
  ·
    refine ⟨9314400868814727223857425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6209600579209818149238283 9314400868814727223857425)
    ·
      refine ⟨6985800651611045417893069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9314400868814727223857425 6985800651611045417893069)
      ·
        refine ⟨2619675244354142031709901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6985800651611045417893069 2619675244354142031709901)
        ·
          refine ⟨982378216632803261891213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2619675244354142031709901 982378216632803261891213)
          ·
            refine ⟨368391831237301223209205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 982378216632803261891213 368391831237301223209205)
            ·
              refine ⟨34536734178496989675863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 368391831237301223209205 34536734178496989675863)
              ·
                rfl

theorem cell19_340504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_340504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340504 prefixEnd_340504 := by exact prefixLift 340504
  have htrace : WordTrace (prefixWord ++ tailWord_340504) baseStart_340504 baseEnd_340504 := by
    simpa [prefixWord, tailWord_340504, baseEnd_340504] using wordTrace_append hprefix tailTrace_340504
  have hstable : (prefixWord ++ tailWord_340504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340504).length < 2 ^ (prefixWord ++ tailWord_340504).sum := by decide
  have hdescent : baseEnd_340504 < baseStart_340504 := by decide
  rcases family_descends (prefixWord ++ tailWord_340504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340506 : List Nat := [3, 1, 1, 3, 1, 1, 9]
def baseStart_340506 : Nat := 118140960795 + 340506 * 2 ^ 59
def prefixEnd_340506 : Nat := 4983230072969 + 3 ^ 40 * 340506 * 2
def baseEnd_340506 : Nat := 34536937035051852327713

theorem tailTrace_340506 : CollatzResearch.WordTrace tailWord_340506 prefixEnd_340506 34536937035051852327713 := by
  unfold tailWord_340506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104818526103097660012343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8279516069608260426699581 3104818526103097660012343)
  ·
    refine ⟨4657227789154646490018515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3104818526103097660012343 4657227789154646490018515)
    ·
      refine ⟨6985841683731969735027773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4657227789154646490018515 6985841683731969735027773)
      ·
        refine ⟨2619690631399488650635415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6985841683731969735027773 2619690631399488650635415)
        ·
          refine ⟨3929535947099232975953123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619690631399488650635415 3929535947099232975953123)
          ·
            refine ⟨5894303920648849463929685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929535947099232975953123 5894303920648849463929685)
            ·
              refine ⟨34536937035051852327713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5894303920648849463929685 34536937035051852327713)
              ·
                rfl

theorem cell19_340506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_340506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340506 prefixEnd_340506 := by exact prefixLift 340506
  have htrace : WordTrace (prefixWord ++ tailWord_340506) baseStart_340506 baseEnd_340506 := by
    simpa [prefixWord, tailWord_340506, baseEnd_340506] using wordTrace_append hprefix tailTrace_340506
  have hstable : (prefixWord ++ tailWord_340506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340506).length < 2 ^ (prefixWord ++ tailWord_340506).sum := by decide
  have hdescent : baseEnd_340506 < baseStart_340506 := by decide
  rcases family_descends (prefixWord ++ tailWord_340506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340519 : List Nat := [1, 1, 7, 2, 1, 1, 2, 4]
def baseStart_340519 : Nat := 118140960795 + 340519 * 2 ^ 59
def prefixEnd_340519 : Nat := 4983230072969 + 3 ^ 40 * 340519 * 2
def baseEnd_340519 : Nat := 103614766807975378694215

theorem tailTrace_340519 : CollatzResearch.WordTrace tailWord_340519 prefixEnd_340519 103614766807975378694215 := by
  unfold tailWord_340519
  simp only [CollatzResearch.WordTrace]
  refine ⟨12419748253365293860272611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8279832168910195906848407 12419748253365293860272611)
  ·
    refine ⟨18629622380047940790408917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12419748253365293860272611 18629622380047940790408917)
    ·
      refine ⟨436631774532373612275209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18629622380047940790408917 436631774532373612275209)
      ·
        refine ⟨327473830899280209206407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436631774532373612275209 327473830899280209206407)
        ·
          refine ⟨491210746348920313809611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327473830899280209206407 491210746348920313809611)
          ·
            refine ⟨736816119523380470714417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491210746348920313809611 736816119523380470714417)
            ·
              refine ⟨552612089642535353035813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736816119523380470714417 552612089642535353035813)
              ·
                refine ⟨103614766807975378694215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552612089642535353035813 103614766807975378694215)
                ·
                  rfl

theorem cell19_340519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_340519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340519 prefixEnd_340519 := by exact prefixLift 340519
  have htrace : WordTrace (prefixWord ++ tailWord_340519) baseStart_340519 baseEnd_340519 := by
    simpa [prefixWord, tailWord_340519, baseEnd_340519] using wordTrace_append hprefix tailTrace_340519
  have hstable : (prefixWord ++ tailWord_340519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340519).length < 2 ^ (prefixWord ++ tailWord_340519).sum := by decide
  have hdescent : baseEnd_340519 < baseStart_340519 := by decide
  rcases family_descends (prefixWord ++ tailWord_340519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340544 : List Nat := [2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_340544 : Nat := 118140960795 + 340544 * 2 ^ 59
def prefixEnd_340544 : Nat := 4983230072969 + 3 ^ 40 * 340544 * 2
def baseEnd_340544 : Nat := 103622373928782728138591

theorem tailTrace_340544 : CollatzResearch.WordTrace tailWord_340544 prefixEnd_340544 103622373928782728138591 := by
  unfold tailWord_340544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210330039137361564966343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8280440052183148753288457 6210330039137361564966343)
  ·
    refine ⟨9315495058706042347449515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6210330039137361564966343 9315495058706042347449515)
    ·
      refine ⟨13973242588059063521174273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9315495058706042347449515 13973242588059063521174273)
      ·
        refine ⟨10479931941044297640880705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13973242588059063521174273 10479931941044297640880705)
        ·
          refine ⟨7859948955783223230660529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10479931941044297640880705 7859948955783223230660529)
          ·
            refine ⟨5894961716837417422995397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859948955783223230660529 5894961716837417422995397)
            ·
              refine ⟨1105305321907015766811637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5894961716837417422995397 1105305321907015766811637)
              ·
                refine ⟨103622373928782728138591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1105305321907015766811637 103622373928782728138591)
                ·
                  rfl

theorem cell19_340544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_340544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340544 prefixEnd_340544 := by exact prefixLift 340544
  have htrace : WordTrace (prefixWord ++ tailWord_340544) baseStart_340544 baseEnd_340544 := by
    simpa [prefixWord, tailWord_340544, baseEnd_340544] using wordTrace_append hprefix tailTrace_340544
  have hstable : (prefixWord ++ tailWord_340544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340544).length < 2 ^ (prefixWord ++ tailWord_340544).sum := by decide
  have hdescent : baseEnd_340544 < baseStart_340544 := by decide
  rcases family_descends (prefixWord ++ tailWord_340544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340618 : List Nat := [3, 1, 2, 3, 3, 1, 6]
def baseStart_340618 : Nat := 118140960795 + 340618 * 2 ^ 59
def prefixEnd_340618 : Nat := 4983230072969 + 3 ^ 40 * 340618 * 2
def baseEnd_340618 : Nat := 34548297002124160831315

theorem tailTrace_340618 : CollatzResearch.WordTrace tailWord_340618 prefixEnd_340618 34548297002124160831315 := by
  unfold tailWord_340618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105839770001658442031627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8282239386671089178751005 3105839770001658442031627)
  ·
    refine ⟨4658759655002487663047441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3105839770001658442031627 4658759655002487663047441)
    ·
      refine ⟨3494069741251865747285581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4658759655002487663047441 3494069741251865747285581)
      ·
        refine ⟨1310276152969449655232093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3494069741251865747285581 1310276152969449655232093)
        ·
          refine ⟨491353557363543620712035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1310276152969449655232093 491353557363543620712035)
          ·
            refine ⟨737030336045315431068053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491353557363543620712035 737030336045315431068053)
            ·
              refine ⟨34548297002124160831315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 737030336045315431068053 34548297002124160831315)
              ·
                rfl

theorem cell19_340618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_340618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340618 prefixEnd_340618 := by exact prefixLift 340618
  have htrace : WordTrace (prefixWord ++ tailWord_340618) baseStart_340618 baseEnd_340618 := by
    simpa [prefixWord, tailWord_340618, baseEnd_340618] using wordTrace_append hprefix tailTrace_340618
  have hstable : (prefixWord ++ tailWord_340618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340618).length < 2 ^ (prefixWord ++ tailWord_340618).sum := by decide
  have hdescent : baseEnd_340618 < baseStart_340618 := by decide
  rcases family_descends (prefixWord ++ tailWord_340618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340650 : List Nat := [3, 1, 5, 2, 1, 2, 2, 3]
def baseStart_340650 : Nat := 118140960795 + 340650 * 2 ^ 59
def prefixEnd_340650 : Nat := 4983230072969 + 3 ^ 40 * 340650 * 2
def baseEnd_340650 : Nat := 103654628121005889782747

theorem tailTrace_340650 : CollatzResearch.WordTrace tailWord_340650 prefixEnd_340650 103654628121005889782747 := by
  unfold tailWord_340650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3106131553972675808322851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8283017477260468822194269 3106131553972675808322851)
  ·
    refine ⟨4659197330959013712484277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3106131553972675808322851 4659197330959013712484277)
    ·
      refine ⟨436799749777407535545401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4659197330959013712484277 436799749777407535545401)
      ·
        refine ⟨327599812333055651659051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436799749777407535545401 327599812333055651659051)
        ·
          refine ⟨491399718499583477488577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327599812333055651659051 491399718499583477488577)
          ·
            refine ⟨368549788874687608116433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491399718499583477488577 368549788874687608116433)
            ·
              refine ⟨276412341656015706087325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368549788874687608116433 276412341656015706087325)
              ·
                refine ⟨103654628121005889782747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276412341656015706087325 103654628121005889782747)
                ·
                  rfl

theorem cell19_340650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_340650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340650 prefixEnd_340650 := by exact prefixLift 340650
  have htrace : WordTrace (prefixWord ++ tailWord_340650) baseStart_340650 baseEnd_340650 := by
    simpa [prefixWord, tailWord_340650, baseEnd_340650] using wordTrace_append hprefix tailTrace_340650
  have hstable : (prefixWord ++ tailWord_340650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340650).length < 2 ^ (prefixWord ++ tailWord_340650).sum := by decide
  have hdescent : baseEnd_340650 < baseStart_340650 := by decide
  rcases family_descends (prefixWord ++ tailWord_340650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340654 : List Nat := [4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_340654 : Nat := 118140960795 + 340654 * 2 ^ 59
def prefixEnd_340654 : Nat := 4983230072969 + 3 ^ 40 * 340654 * 2
def baseEnd_340654 : Nat := 103655845260335065693847

theorem tailTrace_340654 : CollatzResearch.WordTrace tailWord_340654 prefixEnd_340654 103655845260335065693847 := by
  unfold tailWord_340654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1553084013484526489554627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8283114738584141277624677 1553084013484526489554627)
  ·
    refine ⟨2329626020226789734331941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1553084013484526489554627 2329626020226789734331941)
    ·
      refine ⟨436804878792523075187239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2329626020226789734331941 436804878792523075187239)
      ·
        refine ⟨655207318188784612780859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436804878792523075187239 655207318188784612780859)
        ·
          refine ⟨982810977283176919171289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655207318188784612780859 982810977283176919171289)
          ·
            refine ⟨737108232962382689378467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982810977283176919171289 737108232962382689378467)
            ·
              refine ⟨1105662349443574034067701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737108232962382689378467 1105662349443574034067701)
              ·
                refine ⟨103655845260335065693847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1105662349443574034067701 103655845260335065693847)
                ·
                  rfl

theorem cell19_340654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_340654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340654 prefixEnd_340654 := by exact prefixLift 340654
  have htrace : WordTrace (prefixWord ++ tailWord_340654) baseStart_340654 baseEnd_340654 := by
    simpa [prefixWord, tailWord_340654, baseEnd_340654] using wordTrace_append hprefix tailTrace_340654
  have hstable : (prefixWord ++ tailWord_340654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340654).length < 2 ^ (prefixWord ++ tailWord_340654).sum := by decide
  have hdescent : baseEnd_340654 < baseStart_340654 := by decide
  rcases family_descends (prefixWord ++ tailWord_340654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340692 : List Nat := [2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_340692 : Nat := 118140960795 + 340692 * 2 ^ 59
def prefixEnd_340692 : Nat := 4983230072969 + 3 ^ 40 * 340692 * 2
def baseEnd_340692 : Nat := 103667408083962236849299

theorem tailTrace_340692 : CollatzResearch.WordTrace tailWord_340692 prefixEnd_340692 103667408083962236849299 := by
  unfold tailWord_340692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213029040869272203160165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8284038721159029604213553 6213029040869272203160165)
  ·
    refine ⟨1164942945162988538092531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6213029040869272203160165 1164942945162988538092531)
    ·
      refine ⟨1747414417744482807138797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1164942945162988538092531 1747414417744482807138797)
      ·
        refine ⟨655280406654181052677049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1747414417744482807138797 655280406654181052677049)
        ·
          refine ⟨491460304990635789507787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655280406654181052677049 491460304990635789507787)
          ·
            refine ⟨737190457485953684261681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491460304990635789507787 737190457485953684261681)
            ·
              refine ⟨552892843114465263196261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737190457485953684261681 552892843114465263196261)
              ·
                refine ⟨103667408083962236849299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552892843114465263196261 103667408083962236849299)
                ·
                  rfl

theorem cell19_340692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_340692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340692 prefixEnd_340692 := by exact prefixLift 340692
  have htrace : WordTrace (prefixWord ++ tailWord_340692) baseStart_340692 baseEnd_340692 := by
    simpa [prefixWord, tailWord_340692, baseEnd_340692] using wordTrace_append hprefix tailTrace_340692
  have hstable : (prefixWord ++ tailWord_340692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340692).length < 2 ^ (prefixWord ++ tailWord_340692).sum := by decide
  have hdescent : baseEnd_340692 < baseStart_340692 := by decide
  rcases family_descends (prefixWord ++ tailWord_340692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340696 : List Nat := [2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_340696 : Nat := 118140960795 + 340696 * 2 ^ 59
def prefixEnd_340696 : Nat := 4983230072969 + 3 ^ 40 * 340696 * 2
def baseEnd_340696 : Nat := 103668625223291412760399

theorem tailTrace_340696 : CollatzResearch.WordTrace tailWord_340696 prefixEnd_340696 103668625223291412760399 := by
  unfold tailWord_340696
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213101986862026544732971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8284135982482702059643961 6213101986862026544732971)
  ·
    refine ⟨9319652980293039817099457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213101986862026544732971 9319652980293039817099457)
    ·
      refine ⟨6989739735219779862824593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9319652980293039817099457 6989739735219779862824593)
      ·
        refine ⟨5242304801414834897118445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6989739735219779862824593 5242304801414834897118445)
        ·
          refine ⟨1965864300530563086419417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5242304801414834897118445 1965864300530563086419417)
          ·
            refine ⟨1474398225397922314814563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1965864300530563086419417 1474398225397922314814563)
            ·
              refine ⟨2211597338096883472221845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474398225397922314814563 2211597338096883472221845)
              ·
                refine ⟨103668625223291412760399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2211597338096883472221845 103668625223291412760399)
                ·
                  rfl

theorem cell19_340696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_340696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340696 prefixEnd_340696 := by exact prefixLift 340696
  have htrace : WordTrace (prefixWord ++ tailWord_340696) baseStart_340696 baseEnd_340696 := by
    simpa [prefixWord, tailWord_340696, baseEnd_340696] using wordTrace_append hprefix tailTrace_340696
  have hstable : (prefixWord ++ tailWord_340696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340696).length < 2 ^ (prefixWord ++ tailWord_340696).sum := by decide
  have hdescent : baseEnd_340696 < baseStart_340696 := by decide
  rcases family_descends (prefixWord ++ tailWord_340696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340753 : List Nat := [1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_340753 : Nat := 118140960795 + 340753 * 2 ^ 59
def prefixEnd_340753 : Nat := 4983230072969 + 3 ^ 40 * 340753 * 2
def baseEnd_340753 : Nat := 103685969458732169493577

theorem tailTrace_340753 : CollatzResearch.WordTrace tailWord_340753 prefixEnd_340753 103685969458732169493577 := by
  unfold tailWord_340753
  simp only [CollatzResearch.WordTrace]
  refine ⟨12428282934517551824290913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8285521956345034549527275 12428282934517551824290913)
  ·
    refine ⟨9321212200888163868218185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12428282934517551824290913 9321212200888163868218185)
    ·
      refine ⟨6990909150666122901163639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9321212200888163868218185 6990909150666122901163639)
      ·
        refine ⟨10486363725999184351745459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990909150666122901163639 10486363725999184351745459)
        ·
          refine ⟨15729545588998776527618189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10486363725999184351745459 15729545588998776527618189)
          ·
            refine ⟨5898579595874541197856821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15729545588998776527618189 5898579595874541197856821)
            ·
              refine ⟨552991837113238237299077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5898579595874541197856821 552991837113238237299077)
              ·
                refine ⟨103685969458732169493577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552991837113238237299077 103685969458732169493577)
                ·
                  rfl

theorem cell19_340753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_340753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340753 prefixEnd_340753 := by exact prefixLift 340753
  have htrace : WordTrace (prefixWord ++ tailWord_340753) baseStart_340753 baseEnd_340753 := by
    simpa [prefixWord, tailWord_340753, baseEnd_340753] using wordTrace_append hprefix tailTrace_340753
  have hstable : (prefixWord ++ tailWord_340753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340753).length < 2 ^ (prefixWord ++ tailWord_340753).sum := by decide
  have hdescent : baseEnd_340753 < baseStart_340753 := by decide
  rcases family_descends (prefixWord ++ tailWord_340753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340867 : List Nat := [1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_340867 : Nat := 118140960795 + 340867 * 2 ^ 59
def prefixEnd_340867 : Nat := 4983230072969 + 3 ^ 40 * 340867 * 2
def baseEnd_340867 : Nat := 103720657929613682959933

theorem tailTrace_340867 : CollatzResearch.WordTrace tailWord_340867 prefixEnd_340867 103720657929613682959933 := by
  unfold tailWord_340867
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432440856104549293940855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8288293904069699529293903 12432440856104549293940855)
  ·
    refine ⟨18648661284156823940911283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12432440856104549293940855 18648661284156823940911283)
    ·
      refine ⟨27972991926235235911366925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18648661284156823940911283 27972991926235235911366925)
      ·
        refine ⟨10489871972338213466762597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27972991926235235911366925 10489871972338213466762597)
        ·
          refine ⟨1966850994813415025017987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10489871972338213466762597 1966850994813415025017987)
          ·
            refine ⟨2950276492220122537526981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966850994813415025017987 2950276492220122537526981)
            ·
              refine ⟨553176842291272975786309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2950276492220122537526981 553176842291272975786309)
              ·
                refine ⟨103720657929613682959933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 553176842291272975786309 103720657929613682959933)
                ·
                  rfl

theorem cell19_340867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_340867 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340867 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340867 prefixEnd_340867 := by exact prefixLift 340867
  have htrace : WordTrace (prefixWord ++ tailWord_340867) baseStart_340867 baseEnd_340867 := by
    simpa [prefixWord, tailWord_340867, baseEnd_340867] using wordTrace_append hprefix tailTrace_340867
  have hstable : (prefixWord ++ tailWord_340867).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340867).length < 2 ^ (prefixWord ++ tailWord_340867).sum := by decide
  have hdescent : baseEnd_340867 < baseStart_340867 := by decide
  rcases family_descends (prefixWord ++ tailWord_340867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340903 : List Nat := [1, 1, 6, 1, 4, 6]
def baseStart_340903 : Nat := 118140960795 + 340903 * 2 ^ 59
def prefixEnd_340903 : Nat := 4983230072969 + 3 ^ 40 * 340903 * 2
def baseEnd_340903 : Nat := 11525734687064029573315

theorem tailTrace_340903 : CollatzResearch.WordTrace tailWord_340903 prefixEnd_340903 11525734687064029573315 := by
  unfold tailWord_340903
  simp only [CollatzResearch.WordTrace]
  refine ⟨12433753883974127442251363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8289169255982751628167575 12433753883974127442251363)
  ·
    refine ⟨18650630825961191163377045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12433753883974127442251363 18650630825961191163377045)
    ·
      refine ⟨874248319966930835783299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18650630825961191163377045 874248319966930835783299)
      ·
        refine ⟨1311372479950396253674949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874248319966930835783299 1311372479950396253674949)
        ·
          refine ⟨245882339990699297564053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1311372479950396253674949 245882339990699297564053)
          ·
            refine ⟨11525734687064029573315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 245882339990699297564053 11525734687064029573315)
            ·
              rfl

theorem cell19_340903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 6].length) (baseStart_340903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_340903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_340903 prefixEnd_340903 := by exact prefixLift 340903
  have htrace : WordTrace (prefixWord ++ tailWord_340903) baseStart_340903 baseEnd_340903 := by
    simpa [prefixWord, tailWord_340903, baseEnd_340903] using wordTrace_append hprefix tailTrace_340903
  have hstable : (prefixWord ++ tailWord_340903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340903).length < 2 ^ (prefixWord ++ tailWord_340903).sum := by decide
  have hdescent : baseEnd_340903 < baseStart_340903 := by decide
  rcases family_descends (prefixWord ++ tailWord_340903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341000 : List Nat := [2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_341000 : Nat := 118140960795 + 341000 * 2 ^ 59
def prefixEnd_341000 : Nat := 4983230072969 + 3 ^ 40 * 341000 * 2
def baseEnd_341000 : Nat := 103761127812308782004015

theorem tailTrace_341000 : CollatzResearch.WordTrace tailWord_341000 prefixEnd_341000 103761127812308782004015 := by
  unfold tailWord_341000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6218645882311356504266227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8291527843081808672354969 6218645882311356504266227)
  ·
    refine ⟨9327968823467034756399341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6218645882311356504266227 9327968823467034756399341)
    ·
      refine ⟨3497988308800138033649753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9327968823467034756399341 3497988308800138033649753)
      ·
        refine ⟨2623491231600103525237315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3497988308800138033649753 2623491231600103525237315)
        ·
          refine ⟨3935236847400155287855973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623491231600103525237315 3935236847400155287855973)
          ·
            refine ⟨737856908887529116472995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3935236847400155287855973 737856908887529116472995)
            ·
              refine ⟨1106785363331293674709493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737856908887529116472995 1106785363331293674709493)
              ·
                refine ⟨103761127812308782004015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1106785363331293674709493 103761127812308782004015)
                ·
                  rfl

theorem cell19_341000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_341000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341000 prefixEnd_341000 := by exact prefixLift 341000
  have htrace : WordTrace (prefixWord ++ tailWord_341000) baseStart_341000 baseEnd_341000 := by
    simpa [prefixWord, tailWord_341000, baseEnd_341000] using wordTrace_append hprefix tailTrace_341000
  have hstable : (prefixWord ++ tailWord_341000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341000).length < 2 ^ (prefixWord ++ tailWord_341000).sum := by decide
  have hdescent : baseEnd_341000 < baseStart_341000 := by decide
  rcases family_descends (prefixWord ++ tailWord_341000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341059 : List Nat := [1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_341059 : Nat := 118140960795 + 341059 * 2 ^ 59
def prefixEnd_341059 : Nat := 4983230072969 + 3 ^ 40 * 341059 * 2
def baseEnd_341059 : Nat := 103779080617414126692743

theorem tailTrace_341059 : CollatzResearch.WordTrace tailWord_341059 prefixEnd_341059 103779080617414126692743 := by
  unfold tailWord_341059
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439443671408966084930231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8292962447605977389953487 12439443671408966084930231)
  ·
    refine ⟨18659165507113449127395347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12439443671408966084930231 18659165507113449127395347)
    ·
      refine ⟨27988748260670173691093021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18659165507113449127395347 27988748260670173691093021)
      ·
        refine ⟨10495780597751315134159883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27988748260670173691093021 10495780597751315134159883)
        ·
          refine ⟨15743670896626972701239825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10495780597751315134159883 15743670896626972701239825)
          ·
            refine ⟨11807753172470229525929869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15743670896626972701239825 11807753172470229525929869)
            ·
              refine ⟨4427907439676336072223701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11807753172470229525929869 4427907439676336072223701)
              ·
                refine ⟨103779080617414126692743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4427907439676336072223701 103779080617414126692743)
                ·
                  rfl

theorem cell19_341059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_341059 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341059 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341059 prefixEnd_341059 := by exact prefixLift 341059
  have htrace : WordTrace (prefixWord ++ tailWord_341059) baseStart_341059 baseEnd_341059 := by
    simpa [prefixWord, tailWord_341059, baseEnd_341059] using wordTrace_append hprefix tailTrace_341059
  have hstable : (prefixWord ++ tailWord_341059).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341059).length < 2 ^ (prefixWord ++ tailWord_341059).sum := by decide
  have hdescent : baseEnd_341059 < baseStart_341059 := by decide
  rcases family_descends (prefixWord ++ tailWord_341059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341095 : List Nat := [1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_341095 : Nat := 118140960795 + 341095 * 2 ^ 59
def prefixEnd_341095 : Nat := 4983230072969 + 3 ^ 40 * 341095 * 2
def baseEnd_341095 : Nat := 103790034871376709892645

theorem tailTrace_341095 : CollatzResearch.WordTrace tailWord_341095 prefixEnd_341095 103790034871376709892645 := by
  unfold tailWord_341095
  simp only [CollatzResearch.WordTrace]
  refine ⟨12440756699278544233240739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8293837799519029488827159 12440756699278544233240739)
  ·
    refine ⟨18661135048917816349861109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12440756699278544233240739 18661135048917816349861109)
    ·
      refine ⟨1749481410836045282799479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18661135048917816349861109 1749481410836045282799479)
      ·
        refine ⟨2624222116254067924199219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749481410836045282799479 2624222116254067924199219)
        ·
          refine ⟨3936333174381101886298829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624222116254067924199219 3936333174381101886298829)
          ·
            refine ⟨1476124940392913207362061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3936333174381101886298829 1476124940392913207362061)
            ·
              refine ⟨553546852647342452760773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1476124940392913207362061 553546852647342452760773)
              ·
                refine ⟨103790034871376709892645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 553546852647342452760773 103790034871376709892645)
                ·
                  rfl

theorem cell19_341095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_341095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341095 prefixEnd_341095 := by exact prefixLift 341095
  have htrace : WordTrace (prefixWord ++ tailWord_341095) baseStart_341095 baseEnd_341095 := by
    simpa [prefixWord, tailWord_341095, baseEnd_341095] using wordTrace_append hprefix tailTrace_341095
  have hstable : (prefixWord ++ tailWord_341095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341095).length < 2 ^ (prefixWord ++ tailWord_341095).sum := by decide
  have hdescent : baseEnd_341095 < baseStart_341095 := by decide
  rcases family_descends (prefixWord ++ tailWord_341095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341165 : List Nat := [1, 5, 2, 1, 4, 1, 2, 3]
def baseStart_341165 : Nat := 118140960795 + 341165 * 2 ^ 59
def prefixEnd_341165 : Nat := 4983230072969 + 3 ^ 40 * 341165 * 2
def baseEnd_341165 : Nat := 103811334809637288336899

theorem tailTrace_341165 : CollatzResearch.WordTrace tailWord_341165 prefixEnd_341165 103811334809637288336899 := by
  unfold tailWord_341165
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443309809024946188288949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8295539872683297458859299 12443309809024946188288949)
  ·
    refine ⟨1166560294596088705152089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12443309809024946188288949 1166560294596088705152089)
    ·
      refine ⟨874920220947066528864067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1166560294596088705152089 874920220947066528864067)
      ·
        refine ⟨1312380331420599793296101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874920220947066528864067 1312380331420599793296101)
        ·
          refine ⟨246071312141362461243019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1312380331420599793296101 246071312141362461243019)
          ·
            refine ⟨369106968212043691864529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246071312141362461243019 369106968212043691864529)
            ·
              refine ⟨276830226159032768898397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369106968212043691864529 276830226159032768898397)
              ·
                refine ⟨103811334809637288336899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276830226159032768898397 103811334809637288336899)
                ·
                  rfl

theorem cell19_341165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 3].length) (baseStart_341165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341165 prefixEnd_341165 := by exact prefixLift 341165
  have htrace : WordTrace (prefixWord ++ tailWord_341165) baseStart_341165 baseEnd_341165 := by
    simpa [prefixWord, tailWord_341165, baseEnd_341165] using wordTrace_append hprefix tailTrace_341165
  have hstable : (prefixWord ++ tailWord_341165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341165).length < 2 ^ (prefixWord ++ tailWord_341165).sum := by decide
  have hdescent : baseEnd_341165 < baseStart_341165 := by decide
  rcases family_descends (prefixWord ++ tailWord_341165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341169 : List Nat := [1, 2, 2, 5, 1, 1, 4, 3]
def baseStart_341169 : Nat := 118140960795 + 341169 * 2 ^ 59
def prefixEnd_341169 : Nat := 4983230072969 + 3 ^ 40 * 341169 * 2
def baseEnd_341169 : Nat := 103812551948966464247999

theorem tailTrace_341169 : CollatzResearch.WordTrace tailWord_341169 prefixEnd_341169 103812551948966464247999 := by
  unfold tailWord_341169
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443455701010454871434561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8295637134006969914289707 12443455701010454871434561)
  ·
    refine ⟨9332591775757841153575921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12443455701010454871434561 9332591775757841153575921)
    ·
      refine ⟨6999443831818380865181941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9332591775757841153575921 6999443831818380865181941)
      ·
        refine ⟨656197859232973206110807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6999443831818380865181941 656197859232973206110807)
        ·
          refine ⟨984296788849459809166211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656197859232973206110807 984296788849459809166211)
          ·
            refine ⟨1476445183274189713749317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984296788849459809166211 1476445183274189713749317)
            ·
              refine ⟨276833471863910571327997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1476445183274189713749317 276833471863910571327997)
              ·
                refine ⟨103812551948966464247999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276833471863910571327997 103812551948966464247999)
                ·
                  rfl

theorem cell19_341169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_341169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341169 prefixEnd_341169 := by exact prefixLift 341169
  have htrace : WordTrace (prefixWord ++ tailWord_341169) baseStart_341169 baseEnd_341169 := by
    simpa [prefixWord, tailWord_341169, baseEnd_341169] using wordTrace_append hprefix tailTrace_341169
  have hstable : (prefixWord ++ tailWord_341169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341169).length < 2 ^ (prefixWord ++ tailWord_341169).sum := by decide
  have hdescent : baseEnd_341169 < baseStart_341169 := by decide
  rcases family_descends (prefixWord ++ tailWord_341169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341171 : List Nat := [1, 1, 1, 2, 3, 2, 6, 3]
def baseStart_341171 : Nat := 118140960795 + 341171 * 2 ^ 59
def prefixEnd_341171 : Nat := 4983230072969 + 3 ^ 40 * 341171 * 2
def baseEnd_341171 : Nat := 103813160518631052203549

theorem tailTrace_341171 : CollatzResearch.WordTrace tailWord_341171 prefixEnd_341171 103813160518631052203549 := by
  unfold tailWord_341171
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443528647003209213007367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8295685764668806142004911 12443528647003209213007367)
  ·
    refine ⟨18665292970504813819511051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12443528647003209213007367 18665292970504813819511051)
    ·
      refine ⟨27997939455757220729266577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18665292970504813819511051 27997939455757220729266577)
      ·
        refine ⟨20998454591817915546949933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27997939455757220729266577 20998454591817915546949933)
        ·
          refine ⟨7874420471931718330106225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20998454591817915546949933 7874420471931718330106225)
          ·
            refine ⟨5905815353948788747579669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7874420471931718330106225 5905815353948788747579669)
            ·
              refine ⟨276835094716349472542797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5905815353948788747579669 276835094716349472542797)
              ·
                refine ⟨103813160518631052203549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276835094716349472542797 103813160518631052203549)
                ·
                  rfl

theorem cell19_341171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_341171 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341171 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341171 prefixEnd_341171 := by exact prefixLift 341171
  have htrace : WordTrace (prefixWord ++ tailWord_341171) baseStart_341171 baseEnd_341171 := by
    simpa [prefixWord, tailWord_341171, baseEnd_341171] using wordTrace_append hprefix tailTrace_341171
  have hstable : (prefixWord ++ tailWord_341171).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341171).length < 2 ^ (prefixWord ++ tailWord_341171).sum := by decide
  have hdescent : baseEnd_341171 < baseStart_341171 := by decide
  rcases family_descends (prefixWord ++ tailWord_341171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341188 : List Nat := [2, 3, 3, 1, 3, 2, 5]
def baseStart_341188 : Nat := 118140960795 + 341188 * 2 ^ 59
def prefixEnd_341188 : Nat := 4983230072969 + 3 ^ 40 * 341188 * 2
def baseEnd_341188 : Nat := 34606111120260016608575

theorem tailTrace_341188 : CollatzResearch.WordTrace tailWord_341188 prefixEnd_341188 34606111120260016608575 := by
  unfold tailWord_341188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6222074343970810558188109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8296099125294414077584145 6222074343970810558188109)
  ·
    refine ⟨2333277878989053959320541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6222074343970810558188109 2333277878989053959320541)
    ·
      refine ⟨874979204620895234745203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2333277878989053959320541 874979204620895234745203)
      ·
        refine ⟨1312468806931342852117805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874979204620895234745203 1312468806931342852117805)
        ·
          refine ⟨492175802599253569544177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1312468806931342852117805 492175802599253569544177)
          ·
            refine ⟨369131851949440177158133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492175802599253569544177 369131851949440177158133)
            ·
              refine ⟨34606111120260016608575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 369131851949440177158133 34606111120260016608575)
              ·
                rfl

theorem cell19_341188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_341188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341188 prefixEnd_341188 := by exact prefixLift 341188
  have htrace : WordTrace (prefixWord ++ tailWord_341188) baseStart_341188 baseEnd_341188 := by
    simpa [prefixWord, tailWord_341188, baseEnd_341188] using wordTrace_append hprefix tailTrace_341188
  have hstable : (prefixWord ++ tailWord_341188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341188).length < 2 ^ (prefixWord ++ tailWord_341188).sum := by decide
  have hdescent : baseEnd_341188 < baseStart_341188 := by decide
  rcases family_descends (prefixWord ++ tailWord_341188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341192 : List Nat := [2, 1, 3, 1, 2, 1, 9]
def baseStart_341192 : Nat := 118140960795 + 341192 * 2 ^ 59
def prefixEnd_341192 : Nat := 4983230072969 + 3 ^ 40 * 341192 * 2
def baseEnd_341192 : Nat := 34606516833369741912275

theorem tailTrace_341192 : CollatzResearch.WordTrace tailWord_341192 prefixEnd_341192 34606516833369741912275 := by
  unfold tailWord_341192
  simp only [CollatzResearch.WordTrace]
  refine ⟨6222147289963564899760915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8296196386618086533014553 6222147289963564899760915)
  ·
    refine ⟨9333220934945347349641373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6222147289963564899760915 9333220934945347349641373)
    ·
      refine ⟨3499957850604505256115515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9333220934945347349641373 3499957850604505256115515)
      ·
        refine ⟨5249936775906757884173273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499957850604505256115515 5249936775906757884173273)
        ·
          refine ⟨3937452581930068413129955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5249936775906757884173273 3937452581930068413129955)
          ·
            refine ⟨5906178872895102619694933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937452581930068413129955 5906178872895102619694933)
            ·
              refine ⟨34606516833369741912275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5906178872895102619694933 34606516833369741912275)
              ·
                rfl

theorem cell19_341192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_341192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341192 prefixEnd_341192 := by exact prefixLift 341192
  have htrace : WordTrace (prefixWord ++ tailWord_341192) baseStart_341192 baseEnd_341192 := by
    simpa [prefixWord, tailWord_341192, baseEnd_341192] using wordTrace_append hprefix tailTrace_341192
  have hstable : (prefixWord ++ tailWord_341192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341192).length < 2 ^ (prefixWord ++ tailWord_341192).sum := by decide
  have hdescent : baseEnd_341192 < baseStart_341192 := by decide
  rcases family_descends (prefixWord ++ tailWord_341192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341249 : List Nat := [1, 2, 4, 1, 1, 10]
def baseStart_341249 : Nat := 118140960795 + 341249 * 2 ^ 59
def prefixEnd_341249 : Nat := 4983230072969 + 3 ^ 40 * 341249 * 2
def baseEnd_341249 : Nat := 11537432748394442496667

theorem tailTrace_341249 : CollatzResearch.WordTrace tailWord_341249 prefixEnd_341249 11537432748394442496667 := by
  unfold tailWord_341249
  simp only [CollatzResearch.WordTrace]
  refine ⟨12446373540720628534346801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8297582360480419022897867 12446373540720628534346801)
  ·
    refine ⟨9334780155540471400760101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12446373540720628534346801 9334780155540471400760101)
    ·
      refine ⟨1750271279163838387642519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9334780155540471400760101 1750271279163838387642519)
      ·
        refine ⟨2625406918745757581463779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750271279163838387642519 2625406918745757581463779)
        ·
          refine ⟨3938110378118636372195669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625406918745757581463779 3938110378118636372195669)
          ·
            refine ⟨11537432748394442496667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3938110378118636372195669 11537432748394442496667)
            ·
              rfl

theorem cell19_341249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 10].length) (baseStart_341249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341249 prefixEnd_341249 := by exact prefixLift 341249
  have htrace : WordTrace (prefixWord ++ tailWord_341249) baseStart_341249 baseEnd_341249 := by
    simpa [prefixWord, tailWord_341249, baseEnd_341249] using wordTrace_append hprefix tailTrace_341249
  have hstable : (prefixWord ++ tailWord_341249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341249).length < 2 ^ (prefixWord ++ tailWord_341249).sum := by decide
  have hdescent : baseEnd_341249 < baseStart_341249 := by decide
  rcases family_descends (prefixWord ++ tailWord_341249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341306 : List Nat := [3, 1, 1, 1, 4, 1, 8]
def baseStart_341306 : Nat := 118140960795 + 341306 * 2 ^ 59
def prefixEnd_341306 : Nat := 4983230072969 + 3 ^ 40 * 341306 * 2
def baseEnd_341306 : Nat := 34618079656996913067727

theorem tailTrace_341306 : CollatzResearch.WordTrace tailWord_341306 prefixEnd_341306 34618079656996913067727 := by
  unfold tailWord_341306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112113125378531817292943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8298968334342751512781181 3112113125378531817292943)
  ·
    refine ⟨4668169688067797725939415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3112113125378531817292943 4668169688067797725939415)
    ·
      refine ⟨7002254532101696588909123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4668169688067797725939415 7002254532101696588909123)
      ·
        refine ⟨10503381798152544883363685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7002254532101696588909123 10503381798152544883363685)
        ·
          refine ⟨1969384087153602165630691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10503381798152544883363685 1969384087153602165630691)
          ·
            refine ⟨2954076130730403248446037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969384087153602165630691 2954076130730403248446037)
            ·
              refine ⟨34618079656996913067727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2954076130730403248446037 34618079656996913067727)
              ·
                rfl

theorem cell19_341306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_341306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341306 prefixEnd_341306 := by exact prefixLift 341306
  have htrace : WordTrace (prefixWord ++ tailWord_341306) baseStart_341306 baseEnd_341306 := by
    simpa [prefixWord, tailWord_341306, baseEnd_341306] using wordTrace_append hprefix tailTrace_341306
  have hstable : (prefixWord ++ tailWord_341306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341306).length < 2 ^ (prefixWord ++ tailWord_341306).sum := by decide
  have hdescent : baseEnd_341306 < baseStart_341306 := by decide
  rcases family_descends (prefixWord ++ tailWord_341306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341378 : List Nat := [3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_341378 : Nat := 118140960795 + 341378 * 2 ^ 59
def prefixEnd_341378 : Nat := 4983230072969 + 3 ^ 40 * 341378 * 2
def baseEnd_341378 : Nat := 103876147478915905602985

theorem tailTrace_341378 : CollatzResearch.WordTrace tailWord_341378 prefixEnd_341378 103876147478915905602985 := by
  unfold tailWord_341378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112769639313320891448197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8300719038168855710528525 3112769639313320891448197)
  ·
    refine ⟨583644307371247667146537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3112769639313320891448197 583644307371247667146537)
    ·
      refine ⟨437733230528435750359903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 583644307371247667146537 437733230528435750359903)
      ·
        refine ⟨656599845792653625539855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437733230528435750359903 656599845792653625539855)
        ·
          refine ⟨984899768688980438309783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656599845792653625539855 984899768688980438309783)
          ·
            refine ⟨1477349653033470657464675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984899768688980438309783 1477349653033470657464675)
            ·
              refine ⟨2216024479550205986197013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477349653033470657464675 2216024479550205986197013)
              ·
                refine ⟨103876147478915905602985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2216024479550205986197013 103876147478915905602985)
                ·
                  rfl

theorem cell19_341378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_341378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341378 prefixEnd_341378 := by exact prefixLift 341378
  have htrace : WordTrace (prefixWord ++ tailWord_341378) baseStart_341378 baseEnd_341378 := by
    simpa [prefixWord, tailWord_341378, baseEnd_341378] using wordTrace_append hprefix tailTrace_341378
  have hstable : (prefixWord ++ tailWord_341378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341378).length < 2 ^ (prefixWord ++ tailWord_341378).sum := by decide
  have hdescent : baseEnd_341378 < baseStart_341378 := by decide
  rcases family_descends (prefixWord ++ tailWord_341378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341380 : List Nat := [2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_341380 : Nat := 118140960795 + 341380 * 2 ^ 59
def prefixEnd_341380 : Nat := 4983230072969 + 3 ^ 40 * 341380 * 2
def baseEnd_341380 : Nat := 103876756048580493558535

theorem tailTrace_341380 : CollatzResearch.WordTrace tailWord_341380 prefixEnd_341380 103876756048580493558535 := by
  unfold tailWord_341380
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225575751623018953682797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8300767668830691938243729 6225575751623018953682797)
  ·
    refine ⟨2334590906858632107631049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6225575751623018953682797 2334590906858632107631049)
    ·
      refine ⟨1750943180143974080723287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2334590906858632107631049 1750943180143974080723287)
      ·
        refine ⟨2626414770215961121084931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750943180143974080723287 2626414770215961121084931)
        ·
          refine ⟨3939622155323941681627397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626414770215961121084931 3939622155323941681627397)
          ·
            refine ⟨738679154123239065305137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3939622155323941681627397 738679154123239065305137)
            ·
              refine ⟨554009365592429298978853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738679154123239065305137 554009365592429298978853)
              ·
                refine ⟨103876756048580493558535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554009365592429298978853 103876756048580493558535)
                ·
                  rfl

theorem cell19_341380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_341380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341380 prefixEnd_341380 := by exact prefixLift 341380
  have htrace : WordTrace (prefixWord ++ tailWord_341380) baseStart_341380 baseEnd_341380 := by
    simpa [prefixWord, tailWord_341380, baseEnd_341380] using wordTrace_append hprefix tailTrace_341380
  have hstable : (prefixWord ++ tailWord_341380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341380).length < 2 ^ (prefixWord ++ tailWord_341380).sum := by decide
  have hdescent : baseEnd_341380 < baseStart_341380 := by decide
  rcases family_descends (prefixWord ++ tailWord_341380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
