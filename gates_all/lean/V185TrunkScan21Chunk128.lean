import V185TrunkScan21Chunk127

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1559132 : List Nat := [2, 2, 4, 1, 4, 1, 2, 5]
def baseStart_1559132 : Nat := 118140960795 + 1559132 * 2 ^ 59
def prefixEnd_1559132 : Nat := 4983230072969 + 3 ^ 40 * 1559132 * 2
def baseEnd_1559132 : Nat := 118605054786059129271065

theorem tailTrace_1559132 : CollatzResearch.WordTrace tailWord_1559132 prefixEnd_1559132 118605054786059129271065 := by
  unfold tailWord_1559132
  simp only [CollatzResearch.WordTrace]
  refine ⟨28433107893769258695595825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37910810525025678260794433 28433107893769258695595825)
  ·
    refine ⟨21324830920326944021696869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28433107893769258695595825 21324830920326944021696869)
    ·
      refine ⟨3998405797561302004068163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21324830920326944021696869 3998405797561302004068163)
      ·
        refine ⟨5997608696341953006102245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998405797561302004068163 5997608696341953006102245)
        ·
          refine ⟨1124551630564116188644171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5997608696341953006102245 1124551630564116188644171)
          ·
            refine ⟨1686827445846174282966257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124551630564116188644171 1686827445846174282966257)
            ·
              refine ⟨1265120584384630712224693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686827445846174282966257 1265120584384630712224693)
              ·
                refine ⟨118605054786059129271065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1265120584384630712224693 118605054786059129271065)
                ·
                  rfl

theorem cell21_1559132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_1559132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559132 prefixEnd_1559132 := by exact prefixLift 1559132
  have htrace : WordTrace (prefixWord ++ tailWord_1559132) baseStart_1559132 baseEnd_1559132 := by
    simpa [prefixWord, tailWord_1559132, baseEnd_1559132] using wordTrace_append hprefix tailTrace_1559132
  have hstable : (prefixWord ++ tailWord_1559132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559132).length < 2 ^ (prefixWord ++ tailWord_1559132).sum := by decide
  have hdescent : baseEnd_1559132 < baseStart_1559132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559219 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 4]
def baseStart_1559219 : Nat := 118140960795 + 1559219 * 2 ^ 59
def prefixEnd_1559219 : Nat := 4983230072969 + 3 ^ 40 * 1559219 * 2
def baseEnd_1559219 : Nat := 355835018943484569863017

theorem tailTrace_1559219 : CollatzResearch.WordTrace tailWord_1559219 prefixEnd_1559219 355835018943484569863017 := by
  unfold tailWord_1559219
  simp only [CollatzResearch.WordTrace]
  refine ⟨56869388938223331249608711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37912925958815554166405807 56869388938223331249608711)
  ·
    refine ⟨85304083407334996874413067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56869388938223331249608711 85304083407334996874413067)
    ·
      refine ⟨127956125111002495311619601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85304083407334996874413067 127956125111002495311619601)
      ·
        refine ⟨95967093833251871483714701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127956125111002495311619601 95967093833251871483714701)
        ·
          refine ⟨35987660187469451806393013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95967093833251871483714701 35987660187469451806393013)
          ·
            refine ⟨3373843142575261106849345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35987660187469451806393013 3373843142575261106849345)
            ·
              refine ⟨2530382356931445830137009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373843142575261106849345 2530382356931445830137009)
              ·
                refine ⟨1897786767698584372602757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2530382356931445830137009 1897786767698584372602757)
                ·
                  refine ⟨355835018943484569863017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1897786767698584372602757 355835018943484569863017)
                  ·
                    rfl

theorem cell21_1559219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 4].length) (baseStart_1559219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559219 prefixEnd_1559219 := by exact prefixLift 1559219
  have htrace : WordTrace (prefixWord ++ tailWord_1559219) baseStart_1559219 baseEnd_1559219 := by
    simpa [prefixWord, tailWord_1559219, baseEnd_1559219] using wordTrace_append hprefix tailTrace_1559219
  have hstable : (prefixWord ++ tailWord_1559219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559219).length < 2 ^ (prefixWord ++ tailWord_1559219).sum := by decide
  have hdescent : baseEnd_1559219 < baseStart_1559219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559368 : List Nat := [2, 1, 3, 1, 1, 3, 1, 9]
def baseStart_1559368 : Nat := 118140960795 + 1559368 * 2 ^ 59
def prefixEnd_1559368 : Nat := 4983230072969 + 3 ^ 40 * 1559368 * 2
def baseEnd_1559368 : Nat := 118623007591164473959793

theorem tailTrace_1559368 : CollatzResearch.WordTrace tailWord_1559368 prefixEnd_1559368 118623007591164473959793 := by
  unfold tailWord_1559368
  simp only [CollatzResearch.WordTrace]
  refine ⟨28437411707341764848391379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37916548943122353131188505 28437411707341764848391379)
  ·
    refine ⟨42656117561012647272587069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28437411707341764848391379 42656117561012647272587069)
    ·
      refine ⟨15996044085379742727220151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42656117561012647272587069 15996044085379742727220151)
      ·
        refine ⟨23994066128069614090830227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15996044085379742727220151 23994066128069614090830227)
        ·
          refine ⟨35991099192104421136245341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23994066128069614090830227 35991099192104421136245341)
          ·
            refine ⟨13496662197039157926092003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35991099192104421136245341 13496662197039157926092003)
            ·
              refine ⟨20244993295558736889138005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13496662197039157926092003 20244993295558736889138005)
              ·
                refine ⟨118623007591164473959793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20244993295558736889138005 118623007591164473959793)
                ·
                  rfl

theorem cell21_1559368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_1559368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559368 prefixEnd_1559368 := by exact prefixLift 1559368
  have htrace : WordTrace (prefixWord ++ tailWord_1559368) baseStart_1559368 baseEnd_1559368 := by
    simpa [prefixWord, tailWord_1559368, baseEnd_1559368] using wordTrace_append hprefix tailTrace_1559368
  have hstable : (prefixWord ++ tailWord_1559368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559368).length < 2 ^ (prefixWord ++ tailWord_1559368).sum := by decide
  have hdescent : baseEnd_1559368 < baseStart_1559368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559388 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_1559388 : Nat := 118140960795 + 1559388 * 2 ^ 59
def prefixEnd_1559388 : Nat := 4983230072969 + 3 ^ 40 * 1559388 * 2
def baseEnd_1559388 : Nat := 355873587045977831546005

theorem tailTrace_1559388 : CollatzResearch.WordTrace tailWord_1559388 prefixEnd_1559388 355873587045977831546005 := by
  unfold tailWord_1559388
  simp only [CollatzResearch.WordTrace]
  refine ⟨28437776437305536556255409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37917035249740715408340545 28437776437305536556255409)
  ·
    refine ⟨21328332327979152417191557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28437776437305536556255409 21328332327979152417191557)
    ·
      refine ⟨3999062311496091078223417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21328332327979152417191557 3999062311496091078223417)
      ·
        refine ⟨2999296733622068308667563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3999062311496091078223417 2999296733622068308667563)
        ·
          refine ⟨4498945100433102463001345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999296733622068308667563 4498945100433102463001345)
          ·
            refine ⟨3374208825324826847251009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4498945100433102463001345 3374208825324826847251009)
            ·
              refine ⟨2530656618993620135438257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3374208825324826847251009 2530656618993620135438257)
              ·
                refine ⟨1897992464245215101578693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2530656618993620135438257 1897992464245215101578693)
                ·
                  refine ⟨355873587045977831546005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1897992464245215101578693 355873587045977831546005)
                  ·
                    rfl

theorem cell21_1559388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_1559388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559388 prefixEnd_1559388 := by exact prefixLift 1559388
  have htrace : WordTrace (prefixWord ++ tailWord_1559388) baseStart_1559388 baseEnd_1559388 := by
    simpa [prefixWord, tailWord_1559388, baseEnd_1559388] using wordTrace_append hprefix tailTrace_1559388
  have hstable : (prefixWord ++ tailWord_1559388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559388).length < 2 ^ (prefixWord ++ tailWord_1559388).sum := by decide
  have hdescent : baseEnd_1559388 < baseStart_1559388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559433 : List Nat := [1, 2, 1, 1, 5, 3, 2, 3, 3]
def baseStart_1559433 : Nat := 118140960795 + 1559433 * 2 ^ 59
def prefixEnd_1559433 : Nat := 4983230072969 + 3 ^ 40 * 1559433 * 2
def baseEnd_1559433 : Nat := 355883856659067753295913

theorem tailTrace_1559433 : CollatzResearch.WordTrace tailWord_1559433 prefixEnd_1559433 355883856659067753295913 := by
  unfold tailWord_1559433
  simp only [CollatzResearch.WordTrace]
  refine ⟨56877194159448045797898953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37918129439632030531932635 56877194159448045797898953)
  ·
    refine ⟨42657895619586034348424215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56877194159448045797898953 42657895619586034348424215)
    ·
      refine ⟨63986843429379051522636323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42657895619586034348424215 63986843429379051522636323)
      ·
        refine ⟨95980265144068577283954485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63986843429379051522636323 95980265144068577283954485)
        ·
          refine ⟨8998149857256429120370733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95980265144068577283954485 8998149857256429120370733)
          ·
            refine ⟨3374306196471160920139025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8998149857256429120370733 3374306196471160920139025)
            ·
              refine ⟨2530729647353370690104269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3374306196471160920139025 2530729647353370690104269)
              ·
                refine ⟨949023617757514008789101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2530729647353370690104269 949023617757514008789101)
                ·
                  refine ⟨355883856659067753295913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949023617757514008789101 355883856659067753295913)
                  ·
                    rfl

theorem cell21_1559433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_1559433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559433 prefixEnd_1559433 := by exact prefixLift 1559433
  have htrace : WordTrace (prefixWord ++ tailWord_1559433) baseStart_1559433 baseEnd_1559433 := by
    simpa [prefixWord, tailWord_1559433, baseEnd_1559433] using wordTrace_append hprefix tailTrace_1559433
  have hstable : (prefixWord ++ tailWord_1559433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559433).length < 2 ^ (prefixWord ++ tailWord_1559433).sum := by decide
  have hdescent : baseEnd_1559433 < baseStart_1559433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559501 : List Nat := [1, 6, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1559501 : Nat := 118140960795 + 1559501 * 2 ^ 59
def prefixEnd_1559501 : Nat := 4983230072969 + 3 ^ 40 * 1559501 * 2
def baseEnd_1559501 : Nat := 355899375185514746162441

theorem tailTrace_1559501 : CollatzResearch.WordTrace tailWord_1559501 prefixEnd_1559501 355899375185514746162441 := by
  unfold tailWord_1559501
  simp only [CollatzResearch.WordTrace]
  refine ⟨56879674323201693411374357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37919782882134462274249571 56879674323201693411374357)
  ·
    refine ⟨2666234733900079378658173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56879674323201693411374357 2666234733900079378658173)
    ·
      refine ⟨999838025212529766996815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2666234733900079378658173 999838025212529766996815)
      ·
        refine ⟨1499757037818794650495223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999838025212529766996815 1499757037818794650495223)
        ·
          refine ⟨2249635556728191975742835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499757037818794650495223 2249635556728191975742835)
          ·
            refine ⟨3374453335092287963614253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2249635556728191975742835 3374453335092287963614253)
            ·
              refine ⟨1265420000659607986355345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3374453335092287963614253 1265420000659607986355345)
              ·
                refine ⟨949065000494705989766509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265420000659607986355345 949065000494705989766509)
                ·
                  refine ⟨355899375185514746162441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949065000494705989766509 355899375185514746162441)
                  ·
                    rfl

theorem cell21_1559501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1559501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559501 prefixEnd_1559501 := by exact prefixLift 1559501
  have htrace : WordTrace (prefixWord ++ tailWord_1559501) baseStart_1559501 baseEnd_1559501 := by
    simpa [prefixWord, tailWord_1559501, baseEnd_1559501] using wordTrace_append hprefix tailTrace_1559501
  have hstable : (prefixWord ++ tailWord_1559501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559501).length < 2 ^ (prefixWord ++ tailWord_1559501).sum := by decide
  have hdescent : baseEnd_1559501 < baseStart_1559501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559509 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 5]
def baseStart_1559509 : Nat := 118140960795 + 1559509 * 2 ^ 59
def prefixEnd_1559509 : Nat := 4983230072969 + 3 ^ 40 * 1559509 * 2
def baseEnd_1559509 : Nat := 355901200894508510029091

theorem tailTrace_1559509 : CollatzResearch.WordTrace tailWord_1559509 prefixEnd_1559509 355901200894508510029091 := by
  unfold tailWord_1559509
  simp only [CollatzResearch.WordTrace]
  refine ⟨56879966107172710777665581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37919977404781807185110387 56879966107172710777665581)
  ·
    refine ⟨21329987290189766541624593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56879966107172710777665581 21329987290189766541624593)
    ·
      refine ⟨15997490467642324906218445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21329987290189766541624593 15997490467642324906218445)
      ·
        refine ⟨5999058925365871839831917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15997490467642324906218445 5999058925365871839831917)
        ·
          refine ⟨2249647097012201939936969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5999058925365871839831917 2249647097012201939936969)
          ·
            refine ⟨1687235322759151454952727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2249647097012201939936969 1687235322759151454952727)
            ·
              refine ⟨2530852984138727182429091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687235322759151454952727 2530852984138727182429091)
              ·
                refine ⟨3796279476208090773643637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530852984138727182429091 3796279476208090773643637)
                ·
                  refine ⟨355901200894508510029091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3796279476208090773643637 355901200894508510029091)
                  ·
                    rfl

theorem cell21_1559509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_1559509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559509 prefixEnd_1559509 := by exact prefixLift 1559509
  have htrace : WordTrace (prefixWord ++ tailWord_1559509) baseStart_1559509 baseEnd_1559509 := by
    simpa [prefixWord, tailWord_1559509, baseEnd_1559509] using wordTrace_append hprefix tailTrace_1559509
  have hstable : (prefixWord ++ tailWord_1559509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559509).length < 2 ^ (prefixWord ++ tailWord_1559509).sum := by decide
  have hdescent : baseEnd_1559509 < baseStart_1559509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559554 : List Nat := [3, 4, 1, 3, 1, 9]
def baseStart_1559554 : Nat := 118140960795 + 1559554 * 2 ^ 59
def prefixEnd_1559554 : Nat := 4983230072969 + 3 ^ 40 * 1559554 * 2
def baseEnd_1559554 : Nat := 13181906315096238214037

theorem tailTrace_1559554 : CollatzResearch.WordTrace tailWord_1559554 prefixEnd_1559554 13181906315096238214037 := by
  unfold tailWord_1559554
  simp only [CollatzResearch.WordTrace]
  refine ⟨14220401848002420865763429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37921071594673122308702477 14220401848002420865763429)
  ·
    refine ⟨2666325346500453912330643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14220401848002420865763429 2666325346500453912330643)
    ·
      refine ⟨3999488019750680868495965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2666325346500453912330643 3999488019750680868495965)
      ·
        refine ⟨1499808007406505325685987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3999488019750680868495965 1499808007406505325685987)
        ·
          refine ⟨2249712011109757988528981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499808007406505325685987 2249712011109757988528981)
          ·
            refine ⟨13181906315096238214037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2249712011109757988528981 13181906315096238214037)
            ·
              rfl

theorem cell21_1559554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 9].length) (baseStart_1559554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559554 prefixEnd_1559554 := by exact prefixLift 1559554
  have htrace : WordTrace (prefixWord ++ tailWord_1559554) baseStart_1559554 baseEnd_1559554 := by
    simpa [prefixWord, tailWord_1559554, baseEnd_1559554] using wordTrace_append hprefix tailTrace_1559554
  have hstable : (prefixWord ++ tailWord_1559554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559554).length < 2 ^ (prefixWord ++ tailWord_1559554).sum := by decide
  have hdescent : baseEnd_1559554 < baseStart_1559554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559658 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_1559658 : Nat := 118140960795 + 1559658 * 2 ^ 59
def prefixEnd_1559658 : Nat := 4983230072969 + 3 ^ 40 * 1559658 * 2
def baseEnd_1559658 : Nat := 355935204724517362045453

theorem tailTrace_1559658 : CollatzResearch.WordTrace tailWord_1559658 prefixEnd_1559658 355935204724517362045453 := by
  unfold tailWord_1559658
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221350145908227306209907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37923600389088606149893085 14221350145908227306209907)
  ·
    refine ⟨21332025218862340959314861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14221350145908227306209907 21332025218862340959314861)
    ·
      refine ⟨7999509457073377859743073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21332025218862340959314861 7999509457073377859743073)
      ·
        refine ⟨5999632092805033394807305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7999509457073377859743073 5999632092805033394807305)
        ·
          refine ⟨4499724069603775046105479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5999632092805033394807305 4499724069603775046105479)
          ·
            refine ⟨6749586104405662569158219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499724069603775046105479 6749586104405662569158219)
            ·
              refine ⟨10124379156608493853737329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749586104405662569158219 10124379156608493853737329)
              ·
                refine ⟨7593284367456370390302997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10124379156608493853737329 7593284367456370390302997)
                ·
                  refine ⟨355935204724517362045453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7593284367456370390302997 355935204724517362045453)
                  ·
                    rfl

theorem cell21_1559658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_1559658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559658 prefixEnd_1559658 := by exact prefixLift 1559658
  have htrace : WordTrace (prefixWord ++ tailWord_1559658) baseStart_1559658 baseEnd_1559658 := by
    simpa [prefixWord, tailWord_1559658, baseEnd_1559658] using wordTrace_append hprefix tailTrace_1559658
  have hstable : (prefixWord ++ tailWord_1559658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559658).length < 2 ^ (prefixWord ++ tailWord_1559658).sum := by decide
  have hdescent : baseEnd_1559658 < baseStart_1559658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559661 : List Nat := [1, 5, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1559661 : Nat := 118140960795 + 1559661 * 2 ^ 59
def prefixEnd_1559661 : Nat := 4983230072969 + 3 ^ 40 * 1559661 * 2
def baseEnd_1559661 : Nat := 355935889365390023495447

theorem tailTrace_1559661 : CollatzResearch.WordTrace tailWord_1559661 prefixEnd_1559661 355935889365390023495447 := by
  unfold tailWord_1559661
  simp only [CollatzResearch.WordTrace]
  refine ⟨56885510002622040737198837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37923673335081360491465891 56885510002622040737198837)
  ·
    refine ⟨5333016562745816319112391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56885510002622040737198837 5333016562745816319112391)
    ·
      refine ⟨7999524844118724478668587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5333016562745816319112391 7999524844118724478668587)
      ·
        refine ⟨11999287266178086718002881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7999524844118724478668587 11999287266178086718002881)
        ·
          refine ⟨8999465449633565038502161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11999287266178086718002881 8999465449633565038502161)
          ·
            refine ⟨6749599087225173778876621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8999465449633565038502161 6749599087225173778876621)
            ·
              refine ⟨2531099657709440167078733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6749599087225173778876621 2531099657709440167078733)
              ·
                refine ⟨949162371641040062654525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2531099657709440167078733 949162371641040062654525)
                ·
                  refine ⟨355935889365390023495447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949162371641040062654525 355935889365390023495447)
                  ·
                    rfl

theorem cell21_1559661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1559661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559661 prefixEnd_1559661 := by exact prefixLift 1559661
  have htrace : WordTrace (prefixWord ++ tailWord_1559661) baseStart_1559661 baseEnd_1559661 := by
    simpa [prefixWord, tailWord_1559661, baseEnd_1559661] using wordTrace_append hprefix tailTrace_1559661
  have hstable : (prefixWord ++ tailWord_1559661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559661).length < 2 ^ (prefixWord ++ tailWord_1559661).sum := by decide
  have hdescent : baseEnd_1559661 < baseStart_1559661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559737 : List Nat := [1, 2, 1, 4, 1, 3, 4, 2, 3]
def baseStart_1559737 : Nat := 118140960795 + 1559737 * 2 ^ 59
def prefixEnd_1559737 : Nat := 4983230072969 + 3 ^ 40 * 1559737 * 2
def baseEnd_1559737 : Nat := 355953233600830780228625

theorem tailTrace_1559737 : CollatzResearch.WordTrace tailWord_1559737 prefixEnd_1559737 355953233600830780228625 := by
  unfold tailWord_1559737
  simp only [CollatzResearch.WordTrace]
  refine ⟨56888281950346705716965465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37925521300231137144643643 56888281950346705716965465)
  ·
    refine ⟨42666211462760029287724099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56888281950346705716965465 42666211462760029287724099)
    ·
      refine ⟨63999317194140043931586149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42666211462760029287724099 63999317194140043931586149)
      ·
        refine ⟨11999871973901258237172403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63999317194140043931586149 11999871973901258237172403)
        ·
          refine ⟨17999807960851887355758605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11999871973901258237172403 17999807960851887355758605)
          ·
            refine ⟨6749927985319457758409477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17999807960851887355758605 6749927985319457758409477)
            ·
              refine ⟨1265611497247398329701777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6749927985319457758409477 1265611497247398329701777)
              ·
                refine ⟨949208622935548747276333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265611497247398329701777 949208622935548747276333)
                ·
                  refine ⟨355953233600830780228625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949208622935548747276333 355953233600830780228625)
                  ·
                    rfl

theorem cell21_1559737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_1559737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559737 prefixEnd_1559737 := by exact prefixLift 1559737
  have htrace : WordTrace (prefixWord ++ tailWord_1559737) baseStart_1559737 baseEnd_1559737 := by
    simpa [prefixWord, tailWord_1559737, baseEnd_1559737] using wordTrace_append hprefix tailTrace_1559737
  have hstable : (prefixWord ++ tailWord_1559737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559737).length < 2 ^ (prefixWord ++ tailWord_1559737).sum := by decide
  have hdescent : baseEnd_1559737 < baseStart_1559737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559917 : List Nat := [1, 5, 1, 1, 1, 5, 1, 6]
def baseStart_1559917 : Nat := 118140960795 + 1559917 * 2 ^ 59
def prefixEnd_1559917 : Nat := 4983230072969 + 3 ^ 40 * 1559917 * 2
def baseEnd_1559917 : Nat := 118664770684396822409419

theorem tailTrace_1559917 : CollatzResearch.WordTrace tailWord_1559917 prefixEnd_1559917 118664770684396822409419 := by
  unfold tailWord_1559917
  simp only [CollatzResearch.WordTrace]
  refine ⟨56894847089694596458518005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37929898059796397639012003 56894847089694596458518005)
  ·
    refine ⟨5333891914658868417986063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56894847089694596458518005 5333891914658868417986063)
    ·
      refine ⟨8000837871988302626979095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5333891914658868417986063 8000837871988302626979095)
      ·
        refine ⟨12001256807982453940468643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000837871988302626979095 12001256807982453940468643)
        ·
          refine ⟨18001885211973680910702965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12001256807982453940468643 18001885211973680910702965)
          ·
            refine ⟨1687676738622532585378403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18001885211973680910702965 1687676738622532585378403)
            ·
              refine ⟨2531515107933798878067605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687676738622532585378403 2531515107933798878067605)
              ·
                refine ⟨118664770684396822409419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2531515107933798878067605 118664770684396822409419)
                ·
                  rfl

theorem cell21_1559917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 6].length) (baseStart_1559917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559917 prefixEnd_1559917 := by exact prefixLift 1559917
  have htrace : WordTrace (prefixWord ++ tailWord_1559917) baseStart_1559917 baseEnd_1559917 := by
    simpa [prefixWord, tailWord_1559917, baseEnd_1559917] using wordTrace_append hprefix tailTrace_1559917
  have hstable : (prefixWord ++ tailWord_1559917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559917).length < 2 ^ (prefixWord ++ tailWord_1559917).sum := by decide
  have hdescent : baseEnd_1559917 < baseStart_1559917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1559948 : List Nat := [2, 2, 1, 2, 1, 3, 4, 3, 3]
def baseStart_1559948 : Nat := 118140960795 + 1559948 * 2 ^ 59
def prefixEnd_1559948 : Nat := 4983230072969 + 3 ^ 40 * 1559948 * 2
def baseEnd_1559948 : Nat := 356001386675541302211527

theorem tailTrace_1559948 : CollatzResearch.WordTrace tailWord_1559948 prefixEnd_1559948 356001386675541302211527 := by
  unfold tailWord_1559948
  simp only [CollatzResearch.WordTrace]
  refine ⟨28447988876291144376448249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37930651835054859168597665 28447988876291144376448249)
  ·
    refine ⟨21335991657218358282336187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28447988876291144376448249 21335991657218358282336187)
    ·
      refine ⟨32003987485827537423504281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21335991657218358282336187 32003987485827537423504281)
      ·
        refine ⟨24002990614370653067628211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32003987485827537423504281 24002990614370653067628211)
        ·
          refine ⟨36004485921555979601442317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24002990614370653067628211 36004485921555979601442317)
          ·
            refine ⟨13501682220583492350540869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36004485921555979601442317 13501682220583492350540869)
            ·
              refine ⟨2531565416359404815726413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13501682220583492350540869 2531565416359404815726413)
              ·
                refine ⟨949337031134776805897405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2531565416359404815726413 949337031134776805897405)
                ·
                  refine ⟨356001386675541302211527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949337031134776805897405 356001386675541302211527)
                  ·
                    rfl

theorem cell21_1559948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_1559948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1559948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1559948 prefixEnd_1559948 := by exact prefixLift 1559948
  have htrace : WordTrace (prefixWord ++ tailWord_1559948) baseStart_1559948 baseEnd_1559948 := by
    simpa [prefixWord, tailWord_1559948, baseEnd_1559948] using wordTrace_append hprefix tailTrace_1559948
  have hstable : (prefixWord ++ tailWord_1559948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1559948).length < 2 ^ (prefixWord ++ tailWord_1559948).sum := by decide
  have hdescent : baseEnd_1559948 < baseStart_1559948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1559948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560021 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 6]
def baseStart_1560021 : Nat := 118140960795 + 1560021 * 2 ^ 59
def prefixEnd_1560021 : Nat := 4983230072969 + 3 ^ 40 * 1560021 * 2
def baseEnd_1560021 : Nat := 356018046270109397494711

theorem tailTrace_1560021 : CollatzResearch.WordTrace tailWord_1560021 prefixEnd_1560021 356018046270109397494711 := by
  unfold tailWord_1560021
  simp only [CollatzResearch.WordTrace]
  refine ⟨56898640281317822220303917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37932426854211881480202611 56898640281317822220303917)
  ·
    refine ⟨21336990105494183332613969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56898640281317822220303917 21336990105494183332613969)
    ·
      refine ⟨16002742579120637499460477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21336990105494183332613969 16002742579120637499460477)
      ·
        refine ⟨6001028467170239062297679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16002742579120637499460477 6001028467170239062297679)
        ·
          refine ⟨9001542700755358593446519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001028467170239062297679 9001542700755358593446519)
          ·
            refine ⟨13502314051133037890169779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9001542700755358593446519 13502314051133037890169779)
            ·
              refine ⟨20253471076699556835254669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13502314051133037890169779 20253471076699556835254669)
              ·
                refine ⟨7595051653762333813220501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20253471076699556835254669 7595051653762333813220501)
                ·
                  refine ⟨356018046270109397494711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7595051653762333813220501 356018046270109397494711)
                  ·
                    rfl

theorem cell21_1560021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_1560021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560021 prefixEnd_1560021 := by exact prefixLift 1560021
  have htrace : WordTrace (prefixWord ++ tailWord_1560021) baseStart_1560021 baseEnd_1560021 := by
    simpa [prefixWord, tailWord_1560021, baseEnd_1560021] using wordTrace_append hprefix tailTrace_1560021
  have hstable : (prefixWord ++ tailWord_1560021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560021).length < 2 ^ (prefixWord ++ tailWord_1560021).sum := by decide
  have hdescent : baseEnd_1560021 < baseStart_1560021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560176 : List Nat := [2, 1, 1, 1, 6, 1, 3, 3, 3]
def baseStart_1560176 : Nat := 118140960795 + 1560176 * 2 ^ 59
def prefixEnd_1560176 : Nat := 4983230072969 + 3 ^ 40 * 1560176 * 2
def baseEnd_1560176 : Nat := 356053419381863572411061

theorem tailTrace_1560176 : CollatzResearch.WordTrace tailWord_1560176 prefixEnd_1560176 356053419381863572411061 := by
  unfold tailWord_1560176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28452146797878141846098191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37936195730504189128130921 28452146797878141846098191)
  ·
    refine ⟨42678220196817212769147287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28452146797878141846098191 42678220196817212769147287)
    ·
      refine ⟨64017330295225819153720931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42678220196817212769147287 64017330295225819153720931)
      ·
        refine ⟨96025995442838728730581397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64017330295225819153720931 96025995442838728730581397)
        ·
          refine ⟨4501218536383065409246003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96025995442838728730581397 4501218536383065409246003)
          ·
            refine ⟨6751827804574598113869005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4501218536383065409246003 6751827804574598113869005)
            ·
              refine ⟨2531935426715474292700877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6751827804574598113869005 2531935426715474292700877)
              ·
                refine ⟨949475785018302859762829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2531935426715474292700877 949475785018302859762829)
                ·
                  refine ⟨356053419381863572411061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949475785018302859762829 356053419381863572411061)
                  ·
                    rfl

theorem cell21_1560176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_1560176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560176 prefixEnd_1560176 := by exact prefixLift 1560176
  have htrace : WordTrace (prefixWord ++ tailWord_1560176) baseStart_1560176 baseEnd_1560176 := by
    simpa [prefixWord, tailWord_1560176, baseEnd_1560176] using wordTrace_append hprefix tailTrace_1560176
  have hstable : (prefixWord ++ tailWord_1560176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560176).length < 2 ^ (prefixWord ++ tailWord_1560176).sum := by decide
  have hdescent : baseEnd_1560176 < baseStart_1560176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560193 : List Nat := [1, 2, 4, 2, 1, 3, 3, 2, 3]
def baseStart_1560193 : Nat := 118140960795 + 1560193 * 2 ^ 59
def prefixEnd_1560193 : Nat := 4983230072969 + 3 ^ 40 * 1560193 * 2
def baseEnd_1560193 : Nat := 356057299013475320627693

theorem tailTrace_1560193 : CollatzResearch.WordTrace tailWord_1560193 prefixEnd_1560193 356057299013475320627693 := by
  unfold tailWord_1560193
  simp only [CollatzResearch.WordTrace]
  refine ⟨56904913636694695595565233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37936609091129797063710155 56904913636694695595565233)
  ·
    refine ⟨42678685227521021696673925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56904913636694695595565233 42678685227521021696673925)
    ·
      refine ⟨8002253480160191568126361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42678685227521021696673925 8002253480160191568126361)
      ·
        refine ⟨6001690110120143676094771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8002253480160191568126361 6001690110120143676094771)
        ·
          refine ⟨9002535165180215514142157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001690110120143676094771 9002535165180215514142157)
          ·
            refine ⟨3375950686942580817803309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9002535165180215514142157 3375950686942580817803309)
            ·
              refine ⟨1265981507603467806676241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3375950686942580817803309 1265981507603467806676241)
              ·
                refine ⟨949486130702600855007181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265981507603467806676241 949486130702600855007181)
                ·
                  refine ⟨356057299013475320627693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949486130702600855007181 356057299013475320627693)
                  ·
                    rfl

theorem cell21_1560193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_1560193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560193 prefixEnd_1560193 := by exact prefixLift 1560193
  have htrace : WordTrace (prefixWord ++ tailWord_1560193) baseStart_1560193 baseEnd_1560193 := by
    simpa [prefixWord, tailWord_1560193, baseEnd_1560193] using wordTrace_append hprefix tailTrace_1560193
  have hstable : (prefixWord ++ tailWord_1560193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560193).length < 2 ^ (prefixWord ++ tailWord_1560193).sum := by decide
  have hdescent : baseEnd_1560193 < baseStart_1560193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560249 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 4]
def baseStart_1560249 : Nat := 118140960795 + 1560249 * 2 ^ 59
def prefixEnd_1560249 : Nat := 4983230072969 + 3 ^ 40 * 1560249 * 2
def baseEnd_1560249 : Nat := 356070078976431667694245

theorem tailTrace_1560249 : CollatzResearch.WordTrace tailWord_1560249 prefixEnd_1560249 356070078976431667694245 := by
  unfold tailWord_1560249
  simp only [CollatzResearch.WordTrace]
  refine ⟨56906956124491817159603801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37937970749661211439735867 56906956124491817159603801)
  ·
    refine ⟨42680217093368862869702851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56906956124491817159603801 42680217093368862869702851)
    ·
      refine ⟨64020325640053294304554277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42680217093368862869702851 64020325640053294304554277)
      ·
        refine ⟨12003811057509992682103927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64020325640053294304554277 12003811057509992682103927)
        ·
          refine ⟨18005716586264989023155891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12003811057509992682103927 18005716586264989023155891)
          ·
            refine ⟨27008574879397483534733837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18005716586264989023155891 27008574879397483534733837)
            ·
              refine ⟨10128215579774056325525189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27008574879397483534733837 10128215579774056325525189)
              ·
                refine ⟨1899040421207635561035973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10128215579774056325525189 1899040421207635561035973)
                ·
                  refine ⟨356070078976431667694245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1899040421207635561035973 356070078976431667694245)
                  ·
                    rfl

theorem cell21_1560249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_1560249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560249 prefixEnd_1560249 := by exact prefixLift 1560249
  have htrace : WordTrace (prefixWord ++ tailWord_1560249) baseStart_1560249 baseEnd_1560249 := by
    simpa [prefixWord, tailWord_1560249, baseEnd_1560249] using wordTrace_append hprefix tailTrace_1560249
  have hstable : (prefixWord ++ tailWord_1560249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560249).length < 2 ^ (prefixWord ++ tailWord_1560249).sum := by decide
  have hdescent : baseEnd_1560249 < baseStart_1560249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560252 : List Nat := [2, 2, 2, 3, 1, 3, 1, 4, 3]
def baseStart_1560252 : Nat := 118140960795 + 1560252 * 2 ^ 59
def prefixEnd_1560252 : Nat := 4983230072969 + 3 ^ 40 * 1560252 * 2
def baseEnd_1560252 : Nat := 356070763617304329144239

theorem tailTrace_1560252 : CollatzResearch.WordTrace tailWord_1560252 prefixEnd_1560252 356070763617304329144239 := by
  unfold tailWord_1560252
  simp only [CollatzResearch.WordTrace]
  refine ⟨28453532771740474335981505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37938043695653965781308673 28453532771740474335981505)
  ·
    refine ⟨21340149578805355751986129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28453532771740474335981505 21340149578805355751986129)
    ·
      refine ⟨16005112184104016813989597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21340149578805355751986129 16005112184104016813989597)
      ·
        refine ⟨6001917069039006305246099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16005112184104016813989597 6001917069039006305246099)
        ·
          refine ⟨9002875603558509457869149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001917069039006305246099 9002875603558509457869149)
          ·
            refine ⟨3376078351334441046700931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9002875603558509457869149 3376078351334441046700931)
            ·
              refine ⟨5064117527001661570051397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376078351334441046700931 5064117527001661570051397)
              ·
                refine ⟨949522036312811544384637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5064117527001661570051397 949522036312811544384637)
                ·
                  refine ⟨356070763617304329144239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949522036312811544384637 356070763617304329144239)
                  ·
                    rfl

theorem cell21_1560252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_1560252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560252 prefixEnd_1560252 := by exact prefixLift 1560252
  have htrace : WordTrace (prefixWord ++ tailWord_1560252) baseStart_1560252 baseEnd_1560252 := by
    simpa [prefixWord, tailWord_1560252, baseEnd_1560252] using wordTrace_append hprefix tailTrace_1560252
  have hstable : (prefixWord ++ tailWord_1560252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560252).length < 2 ^ (prefixWord ++ tailWord_1560252).sum := by decide
  have hdescent : baseEnd_1560252 < baseStart_1560252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560280 : List Nat := [2, 1, 2, 2, 3, 1, 5, 5]
def baseStart_1560280 : Nat := 118140960795 + 1560280 * 2 ^ 59
def prefixEnd_1560280 : Nat := 4983230072969 + 3 ^ 40 * 1560280 * 2
def baseEnd_1560280 : Nat := 118692384532927500892505

theorem tailTrace_1560280 : CollatzResearch.WordTrace tailWord_1560280 prefixEnd_1560280 118692384532927500892505 := by
  unfold tailWord_1560280
  simp only [CollatzResearch.WordTrace]
  refine ⟨28454043393689754726991147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37938724524919672969321529 28454043393689754726991147)
  ·
    refine ⟨42681065090534632090486721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28454043393689754726991147 42681065090534632090486721)
    ·
      refine ⟨32010798817900974067865041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42681065090534632090486721 32010798817900974067865041)
      ·
        refine ⟨24008099113425730550898781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32010798817900974067865041 24008099113425730550898781)
        ·
          refine ⟨9003037167534648956587043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24008099113425730550898781 9003037167534648956587043)
          ·
            refine ⟨13504555751301973434880565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003037167534648956587043 13504555751301973434880565)
            ·
              refine ⟨1266052101684560009520053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13504555751301973434880565 1266052101684560009520053)
              ·
                refine ⟨118692384532927500892505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1266052101684560009520053 118692384532927500892505)
                ·
                  rfl

theorem cell21_1560280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_1560280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560280 prefixEnd_1560280 := by exact prefixLift 1560280
  have htrace : WordTrace (prefixWord ++ tailWord_1560280) baseStart_1560280 baseEnd_1560280 := by
    simpa [prefixWord, tailWord_1560280, baseEnd_1560280] using wordTrace_append hprefix tailTrace_1560280
  have hstable : (prefixWord ++ tailWord_1560280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560280).length < 2 ^ (prefixWord ++ tailWord_1560280).sum := by decide
  have hdescent : baseEnd_1560280 < baseStart_1560280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560311 : List Nat := [1, 1, 3, 1, 1, 1, 6, 4, 3]
def baseStart_1560311 : Nat := 118140960795 + 1560311 * 2 ^ 59
def prefixEnd_1560311 : Nat := 4983230072969 + 3 ^ 40 * 1560311 * 2
def baseEnd_1560311 : Nat := 356084228221133337660785

theorem tailTrace_1560311 : CollatzResearch.WordTrace tailWord_1560311 prefixEnd_1560311 356084228221133337660785 := by
  unfold tailWord_1560311
  simp only [CollatzResearch.WordTrace]
  refine ⟨56909217450267201748360787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37939478300178134498907191 56909217450267201748360787)
  ·
    refine ⟨85363826175400802622541181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56909217450267201748360787 85363826175400802622541181)
    ·
      refine ⟨32011434815775300983452943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85363826175400802622541181 32011434815775300983452943)
      ·
        refine ⟨48017152223662951475179415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32011434815775300983452943 48017152223662951475179415)
        ·
          refine ⟨72025728335494427212769123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48017152223662951475179415 72025728335494427212769123)
          ·
            refine ⟨108038592503241640819153685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72025728335494427212769123 108038592503241640819153685)
            ·
              refine ⟨5064309023589451913397829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108038592503241640819153685 5064309023589451913397829)
              ·
                refine ⟨949557941923022233762093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5064309023589451913397829 949557941923022233762093)
                ·
                  refine ⟨356084228221133337660785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949557941923022233762093 356084228221133337660785)
                  ·
                    rfl

theorem cell21_1560311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 3].length) (baseStart_1560311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560311 prefixEnd_1560311 := by exact prefixLift 1560311
  have htrace : WordTrace (prefixWord ++ tailWord_1560311) baseStart_1560311 baseEnd_1560311 := by
    simpa [prefixWord, tailWord_1560311, baseEnd_1560311] using wordTrace_append hprefix tailTrace_1560311
  have hstable : (prefixWord ++ tailWord_1560311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560311).length < 2 ^ (prefixWord ++ tailWord_1560311).sum := by decide
  have hdescent : baseEnd_1560311 < baseStart_1560311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560356 : List Nat := [2, 3, 1, 3, 2, 3, 7]
def baseStart_1560356 : Nat := 118140960795 + 1560356 * 2 ^ 59
def prefixEnd_1560356 : Nat := 4983230072969 + 3 ^ 40 * 1560356 * 2
def baseEnd_1560356 : Nat := 39566055314913695490077

theorem tailTrace_1560356 : CollatzResearch.WordTrace tailWord_1560356 prefixEnd_1560356 39566055314913695490077 := by
  unfold tailWord_1560356
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455429367552087216874461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37940572490069449622499281 28455429367552087216874461)
  ·
    refine ⟨10670786012832032706327923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28455429367552087216874461 10670786012832032706327923)
    ·
      refine ⟨16006179019248049059491885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10670786012832032706327923 16006179019248049059491885)
      ·
        refine ⟨6002317132218018397309457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16006179019248049059491885 6002317132218018397309457)
        ·
          refine ⟨4501737849163513797982093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6002317132218018397309457 4501737849163513797982093)
          ·
            refine ⟨1688151693436317674243285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4501737849163513797982093 1688151693436317674243285)
            ·
              refine ⟨39566055314913695490077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1688151693436317674243285 39566055314913695490077)
              ·
                rfl

theorem cell21_1560356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 7].length) (baseStart_1560356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560356 prefixEnd_1560356 := by exact prefixLift 1560356
  have htrace : WordTrace (prefixWord ++ tailWord_1560356) baseStart_1560356 baseEnd_1560356 := by
    simpa [prefixWord, tailWord_1560356, baseEnd_1560356] using wordTrace_append hprefix tailTrace_1560356
  have hstable : (prefixWord ++ tailWord_1560356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560356).length < 2 ^ (prefixWord ++ tailWord_1560356).sum := by decide
  have hdescent : baseEnd_1560356 < baseStart_1560356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560418 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1560418 : Nat := 118140960795 + 1560418 * 2 ^ 59
def prefixEnd_1560418 : Nat := 4983230072969 + 3 ^ 40 * 1560418 * 2
def baseEnd_1560418 : Nat := 356108647078924929377233

theorem tailTrace_1560418 : CollatzResearch.WordTrace tailWord_1560418 prefixEnd_1560418 356108647078924929377233 := by
  unfold tailWord_1560418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14228280015219889755626477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37942080040586372681670605 14228280015219889755626477)
  ·
    refine ⟨5335605005707458658359929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14228280015219889755626477 5335605005707458658359929)
    ·
      refine ⟨4001703754280593993769947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5335605005707458658359929 4001703754280593993769947)
      ·
        refine ⟨6002555631420890990654921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001703754280593993769947 6002555631420890990654921)
        ·
          refine ⟨4501916723565668242991191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6002555631420890990654921 4501916723565668242991191)
          ·
            refine ⟨6752875085348502364486787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4501916723565668242991191 6752875085348502364486787)
            ·
              refine ⟨10129312628022753546730181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752875085348502364486787 10129312628022753546730181)
              ·
                refine ⟨1899246117754266290011909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10129312628022753546730181 1899246117754266290011909)
                ·
                  refine ⟨356108647078924929377233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1899246117754266290011909 356108647078924929377233)
                  ·
                    rfl

theorem cell21_1560418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1560418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560418 prefixEnd_1560418 := by exact prefixLift 1560418
  have htrace : WordTrace (prefixWord ++ tailWord_1560418) baseStart_1560418 baseEnd_1560418 := by
    simpa [prefixWord, tailWord_1560418, baseEnd_1560418] using wordTrace_append hprefix tailTrace_1560418
  have hstable : (prefixWord ++ tailWord_1560418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560418).length < 2 ^ (prefixWord ++ tailWord_1560418).sum := by decide
  have hdescent : baseEnd_1560418 < baseStart_1560418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560460 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_1560460 : Nat := 118140960795 + 1560460 * 2 ^ 59
def prefixEnd_1560460 : Nat := 4983230072969 + 3 ^ 40 * 1560460 * 2
def baseEnd_1560460 : Nat := 356118232051142189677147

theorem tailTrace_1560460 : CollatzResearch.WordTrace tailWord_1560460 prefixEnd_1560460 356118232051142189677147 := by
  unfold tailWord_1560460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28457325963363700097767417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37943101284484933463689889 28457325963363700097767417)
  ·
    refine ⟨21342994472522775073325563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28457325963363700097767417 21342994472522775073325563)
    ·
      refine ⟨32014491708784162609988345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21342994472522775073325563 32014491708784162609988345)
      ·
        refine ⟨24010868781588121957491259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32014491708784162609988345 24010868781588121957491259)
        ·
          refine ⟨36016303172382182936236889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24010868781588121957491259 36016303172382182936236889)
          ·
            refine ⟨27012227379286637202177667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36016303172382182936236889 27012227379286637202177667)
            ·
              refine ⟨40518341068929955803266501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27012227379286637202177667 40518341068929955803266501)
              ·
                refine ⟨7597188950424366713112469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40518341068929955803266501 7597188950424366713112469)
                ·
                  refine ⟨356118232051142189677147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7597188950424366713112469 356118232051142189677147)
                  ·
                    rfl

theorem cell21_1560460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_1560460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560460 prefixEnd_1560460 := by exact prefixLift 1560460
  have htrace : WordTrace (prefixWord ++ tailWord_1560460) baseStart_1560460 baseEnd_1560460 := by
    simpa [prefixWord, tailWord_1560460, baseEnd_1560460] using wordTrace_append hprefix tailTrace_1560460
  have hstable : (prefixWord ++ tailWord_1560460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560460).length < 2 ^ (prefixWord ++ tailWord_1560460).sum := by decide
  have hdescent : baseEnd_1560460 < baseStart_1560460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560477 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1560477 : Nat := 118140960795 + 1560477 * 2 ^ 59
def prefixEnd_1560477 : Nat := 4983230072969 + 3 ^ 40 * 1560477 * 2
def baseEnd_1560477 : Nat := 356122111682753937893779

theorem tailTrace_1560477 : CollatzResearch.WordTrace tailWord_1560477 prefixEnd_1560477 356122111682753937893779 := by
  unfold tailWord_1560477
  simp only [CollatzResearch.WordTrace]
  refine ⟨56915271967665812098903685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37943514645110541399269123 56915271967665812098903685)
  ·
    refine ⟨10671613493937339768544441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56915271967665812098903685 10671613493937339768544441)
    ·
      refine ⟨8003710120453004826408331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10671613493937339768544441 8003710120453004826408331)
      ·
        refine ⟨12005565180679507239612497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8003710120453004826408331 12005565180679507239612497)
        ·
          refine ⟨9004173885509630429709373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12005565180679507239612497 9004173885509630429709373)
          ·
            refine ⟨3376565207066111411141015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9004173885509630429709373 3376565207066111411141015)
            ·
              refine ⟨5064847810599167116711523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376565207066111411141015 5064847810599167116711523)
              ·
                refine ⟨7597271715898750675067285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064847810599167116711523 7597271715898750675067285)
                ·
                  refine ⟨356122111682753937893779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7597271715898750675067285 356122111682753937893779)
                  ·
                    rfl

theorem cell21_1560477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1560477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560477 prefixEnd_1560477 := by exact prefixLift 1560477
  have htrace : WordTrace (prefixWord ++ tailWord_1560477) baseStart_1560477 baseEnd_1560477 := by
    simpa [prefixWord, tailWord_1560477, baseEnd_1560477] using wordTrace_append hprefix tailTrace_1560477
  have hstable : (prefixWord ++ tailWord_1560477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560477).length < 2 ^ (prefixWord ++ tailWord_1560477).sum := by decide
  have hdescent : baseEnd_1560477 < baseStart_1560477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560536 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_1560536 : Nat := 118140960795 + 1560536 * 2 ^ 59
def prefixEnd_1560536 : Nat := 4983230072969 + 3 ^ 40 * 1560536 * 2
def baseEnd_1560536 : Nat := 356135576286582946410325

theorem tailTrace_1560536 : CollatzResearch.WordTrace tailWord_1560536 prefixEnd_1560536 356135576286582946410325 := by
  unfold tailWord_1560536
  simp only [CollatzResearch.WordTrace]
  refine ⟨28458711937226032587650731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37944949249634710116867641 28458711937226032587650731)
  ·
    refine ⟨42688067905839048881476097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28458711937226032587650731 42688067905839048881476097)
    ·
      refine ⟨32016050929379286661107073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42688067905839048881476097 32016050929379286661107073)
      ·
        refine ⟨24012038197034464995830305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32016050929379286661107073 24012038197034464995830305)
        ·
          refine ⟨18009028647775848746872729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24012038197034464995830305 18009028647775848746872729)
          ·
            refine ⟨13506771485831886560154547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18009028647775848746872729 13506771485831886560154547)
            ·
              refine ⟨20260157228747829840231821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13506771485831886560154547 20260157228747829840231821)
              ·
                refine ⟨7597558960780436190086933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20260157228747829840231821 7597558960780436190086933)
                ·
                  refine ⟨356135576286582946410325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7597558960780436190086933 356135576286582946410325)
                  ·
                    rfl

theorem cell21_1560536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_1560536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560536 prefixEnd_1560536 := by exact prefixLift 1560536
  have htrace : WordTrace (prefixWord ++ tailWord_1560536) baseStart_1560536 baseEnd_1560536 := by
    simpa [prefixWord, tailWord_1560536, baseEnd_1560536] using wordTrace_append hprefix tailTrace_1560536
  have hstable : (prefixWord ++ tailWord_1560536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560536).length < 2 ^ (prefixWord ++ tailWord_1560536).sum := by decide
  have hdescent : baseEnd_1560536 < baseStart_1560536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560632 : List Nat := [2, 1, 2, 1, 6, 1, 2, 3, 3]
def baseStart_1560632 : Nat := 118140960795 + 1560632 * 2 ^ 59
def prefixEnd_1560632 : Nat := 4983230072969 + 3 ^ 40 * 1560632 * 2
def baseEnd_1560632 : Nat := 356157484794508112810129

theorem tailTrace_1560632 : CollatzResearch.WordTrace tailWord_1560632 prefixEnd_1560632 356157484794508112810129 := by
  unfold tailWord_1560632
  simp only [CollatzResearch.WordTrace]
  refine ⟨28460462641052136785398075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37947283521402849047197433 28460462641052136785398075)
  ·
    refine ⟨42690693961578205178097113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28460462641052136785398075 42690693961578205178097113)
    ·
      refine ⟨32018020471183653883572835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42690693961578205178097113 32018020471183653883572835)
      ·
        refine ⟨48027030706775480825359253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32018020471183653883572835 48027030706775480825359253)
        ·
          refine ⟨2251267064380100663688715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48027030706775480825359253 2251267064380100663688715)
          ·
            refine ⟨3376900596570150995533073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251267064380100663688715 3376900596570150995533073)
            ·
              refine ⟨2532675447427613246649805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376900596570150995533073 2532675447427613246649805)
              ·
                refine ⟨949753292785354967493677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2532675447427613246649805 949753292785354967493677)
                ·
                  refine ⟨356157484794508112810129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949753292785354967493677 356157484794508112810129)
                  ·
                    rfl

theorem cell21_1560632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_1560632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560632 prefixEnd_1560632 := by exact prefixLift 1560632
  have htrace : WordTrace (prefixWord ++ tailWord_1560632) baseStart_1560632 baseEnd_1560632 := by
    simpa [prefixWord, tailWord_1560632, baseEnd_1560632] using wordTrace_append hprefix tailTrace_1560632
  have hstable : (prefixWord ++ tailWord_1560632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560632).length < 2 ^ (prefixWord ++ tailWord_1560632).sum := by decide
  have hdescent : baseEnd_1560632 < baseStart_1560632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560646 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1560646 : Nat := 118140960795 + 1560646 * 2 ^ 59
def prefixEnd_1560646 : Nat := 4983230072969 + 3 ^ 40 * 1560646 * 2
def baseEnd_1560646 : Nat := 356160679785247199576767

theorem tailTrace_1560646 : CollatzResearch.WordTrace tailWord_1560646 prefixEnd_1560646 356160679785247199576767 := by
  unfold tailWord_1560646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778794872001673561306431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37947623936035702641203861 1778794872001673561306431)
  ·
    refine ⟨2668192308002510341959647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1778794872001673561306431 2668192308002510341959647)
    ·
      refine ⟨4002288462003765512939471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2668192308002510341959647 4002288462003765512939471)
      ·
        refine ⟨6003432693005648269409207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4002288462003765512939471 6003432693005648269409207)
        ·
          refine ⟨9005149039508472404113811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6003432693005648269409207 9005149039508472404113811)
          ·
            refine ⟨13507723559262708606170717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005149039508472404113811 13507723559262708606170717)
            ·
              refine ⟨5065396334723515727314019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13507723559262708606170717 5065396334723515727314019)
              ·
                refine ⟨7598094502085273590971029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5065396334723515727314019 7598094502085273590971029)
                ·
                  refine ⟨356160679785247199576767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7598094502085273590971029 356160679785247199576767)
                  ·
                    rfl

theorem cell21_1560646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1560646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560646 prefixEnd_1560646 := by exact prefixLift 1560646
  have htrace : WordTrace (prefixWord ++ tailWord_1560646) baseStart_1560646 baseEnd_1560646 := by
    simpa [prefixWord, tailWord_1560646, baseEnd_1560646] using wordTrace_append hprefix tailTrace_1560646
  have hstable : (prefixWord ++ tailWord_1560646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560646).length < 2 ^ (prefixWord ++ tailWord_1560646).sum := by decide
  have hdescent : baseEnd_1560646 < baseStart_1560646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560688 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_1560688 : Nat := 118140960795 + 1560688 * 2 ^ 59
def prefixEnd_1560688 : Nat := 4983230072969 + 3 ^ 40 * 1560688 * 2
def baseEnd_1560688 : Nat := 356170264757464459876681

theorem tailTrace_1560688 : CollatzResearch.WordTrace tailWord_1560688 prefixEnd_1560688 356170264757464459876681 := by
  unfold tailWord_1560688
  simp only [CollatzResearch.WordTrace]
  refine ⟨28461483884950697567417359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37948645179934263423223145 28461483884950697567417359)
  ·
    refine ⟨42692225827426046351126039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28461483884950697567417359 42692225827426046351126039)
    ·
      refine ⟨64038338741139069526689059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42692225827426046351126039 64038338741139069526689059)
      ·
        refine ⟨96057508111708604290033589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64038338741139069526689059 96057508111708604290033589)
        ·
          refine ⟨9005391385472681652190649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96057508111708604290033589 9005391385472681652190649)
          ·
            refine ⟨6754043539104511239142987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9005391385472681652190649 6754043539104511239142987)
            ·
              refine ⟨10131065308656766858714481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6754043539104511239142987 10131065308656766858714481)
              ·
                refine ⟨7598298981492575144035861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10131065308656766858714481 7598298981492575144035861)
                ·
                  refine ⟨356170264757464459876681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7598298981492575144035861 356170264757464459876681)
                  ·
                    rfl

theorem cell21_1560688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_1560688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560688 prefixEnd_1560688 := by exact prefixLift 1560688
  have htrace : WordTrace (prefixWord ++ tailWord_1560688) baseStart_1560688 baseEnd_1560688 := by
    simpa [prefixWord, tailWord_1560688, baseEnd_1560688] using wordTrace_append hprefix tailTrace_1560688
  have hstable : (prefixWord ++ tailWord_1560688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560688).length < 2 ^ (prefixWord ++ tailWord_1560688).sum := by decide
  have hdescent : baseEnd_1560688 < baseStart_1560688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560708 : List Nat := [2, 3, 2, 1, 2, 1, 5, 2, 3]
def baseStart_1560708 : Nat := 118140960795 + 1560708 * 2 ^ 59
def prefixEnd_1560708 : Nat := 4983230072969 + 3 ^ 40 * 1560708 * 2
def baseEnd_1560708 : Nat := 356174829029948869543307

theorem tailTrace_1560708 : CollatzResearch.WordTrace tailWord_1560708 prefixEnd_1560708 356174829029948869543307 := by
  unfold tailWord_1560708
  simp only [CollatzResearch.WordTrace]
  refine ⟨28461848614914469275281389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37949131486552625700375185 28461848614914469275281389)
  ·
    refine ⟨10673193230592925978230521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28461848614914469275281389 10673193230592925978230521)
    ·
      refine ⟨8004894922944694483672891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10673193230592925978230521 8004894922944694483672891)
      ·
        refine ⟨12007342384417041725509337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8004894922944694483672891 12007342384417041725509337)
        ·
          refine ⟨9005506788312781294132003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12007342384417041725509337 9005506788312781294132003)
          ·
            refine ⟨13508260182469171941198005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005506788312781294132003 13508260182469171941198005)
            ·
              refine ⟨1266399392106484869487313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13508260182469171941198005 1266399392106484869487313)
              ·
                refine ⟨949799544079863652115485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266399392106484869487313 949799544079863652115485)
                ·
                  refine ⟨356174829029948869543307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949799544079863652115485 356174829029948869543307)
                  ·
                    rfl

theorem cell21_1560708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_1560708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560708 prefixEnd_1560708 := by exact prefixLift 1560708
  have htrace : WordTrace (prefixWord ++ tailWord_1560708) baseStart_1560708 baseEnd_1560708 := by
    simpa [prefixWord, tailWord_1560708, baseEnd_1560708] using wordTrace_append hprefix tailTrace_1560708
  have hstable : (prefixWord ++ tailWord_1560708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560708).length < 2 ^ (prefixWord ++ tailWord_1560708).sum := by decide
  have hdescent : baseEnd_1560708 < baseStart_1560708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560770 : List Nat := [3, 5, 1, 1, 1, 3, 1, 6]
def baseStart_1560770 : Nat := 118140960795 + 1560770 * 2 ^ 59
def prefixEnd_1560770 : Nat := 4983230072969 + 3 ^ 40 * 1560770 * 2
def baseEnd_1560770 : Nat := 118729659424883513169949

theorem tailTrace_1560770 : CollatzResearch.WordTrace tailWord_1560770 prefixEnd_1560770 118729659424883513169949 := by
  unfold tailWord_1560770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14231489638901080784829941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37950639037069548759546509 14231489638901080784829941)
  ·
    refine ⟨1334202153646976323577807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14231489638901080784829941 1334202153646976323577807)
    ·
      refine ⟨2001303230470464485366711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334202153646976323577807 2001303230470464485366711)
      ·
        refine ⟨3001954845705696728050067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001303230470464485366711 3001954845705696728050067)
        ·
          refine ⟨4502932268558545092075101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001954845705696728050067 4502932268558545092075101)
          ·
            refine ⟨1688599600709454409528163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4502932268558545092075101 1688599600709454409528163)
            ·
              refine ⟨2532899401064181614292245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688599600709454409528163 2532899401064181614292245)
              ·
                refine ⟨118729659424883513169949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2532899401064181614292245 118729659424883513169949)
                ·
                  rfl

theorem cell21_1560770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_1560770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560770 prefixEnd_1560770 := by exact prefixLift 1560770
  have htrace : WordTrace (prefixWord ++ tailWord_1560770) baseStart_1560770 baseEnd_1560770 := by
    simpa [prefixWord, tailWord_1560770, baseEnd_1560770] using wordTrace_append hprefix tailTrace_1560770
  have hstable : (prefixWord ++ tailWord_1560770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560770).length < 2 ^ (prefixWord ++ tailWord_1560770).sum := by decide
  have hdescent : baseEnd_1560770 < baseStart_1560770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560826 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_1560826 : Nat := 118140960795 + 1560826 * 2 ^ 59
def prefixEnd_1560826 : Nat := 4983230072969 + 3 ^ 40 * 1560826 * 2
def baseEnd_1560826 : Nat := 356201758237606886576399

theorem tailTrace_1560826 : CollatzResearch.WordTrace tailWord_1560826 prefixEnd_1560826 356201758237606886576399 := by
  unfold tailWord_1560826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14232000260850361175839583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37952000695600963135572221 14232000260850361175839583)
  ·
    refine ⟨21348000391275541763759375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14232000260850361175839583 21348000391275541763759375)
    ·
      refine ⟨32022000586913312645639063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21348000391275541763759375 32022000586913312645639063)
      ·
        refine ⟨48033000880369968968458595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32022000586913312645639063 48033000880369968968458595)
        ·
          refine ⟨72049501320554953452687893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48033000880369968968458595 72049501320554953452687893)
          ·
            refine ⟨3377320374401013443094745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72049501320554953452687893 3377320374401013443094745)
            ·
              refine ⟨2532990280800760082321059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377320374401013443094745 2532990280800760082321059)
              ·
                refine ⟨3799485421201140123481589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532990280800760082321059 3799485421201140123481589)
                ·
                  refine ⟨356201758237606886576399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3799485421201140123481589 356201758237606886576399)
                  ·
                    rfl

theorem cell21_1560826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_1560826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560826 prefixEnd_1560826 := by exact prefixLift 1560826
  have htrace : WordTrace (prefixWord ++ tailWord_1560826) baseStart_1560826 baseEnd_1560826 := by
    simpa [prefixWord, tailWord_1560826, baseEnd_1560826] using wordTrace_append hprefix tailTrace_1560826
  have hstable : (prefixWord ++ tailWord_1560826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560826).length < 2 ^ (prefixWord ++ tailWord_1560826).sum := by decide
  have hdescent : baseEnd_1560826 < baseStart_1560826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560877 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1560877 : Nat := 118140960795 + 1560877 * 2 ^ 59
def prefixEnd_1560877 : Nat := 4983230072969 + 3 ^ 40 * 1560877 * 2
def baseEnd_1560877 : Nat := 356213397132442131226295

theorem tailTrace_1560877 : CollatzResearch.WordTrace tailWord_1560877 prefixEnd_1560877 356213397132442131226295 := by
  unfold tailWord_1560877
  simp only [CollatzResearch.WordTrace]
  refine ⟨56929861166216680413464885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37953240777477786942309923 56929861166216680413464885)
  ·
    refine ⟨5337174484332813788762333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56929861166216680413464885 5337174484332813788762333)
    ·
      refine ⟨2001440431624805170785875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5337174484332813788762333 2001440431624805170785875)
      ·
        refine ⟨3002160647437207756178813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001440431624805170785875 3002160647437207756178813)
        ·
          refine ⟨1125810242788952908567055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3002160647437207756178813 1125810242788952908567055)
          ·
            refine ⟨1688715364183429362850583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125810242788952908567055 1688715364183429362850583)
            ·
              refine ⟨2533073046275144044275875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688715364183429362850583 2533073046275144044275875)
              ·
                refine ⟨3799609569412716066413813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533073046275144044275875 3799609569412716066413813)
                ·
                  refine ⟨356213397132442131226295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3799609569412716066413813 356213397132442131226295)
                  ·
                    rfl

theorem cell21_1560877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1560877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560877 prefixEnd_1560877 := by exact prefixLift 1560877
  have htrace : WordTrace (prefixWord ++ tailWord_1560877) baseStart_1560877 baseEnd_1560877 := by
    simpa [prefixWord, tailWord_1560877, baseEnd_1560877] using wordTrace_append hprefix tailTrace_1560877
  have hstable : (prefixWord ++ tailWord_1560877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560877).length < 2 ^ (prefixWord ++ tailWord_1560877).sum := by decide
  have hdescent : baseEnd_1560877 < baseStart_1560877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560933 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 4]
def baseStart_1560933 : Nat := 118140960795 + 1560933 * 2 ^ 59
def prefixEnd_1560933 : Nat := 4983230072969 + 3 ^ 40 * 1560933 * 2
def baseEnd_1560933 : Nat := 356226177095398478292847

theorem tailTrace_1560933 : CollatzResearch.WordTrace tailWord_1560933 prefixEnd_1560933 356226177095398478292847 := by
  unfold tailWord_1560933
  simp only [CollatzResearch.WordTrace]
  refine ⟨56931903654013801977503453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37954602436009201318335635 56931903654013801977503453)
  ·
    refine ⟨21349463870255175741563795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56931903654013801977503453 21349463870255175741563795)
    ·
      refine ⟨32024195805382763612345693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21349463870255175741563795 32024195805382763612345693)
      ·
        refine ⟨12009073427018536354629635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32024195805382763612345693 12009073427018536354629635)
        ·
          refine ⟨18013610140527804531944453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12009073427018536354629635 18013610140527804531944453)
          ·
            refine ⟨3377551901348963349739585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18013610140527804531944453 3377551901348963349739585)
            ·
              refine ⟨2533163926011722512304689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3377551901348963349739585 2533163926011722512304689)
              ·
                refine ⟨1899872944508791884228517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533163926011722512304689 1899872944508791884228517)
                ·
                  refine ⟨356226177095398478292847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1899872944508791884228517 356226177095398478292847)
                  ·
                    rfl

theorem cell21_1560933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_1560933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560933 prefixEnd_1560933 := by exact prefixLift 1560933
  have htrace : WordTrace (prefixWord ++ tailWord_1560933) baseStart_1560933 baseEnd_1560933 := by
    simpa [prefixWord, tailWord_1560933, baseEnd_1560933] using wordTrace_append hprefix tailTrace_1560933
  have hstable : (prefixWord ++ tailWord_1560933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560933).length < 2 ^ (prefixWord ++ tailWord_1560933).sum := by decide
  have hdescent : baseEnd_1560933 < baseStart_1560933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560936 : List Nat := [2, 1, 4, 2, 2, 1, 4, 2, 3]
def baseStart_1560936 : Nat := 118140960795 + 1560936 * 2 ^ 59
def prefixEnd_1560936 : Nat := 4983230072969 + 3 ^ 40 * 1560936 * 2
def baseEnd_1560936 : Nat := 356226861736271139742841

theorem tailTrace_1560936 : CollatzResearch.WordTrace tailWord_1560936 prefixEnd_1560936 356226861736271139742841 := by
  unfold tailWord_1560936
  simp only [CollatzResearch.WordTrace]
  refine ⟨28466006536501466744931331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37954675382001955659908441 28466006536501466744931331)
  ·
    refine ⟨42699009804752200117396997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28466006536501466744931331 42699009804752200117396997)
    ·
      refine ⟨8006064338391037522011937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42699009804752200117396997 8006064338391037522011937)
      ·
        refine ⟨6004548253793278141508953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8006064338391037522011937 6004548253793278141508953)
        ·
          refine ⟨4503411190344958606131715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6004548253793278141508953 4503411190344958606131715)
          ·
            refine ⟨6755116785517437909197573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503411190344958606131715 6755116785517437909197573)
            ·
              refine ⟨1266584397284519607974545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6755116785517437909197573 1266584397284519607974545)
              ·
                refine ⟨949938297963389705980909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266584397284519607974545 949938297963389705980909)
                ·
                  refine ⟨356226861736271139742841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 949938297963389705980909 356226861736271139742841)
                  ·
                    rfl

theorem cell21_1560936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_1560936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560936 prefixEnd_1560936 := by exact prefixLift 1560936
  have htrace : WordTrace (prefixWord ++ tailWord_1560936) baseStart_1560936 baseEnd_1560936 := by
    simpa [prefixWord, tailWord_1560936, baseEnd_1560936] using wordTrace_append hprefix tailTrace_1560936
  have hstable : (prefixWord ++ tailWord_1560936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560936).length < 2 ^ (prefixWord ++ tailWord_1560936).sum := by decide
  have hdescent : baseEnd_1560936 < baseStart_1560936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1560992 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_1560992 : Nat := 118140960795 + 1560992 * 2 ^ 59
def prefixEnd_1560992 : Nat := 4983230072969 + 3 ^ 40 * 1560992 * 2
def baseEnd_1560992 : Nat := 356239641699227486809393

theorem tailTrace_1560992 : CollatzResearch.WordTrace tailWord_1560992 prefixEnd_1560992 356239641699227486809393 := by
  unfold tailWord_1560992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28467027780400027526950615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37956037040533370035934153 28467027780400027526950615)
  ·
    refine ⟨42700541670600041290425923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28467027780400027526950615 42700541670600041290425923)
    ·
      refine ⟨64050812505900061935638885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42700541670600041290425923 64050812505900061935638885)
      ·
        refine ⟨12009527344856261612932291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64050812505900061935638885 12009527344856261612932291)
        ·
          refine ⟨18014291017284392419398437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12009527344856261612932291 18014291017284392419398437)
          ·
            refine ⟨3377679565740823578637207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18014291017284392419398437 3377679565740823578637207)
            ·
              refine ⟨5066519348611235367955811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377679565740823578637207 5066519348611235367955811)
              ·
                refine ⟨7599779022916853051933717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066519348611235367955811 7599779022916853051933717)
                ·
                  refine ⟨356239641699227486809393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7599779022916853051933717 356239641699227486809393)
                  ·
                    rfl

theorem cell21_1560992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_1560992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1560992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1560992 prefixEnd_1560992 := by exact prefixLift 1560992
  have htrace : WordTrace (prefixWord ++ tailWord_1560992) baseStart_1560992 baseEnd_1560992 := by
    simpa [prefixWord, tailWord_1560992, baseEnd_1560992] using wordTrace_append hprefix tailTrace_1560992
  have hstable : (prefixWord ++ tailWord_1560992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1560992).length < 2 ^ (prefixWord ++ tailWord_1560992).sum := by decide
  have hdescent : baseEnd_1560992 < baseStart_1560992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1560992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561068 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_1561068 : Nat := 118140960795 + 1561068 * 2 ^ 59
def prefixEnd_1561068 : Nat := 4983230072969 + 3 ^ 40 * 1561068 * 2
def baseEnd_1561068 : Nat := 356256985934668243542571

theorem tailTrace_1561068 : CollatzResearch.WordTrace tailWord_1561068 prefixEnd_1561068 356256985934668243542571 := by
  unfold tailWord_1561068
  simp only [CollatzResearch.WordTrace]
  refine ⟨28468413754262360016833929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37957885005683146689111905 28468413754262360016833929)
  ·
    refine ⟨21351310315696770012625447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28468413754262360016833929 21351310315696770012625447)
    ·
      refine ⟨32026965473545155018938171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21351310315696770012625447 32026965473545155018938171)
      ·
        refine ⟨48040448210317732528407257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32026965473545155018938171 48040448210317732528407257)
        ·
          refine ⟨36030336157738299396305443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48040448210317732528407257 36030336157738299396305443)
          ·
            refine ⟨54045504236607449094458165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36030336157738299396305443 54045504236607449094458165)
            ·
              refine ⟨5066766022181948352605453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54045504236607449094458165 5066766022181948352605453)
              ·
                refine ⟨1900037258318230632227045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5066766022181948352605453 1900037258318230632227045)
                ·
                  refine ⟨356256985934668243542571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1900037258318230632227045 356256985934668243542571)
                  ·
                    rfl

theorem cell21_1561068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_1561068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561068 prefixEnd_1561068 := by exact prefixLift 1561068
  have htrace : WordTrace (prefixWord ++ tailWord_1561068) baseStart_1561068 baseEnd_1561068 := by
    simpa [prefixWord, tailWord_1561068, baseEnd_1561068] using wordTrace_append hprefix tailTrace_1561068
  have hstable : (prefixWord ++ tailWord_1561068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561068).length < 2 ^ (prefixWord ++ tailWord_1561068).sum := by decide
  have hdescent : baseEnd_1561068 < baseStart_1561068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561130 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_1561130 : Nat := 118140960795 + 1561130 * 2 ^ 59
def prefixEnd_1561130 : Nat := 4983230072969 + 3 ^ 40 * 1561130 * 2
def baseEnd_1561130 : Nat := 356271135179369913509111

theorem tailTrace_1561130 : CollatzResearch.WordTrace tailWord_1561130 prefixEnd_1561130 356271135179369913509111 := by
  unfold tailWord_1561130
  simp only [CollatzResearch.WordTrace]
  refine ⟨14234772208575026155606211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37959392556200069748283229 14234772208575026155606211)
  ·
    refine ⟨21352158312862539233409317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14234772208575026155606211 21352158312862539233409317)
    ·
      refine ⟨4003529683661726106264247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21352158312862539233409317 4003529683661726106264247)
      ·
        refine ⟨6005294525492589159396371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4003529683661726106264247 6005294525492589159396371)
        ·
          refine ⟨9007941788238883739094557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6005294525492589159396371 9007941788238883739094557)
          ·
            refine ⟨3377978170589581402160459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9007941788238883739094557 3377978170589581402160459)
            ·
              refine ⟨5066967255884372103240689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377978170589581402160459 5066967255884372103240689)
              ·
                refine ⟨3800225441913279077430517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5066967255884372103240689 3800225441913279077430517)
                ·
                  refine ⟨356271135179369913509111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3800225441913279077430517 356271135179369913509111)
                  ·
                    rfl

theorem cell21_1561130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_1561130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561130 prefixEnd_1561130 := by exact prefixLift 1561130
  have htrace : WordTrace (prefixWord ++ tailWord_1561130) baseStart_1561130 baseEnd_1561130 := by
    simpa [prefixWord, tailWord_1561130, baseEnd_1561130] using wordTrace_append hprefix tailTrace_1561130
  have hstable : (prefixWord ++ tailWord_1561130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561130).length < 2 ^ (prefixWord ++ tailWord_1561130).sum := by decide
  have hdescent : baseEnd_1561130 < baseStart_1561130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561220 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1561220 : Nat := 118140960795 + 1561220 * 2 ^ 59
def prefixEnd_1561220 : Nat := 4983230072969 + 3 ^ 40 * 1561220 * 2
def baseEnd_1561220 : Nat := 356291674405549757008927

theorem tailTrace_1561220 : CollatzResearch.WordTrace tailWord_1561220 prefixEnd_1561220 356291674405549757008927 := by
  unfold tailWord_1561220
  simp only [CollatzResearch.WordTrace]
  refine ⟨28471185701987024996600557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37961580935982699995467409 28471185701987024996600557)
  ·
    refine ⟨10676694638245134373725209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28471185701987024996600557 10676694638245134373725209)
    ·
      refine ⟨8007520978683850780293907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10676694638245134373725209 8007520978683850780293907)
      ·
        refine ⟨12011281468025776170440861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8007520978683850780293907 12011281468025776170440861)
        ·
          refine ⟨4504230550509666063915323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12011281468025776170440861 4504230550509666063915323)
          ·
            refine ⟨6756345825764499095872985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504230550509666063915323 6756345825764499095872985)
            ·
              refine ⟨5067259369323374321904739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6756345825764499095872985 5067259369323374321904739)
              ·
                refine ⟨7600889053985061482857109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067259369323374321904739 7600889053985061482857109)
                ·
                  refine ⟨356291674405549757008927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7600889053985061482857109 356291674405549757008927)
                  ·
                    rfl

theorem cell21_1561220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1561220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561220 prefixEnd_1561220 := by exact prefixLift 1561220
  have htrace : WordTrace (prefixWord ++ tailWord_1561220) baseStart_1561220 baseEnd_1561220 := by
    simpa [prefixWord, tailWord_1561220, baseEnd_1561220] using wordTrace_append hprefix tailTrace_1561220
  have hstable : (prefixWord ++ tailWord_1561220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561220).length < 2 ^ (prefixWord ++ tailWord_1561220).sum := by decide
  have hdescent : baseEnd_1561220 < baseStart_1561220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561223 : List Nat := [1, 1, 4, 2, 1, 2, 5, 2, 3]
def baseStart_1561223 : Nat := 118140960795 + 1561223 * 2 ^ 59
def prefixEnd_1561223 : Nat := 4983230072969 + 3 ^ 40 * 1561223 * 2
def baseEnd_1561223 : Nat := 356292359046422418458921

theorem tailTrace_1561223 : CollatzResearch.WordTrace tailWord_1561223 prefixEnd_1561223 356292359046422418458921 := by
  unfold tailWord_1561223
  simp only [CollatzResearch.WordTrace]
  refine ⟨56942480822963181505560323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37961653881975454337040215 56942480822963181505560323)
  ·
    refine ⟨85413721234444772258340485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56942480822963181505560323 85413721234444772258340485)
    ·
      refine ⟨16015072731458394798438841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85413721234444772258340485 16015072731458394798438841)
      ·
        refine ⟨12011304548593796098829131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16015072731458394798438841 12011304548593796098829131)
        ·
          refine ⟨18016956822890694148243697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12011304548593796098829131 18016956822890694148243697)
          ·
            refine ⟨13512717617168020611182773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18016956822890694148243697 13512717617168020611182773)
            ·
              refine ⟨1266817276609501932298385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13512717617168020611182773 1266817276609501932298385)
              ·
                refine ⟨950112957457126449223789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266817276609501932298385 950112957457126449223789)
                ·
                  refine ⟨356292359046422418458921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950112957457126449223789 356292359046422418458921)
                  ·
                    rfl

theorem cell21_1561223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 3].length) (baseStart_1561223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561223 prefixEnd_1561223 := by exact prefixLift 1561223
  have htrace : WordTrace (prefixWord ++ tailWord_1561223) baseStart_1561223 baseEnd_1561223 := by
    simpa [prefixWord, tailWord_1561223, baseEnd_1561223] using wordTrace_append hprefix tailTrace_1561223
  have hstable : (prefixWord ++ tailWord_1561223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561223).length < 2 ^ (prefixWord ++ tailWord_1561223).sum := by decide
  have hdescent : baseEnd_1561223 < baseStart_1561223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561324 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_1561324 : Nat := 118140960795 + 1561324 * 2 ^ 59
def prefixEnd_1561324 : Nat := 4983230072969 + 3 ^ 40 * 1561324 * 2
def baseEnd_1561324 : Nat := 356315408622468687275381

theorem tailTrace_1561324 : CollatzResearch.WordTrace tailWord_1561324 prefixEnd_1561324 356315408622468687275381 := by
  unfold tailWord_1561324
  simp only [CollatzResearch.WordTrace]
  refine ⟨28473082297798637877493513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37964109730398183836658017 28473082297798637877493513)
  ·
    refine ⟨21354811723348978408120135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28473082297798637877493513 21354811723348978408120135)
    ·
      refine ⟨32032217585023467612180203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21354811723348978408120135 32032217585023467612180203)
      ·
        refine ⟨48048326377535201418270305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32032217585023467612180203 48048326377535201418270305)
        ·
          refine ⟨36036244783151401063702729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48048326377535201418270305 36036244783151401063702729)
          ·
            refine ⟨27027183587363550797777047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36036244783151401063702729 27027183587363550797777047)
            ·
              refine ⟨40540775381045326196665571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27027183587363550797777047 40540775381045326196665571)
              ·
                refine ⟨60811163071567989294998357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40540775381045326196665571 60811163071567989294998357)
                ·
                  refine ⟨356315408622468687275381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60811163071567989294998357 356315408622468687275381)
                  ·
                    rfl

theorem cell21_1561324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_1561324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561324 prefixEnd_1561324 := by exact prefixLift 1561324
  have htrace : WordTrace (prefixWord ++ tailWord_1561324) baseStart_1561324 baseEnd_1561324 := by
    simpa [prefixWord, tailWord_1561324, baseEnd_1561324] using wordTrace_append hprefix tailTrace_1561324
  have hstable : (prefixWord ++ tailWord_1561324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561324).length < 2 ^ (prefixWord ++ tailWord_1561324).sum := by decide
  have hdescent : baseEnd_1561324 < baseStart_1561324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561341 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1561341 : Nat := 118140960795 + 1561341 * 2 ^ 59
def prefixEnd_1561341 : Nat := 4983230072969 + 3 ^ 40 * 1561341 * 2
def baseEnd_1561341 : Nat := 356319288254080435492013

theorem tailTrace_1561341 : CollatzResearch.WordTrace tailWord_1561341 prefixEnd_1561341 356319288254080435492013 := by
  unfold tailWord_1561341
  simp only [CollatzResearch.WordTrace]
  refine ⟨56946784636535687658355877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37964523091023791772237251 56946784636535687658355877)
  ·
    refine ⟨10677522119350441435941727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56946784636535687658355877 10677522119350441435941727)
    ·
      refine ⟨16016283179025662153912591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10677522119350441435941727 16016283179025662153912591)
      ·
        refine ⟨24024424768538493230868887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16016283179025662153912591 24024424768538493230868887)
        ·
          refine ⟨36036637152807739846303331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24024424768538493230868887 36036637152807739846303331)
          ·
            refine ⟨54054955729211609769454997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36036637152807739846303331 54054955729211609769454997)
            ·
              refine ⟨2533826049806794207943203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54054955729211609769454997 2533826049806794207943203)
              ·
                refine ⟨3800739074710191311914805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533826049806794207943203 3800739074710191311914805)
                ·
                  refine ⟨356319288254080435492013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3800739074710191311914805 356319288254080435492013)
                  ·
                    rfl

theorem cell21_1561341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1561341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561341 prefixEnd_1561341 := by exact prefixLift 1561341
  have htrace : WordTrace (prefixWord ++ tailWord_1561341) baseStart_1561341 baseEnd_1561341 := by
    simpa [prefixWord, tailWord_1561341, baseEnd_1561341] using wordTrace_append hprefix tailTrace_1561341
  have hstable : (prefixWord ++ tailWord_1561341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561341).length < 2 ^ (prefixWord ++ tailWord_1561341).sum := by decide
  have hdescent : baseEnd_1561341 < baseStart_1561341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561375 : List Nat := [1, 1, 2, 4, 2, 4, 1, 3, 3]
def baseStart_1561375 : Nat := 118140960795 + 1561375 * 2 ^ 59
def prefixEnd_1561375 : Nat := 4983230072969 + 3 ^ 40 * 1561375 * 2
def baseEnd_1561375 : Nat := 356327047517303931925277

theorem tailTrace_1561375 : CollatzResearch.WordTrace tailWord_1561375 prefixEnd_1561375 356327047517303931925277 := by
  unfold tailWord_1561375
  simp only [CollatzResearch.WordTrace]
  refine ⟨56948024718412511465093579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37965349812275007643395719 56948024718412511465093579)
  ·
    refine ⟨85422037077618767197640369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56948024718412511465093579 85422037077618767197640369)
    ·
      refine ⟨64066527808214075398230277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85422037077618767197640369 64066527808214075398230277)
      ·
        refine ⟨12012473964040139137168177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64066527808214075398230277 12012473964040139137168177)
        ·
          refine ⟨9009355473030104352876133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12012473964040139137168177 9009355473030104352876133)
          ·
            refine ⟨1689254151193144566164275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9009355473030104352876133 1689254151193144566164275)
            ·
              refine ⟨2533881226789716849246413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689254151193144566164275 2533881226789716849246413)
              ·
                refine ⟨950205460046143818467405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2533881226789716849246413 950205460046143818467405)
                ·
                  refine ⟨356327047517303931925277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950205460046143818467405 356327047517303931925277)
                  ·
                    rfl

theorem cell21_1561375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 3].length) (baseStart_1561375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561375 prefixEnd_1561375 := by exact prefixLift 1561375
  have htrace : WordTrace (prefixWord ++ tailWord_1561375) baseStart_1561375 baseEnd_1561375 := by
    simpa [prefixWord, tailWord_1561375, baseEnd_1561375] using wordTrace_append hprefix tailTrace_1561375
  have hstable : (prefixWord ++ tailWord_1561375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561375).length < 2 ^ (prefixWord ++ tailWord_1561375).sum := by decide
  have hdescent : baseEnd_1561375 < baseStart_1561375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561448 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_1561448 : Nat := 118140960795 + 1561448 * 2 ^ 59
def prefixEnd_1561448 : Nat := 4983230072969 + 3 ^ 40 * 1561448 * 2
def baseEnd_1561448 : Nat := 356343707111872027208461

theorem tailTrace_1561448 : CollatzResearch.WordTrace tailWord_1561448 prefixEnd_1561448 356343707111872027208461 := by
  unfold tailWord_1561448
  simp only [CollatzResearch.WordTrace]
  refine ⟨28475343623574022466250499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37967124831432029955000665 28475343623574022466250499)
  ·
    refine ⟨42713015435361033699375749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28475343623574022466250499 42713015435361033699375749)
    ·
      refine ⟨8008690394130193818632953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42713015435361033699375749 8008690394130193818632953)
      ·
        refine ⟨6006517795597645363974715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8008690394130193818632953 6006517795597645363974715)
        ·
          refine ⟨9009776693396468045962073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006517795597645363974715 9009776693396468045962073)
          ·
            refine ⟨6757332520047351034471555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9009776693396468045962073 6757332520047351034471555)
            ·
              refine ⟨10135998780071026551707333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6757332520047351034471555 10135998780071026551707333)
              ·
                refine ⟨1900499771263317478445125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10135998780071026551707333 1900499771263317478445125)
                ·
                  refine ⟨356343707111872027208461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1900499771263317478445125 356343707111872027208461)
                  ·
                    rfl

theorem cell21_1561448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_1561448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561448 prefixEnd_1561448 := by exact prefixLift 1561448
  have htrace : WordTrace (prefixWord ++ tailWord_1561448) baseStart_1561448 baseEnd_1561448 := by
    simpa [prefixWord, tailWord_1561448, baseEnd_1561448] using wordTrace_append hprefix tailTrace_1561448
  have hstable : (prefixWord ++ tailWord_1561448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561448).length < 2 ^ (prefixWord ++ tailWord_1561448).sum := by decide
  have hdescent : baseEnd_1561448 < baseStart_1561448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561479 : List Nat := [1, 1, 4, 2, 3, 2, 3, 5]
def baseStart_1561479 : Nat := 118140960795 + 1561479 * 2 ^ 59
def prefixEnd_1561479 : Nat := 4983230072969 + 3 ^ 40 * 1561479 * 2
def baseEnd_1561479 : Nat := 118783593911407620730577

theorem tailTrace_1561479 : CollatzResearch.WordTrace tailWord_1561479 prefixEnd_1561479 118783593911407620730577 := by
  unfold tailWord_1561479
  simp only [CollatzResearch.WordTrace]
  refine ⟨56951817910035737226879491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37967878606690491484586327 56951817910035737226879491)
  ·
    refine ⟨85427726865053605840319237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56951817910035737226879491 85427726865053605840319237)
    ·
      refine ⟨16017698787197551095059857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85427726865053605840319237 16017698787197551095059857)
      ·
        refine ⟨12013274090398163321294893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16017698787197551095059857 12013274090398163321294893)
        ·
          refine ⟨4504977783899311245485585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12013274090398163321294893 4504977783899311245485585)
          ·
            refine ⟨3378733337924483434114189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4504977783899311245485585 3378733337924483434114189)
            ·
              refine ⟨1267025001721681287792821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3378733337924483434114189 1267025001721681287792821)
              ·
                refine ⟨118783593911407620730577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1267025001721681287792821 118783593911407620730577)
                ·
                  rfl

theorem cell21_1561479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 5].length) (baseStart_1561479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561479 prefixEnd_1561479 := by exact prefixLift 1561479
  have htrace : WordTrace (prefixWord ++ tailWord_1561479) baseStart_1561479 baseEnd_1561479 := by
    simpa [prefixWord, tailWord_1561479, baseEnd_1561479] using wordTrace_append hprefix tailTrace_1561479
  have hstable : (prefixWord ++ tailWord_1561479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561479).length < 2 ^ (prefixWord ++ tailWord_1561479).sum := by decide
  have hdescent : baseEnd_1561479 < baseStart_1561479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561544 : List Nat := [2, 1, 3, 1, 6, 1, 1, 3, 3]
def baseStart_1561544 : Nat := 118140960795 + 1561544 * 2 ^ 59
def prefixEnd_1561544 : Nat := 4983230072969 + 3 ^ 40 * 1561544 * 2
def baseEnd_1561544 : Nat := 356365615619797193608265

theorem tailTrace_1561544 : CollatzResearch.WordTrace tailWord_1561544 prefixEnd_1561544 356365615619797193608265 := by
  unfold tailWord_1561544
  simp only [CollatzResearch.WordTrace]
  refine ⟨28477094327400126663997843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37969459103200168885330457 28477094327400126663997843)
  ·
    refine ⟨42715641491100189995996765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28477094327400126663997843 42715641491100189995996765)
    ·
      refine ⟨16018365559162571248498787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42715641491100189995996765 16018365559162571248498787)
      ·
        refine ⟨24027548338743856872748181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16018365559162571248498787 24027548338743856872748181)
        ·
          refine ⟨1126291328378618290910071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24027548338743856872748181 1126291328378618290910071)
          ·
            refine ⟨1689436992567927436365107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126291328378618290910071 1689436992567927436365107)
            ·
              refine ⟨2534155488851891154547661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689436992567927436365107 2534155488851891154547661)
              ·
                refine ⟨950308308319459182955373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2534155488851891154547661 950308308319459182955373)
                ·
                  refine ⟨356365615619797193608265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950308308319459182955373 356365615619797193608265)
                  ·
                    rfl

theorem cell21_1561544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_1561544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561544 prefixEnd_1561544 := by exact prefixLift 1561544
  have htrace : WordTrace (prefixWord ++ tailWord_1561544) baseStart_1561544 baseEnd_1561544 := by
    simpa [prefixWord, tailWord_1561544, baseEnd_1561544] using wordTrace_append hprefix tailTrace_1561544
  have hstable : (prefixWord ++ tailWord_1561544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561544).length < 2 ^ (prefixWord ++ tailWord_1561544).sum := by decide
  have hdescent : baseEnd_1561544 < baseStart_1561544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561735 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 4]
def baseStart_1561735 : Nat := 118140960795 + 1561735 * 2 ^ 59
def prefixEnd_1561735 : Nat := 4983230072969 + 3 ^ 40 * 1561735 * 2
def baseEnd_1561735 : Nat := 356409204422023305924541

theorem tailTrace_1561735 : CollatzResearch.WordTrace tailWord_1561735 prefixEnd_1561735 356409204422023305924541 := by
  unfold tailWord_1561735
  simp only [CollatzResearch.WordTrace]
  refine ⟨56961154997108292948198659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37974103331405528632132439 56961154997108292948198659)
  ·
    refine ⟨85441732495662439422297989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56961154997108292948198659 85441732495662439422297989)
    ·
      refine ⟨16020324842936707391680873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85441732495662439422297989 16020324842936707391680873)
      ·
        refine ⟨12015243632202530543760655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16020324842936707391680873 12015243632202530543760655)
        ·
          refine ⟨18022865448303795815640983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12015243632202530543760655 18022865448303795815640983)
          ·
            refine ⟨27034298172455693723461475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18022865448303795815640983 27034298172455693723461475)
            ·
              refine ⟨40551447258683540585192213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27034298172455693723461475 40551447258683540585192213)
              ·
                refine ⟨1900849090250790964930885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40551447258683540585192213 1900849090250790964930885)
                ·
                  refine ⟨356409204422023305924541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1900849090250790964930885 356409204422023305924541)
                  ·
                    rfl

theorem cell21_1561735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 4].length) (baseStart_1561735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561735 prefixEnd_1561735 := by exact prefixLift 1561735
  have htrace : WordTrace (prefixWord ++ tailWord_1561735) baseStart_1561735 baseEnd_1561735 := by
    simpa [prefixWord, tailWord_1561735, baseEnd_1561735] using wordTrace_append hprefix tailTrace_1561735
  have hstable : (prefixWord ++ tailWord_1561735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561735).length < 2 ^ (prefixWord ++ tailWord_1561735).sum := by decide
  have hdescent : baseEnd_1561735 < baseStart_1561735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561752 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_1561752 : Nat := 118140960795 + 1561752 * 2 ^ 59
def prefixEnd_1561752 : Nat := 4983230072969 + 3 ^ 40 * 1561752 * 2
def baseEnd_1561752 : Nat := 356413084053635054141173

theorem tailTrace_1561752 : CollatzResearch.WordTrace tailWord_1561752 prefixEnd_1561752 356413084053635054141173 := by
  unfold tailWord_1561752
  simp only [CollatzResearch.WordTrace]
  refine ⟨28480887519023352425783755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37974516692031136567711673 28480887519023352425783755)
  ·
    refine ⟨42721331278535028638675633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28480887519023352425783755 42721331278535028638675633)
    ·
      refine ⟨32040998458901271479006725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42721331278535028638675633 32040998458901271479006725)
      ·
        refine ⟨6007687211043988402313761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32040998458901271479006725 6007687211043988402313761)
        ·
          refine ⟨4505765408282991301735321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6007687211043988402313761 4505765408282991301735321)
          ·
            refine ⟨3379324056212243476301491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505765408282991301735321 3379324056212243476301491)
            ·
              refine ⟨5068986084318365214452237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379324056212243476301491 5068986084318365214452237)
              ·
                refine ⟨1900869781619386955419589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5068986084318365214452237 1900869781619386955419589)
                ·
                  refine ⟨356413084053635054141173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1900869781619386955419589 356413084053635054141173)
                  ·
                    rfl

theorem cell21_1561752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_1561752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561752 prefixEnd_1561752 := by exact prefixLift 1561752
  have htrace : WordTrace (prefixWord ++ tailWord_1561752) baseStart_1561752 baseEnd_1561752 := by
    simpa [prefixWord, tailWord_1561752, baseEnd_1561752] using wordTrace_append hprefix tailTrace_1561752
  have hstable : (prefixWord ++ tailWord_1561752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561752).length < 2 ^ (prefixWord ++ tailWord_1561752).sum := by decide
  have hdescent : baseEnd_1561752 < baseStart_1561752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561831 : List Nat := [1, 1, 5, 3, 2, 1, 2, 3, 3]
def baseStart_1561831 : Nat := 118140960795 + 1561831 * 2 ^ 59
def prefixEnd_1561831 : Nat := 4983230072969 + 3 ^ 40 * 1561831 * 2
def baseEnd_1561831 : Nat := 356431112929948472324345

theorem tailTrace_1561831 : CollatzResearch.WordTrace tailWord_1561831 prefixEnd_1561831 356431112929948472324345 := by
  unfold tailWord_1561831
  simp only [CollatzResearch.WordTrace]
  refine ⟨56964656404760501343693347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37976437603173667562462231 56964656404760501343693347)
  ·
    refine ⟨85446984607140752015540021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56964656404760501343693347 85446984607140752015540021)
    ·
      refine ⟨8010654806919445501456877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85446984607140752015540021 8010654806919445501456877)
      ·
        refine ⟨3003995552594792063046329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8010654806919445501456877 3003995552594792063046329)
        ·
          refine ⟨2252996664446094047284747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3003995552594792063046329 2252996664446094047284747)
          ·
            refine ⟨3379494996669141070927121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252996664446094047284747 3379494996669141070927121)
            ·
              refine ⟨2534621247501855803195341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3379494996669141070927121 2534621247501855803195341)
              ·
                refine ⟨950482967813195926198253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2534621247501855803195341 950482967813195926198253)
                ·
                  refine ⟨356431112929948472324345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950482967813195926198253 356431112929948472324345)
                  ·
                    rfl

theorem cell21_1561831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 3].length) (baseStart_1561831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561831 prefixEnd_1561831 := by exact prefixLift 1561831
  have htrace : WordTrace (prefixWord ++ tailWord_1561831) baseStart_1561831 baseEnd_1561831 := by
    simpa [prefixWord, tailWord_1561831, baseEnd_1561831] using wordTrace_append hprefix tailTrace_1561831
  have hstable : (prefixWord ++ tailWord_1561831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561831).length < 2 ^ (prefixWord ++ tailWord_1561831).sum := by decide
  have hdescent : baseEnd_1561831 < baseStart_1561831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561842 : List Nat := [3, 2, 1, 3, 3, 1, 8]
def baseStart_1561842 : Nat := 118140960795 + 1561842 * 2 ^ 59
def prefixEnd_1561842 : Nat := 4983230072969 + 3 ^ 40 * 1561842 * 2
def baseEnd_1561842 : Nat := 39603735919979433071221

theorem tailTrace_1561842 : CollatzResearch.WordTrace tailWord_1561842 prefixEnd_1561842 39603735919979433071221 := by
  unfold tailWord_1561842
  simp only [CollatzResearch.WordTrace]
  refine ⟨14241264401930162555585945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37976705071813766814895853 14241264401930162555585945)
  ·
    refine ⟨10680948301447621916689459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14241264401930162555585945 10680948301447621916689459)
    ·
      refine ⟨16021422452171432875034189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10680948301447621916689459 16021422452171432875034189)
      ·
        refine ⟨6008033419564287328137821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16021422452171432875034189 6008033419564287328137821)
        ·
          refine ⟨2253012532336607748051683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6008033419564287328137821 2253012532336607748051683)
          ·
            refine ⟨3379518798504911622077525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253012532336607748051683 3379518798504911622077525)
            ·
              refine ⟨39603735919979433071221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3379518798504911622077525 39603735919979433071221)
              ·
                rfl

theorem cell21_1561842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 8].length) (baseStart_1561842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561842 prefixEnd_1561842 := by exact prefixLift 1561842
  have htrace : WordTrace (prefixWord ++ tailWord_1561842) baseStart_1561842 baseEnd_1561842 := by
    simpa [prefixWord, tailWord_1561842, baseEnd_1561842] using wordTrace_append hprefix tailTrace_1561842
  have hstable : (prefixWord ++ tailWord_1561842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561842).length < 2 ^ (prefixWord ++ tailWord_1561842).sum := by decide
  have hdescent : baseEnd_1561842 < baseStart_1561842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561918 : List Nat := [4, 2, 1, 2, 1, 1, 4, 6]
def baseStart_1561918 : Nat := 118140960795 + 1561918 * 2 ^ 59
def prefixEnd_1561918 : Nat := 4983230072969 + 3 ^ 40 * 1561918 * 2
def baseEnd_1561918 : Nat := 118816989171751884791389

theorem tailTrace_1561918 : CollatzResearch.WordTrace tailWord_1561918 prefixEnd_1561918 118816989171751884791389 := by
  unfold tailWord_1561918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7120978694430664400263801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37978553036963543468073605 7120978694430664400263801)
  ·
    refine ⟨5340734020822998300197851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7120978694430664400263801 5340734020822998300197851)
    ·
      refine ⟨8011101031234497450296777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5340734020822998300197851 8011101031234497450296777)
      ·
        refine ⟨6008325773425873087722583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8011101031234497450296777 6008325773425873087722583)
        ·
          refine ⟨9012488660138809631583875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008325773425873087722583 9012488660138809631583875)
          ·
            refine ⟨13518732990208214447375813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9012488660138809631583875 13518732990208214447375813)
            ·
              refine ⟨2534762435664040208882965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13518732990208214447375813 2534762435664040208882965)
              ·
                refine ⟨118816989171751884791389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2534762435664040208882965 118816989171751884791389)
                ·
                  rfl

theorem cell21_1561918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_1561918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561918 prefixEnd_1561918 := by exact prefixLift 1561918
  have htrace : WordTrace (prefixWord ++ tailWord_1561918) baseStart_1561918 baseEnd_1561918 := by
    simpa [prefixWord, tailWord_1561918, baseEnd_1561918] using wordTrace_append hprefix tailTrace_1561918
  have hstable : (prefixWord ++ tailWord_1561918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561918).length < 2 ^ (prefixWord ++ tailWord_1561918).sum := by decide
  have hdescent : baseEnd_1561918 < baseStart_1561918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561921 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 4]
def baseStart_1561921 : Nat := 118140960795 + 1561921 * 2 ^ 59
def prefixEnd_1561921 : Nat := 4983230072969 + 3 ^ 40 * 1561921 * 2
def baseEnd_1561921 : Nat := 356451652156128315824161

theorem tailTrace_1561921 : CollatzResearch.WordTrace tailWord_1561921 prefixEnd_1561921 356451652156128315824161 := by
  unfold tailWord_1561921
  simp only [CollatzResearch.WordTrace]
  refine ⟨56967938974434446714469617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37978625982956297809646411 56967938974434446714469617)
  ·
    refine ⟨42725954230825835035852213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56967938974434446714469617 42725954230825835035852213)
    ·
      refine ⟨4005558209139922034611145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42725954230825835035852213 4005558209139922034611145)
      ·
        refine ⟨3004168656854941525958359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4005558209139922034611145 3004168656854941525958359)
        ·
          refine ⟨4506252985282412288937539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004168656854941525958359 4506252985282412288937539)
          ·
            refine ⟨6759379477923618433406309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506252985282412288937539 6759379477923618433406309)
            ·
              refine ⟨1267383652110678456263683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6759379477923618433406309 1267383652110678456263683)
              ·
                refine ⟨1901075478166017684395525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267383652110678456263683 1901075478166017684395525)
                ·
                  refine ⟨356451652156128315824161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901075478166017684395525 356451652156128315824161)
                  ·
                    rfl

theorem cell21_1561921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_1561921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561921 prefixEnd_1561921 := by exact prefixLift 1561921
  have htrace : WordTrace (prefixWord ++ tailWord_1561921) baseStart_1561921 baseEnd_1561921 := by
    simpa [prefixWord, tailWord_1561921, baseEnd_1561921] using wordTrace_append hprefix tailTrace_1561921
  have hstable : (prefixWord ++ tailWord_1561921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561921).length < 2 ^ (prefixWord ++ tailWord_1561921).sum := by decide
  have hdescent : baseEnd_1561921 < baseStart_1561921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561946 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_1561946 : Nat := 118140960795 + 1561946 * 2 ^ 59
def prefixEnd_1561946 : Nat := 4983230072969 + 3 ^ 40 * 1561946 * 2
def baseEnd_1561946 : Nat := 356457357496733827907443

theorem tailTrace_1561946 : CollatzResearch.WordTrace tailWord_1561946 prefixEnd_1561946 356457357496733827907443 := by
  unfold tailWord_1561946
  simp only [CollatzResearch.WordTrace]
  refine ⟨14242212699835968996032423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37979233866229250656086461 14242212699835968996032423)
  ·
    refine ⟨21363319049753953494048635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14242212699835968996032423 21363319049753953494048635)
    ·
      refine ⟨32044978574630930241072953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21363319049753953494048635 32044978574630930241072953)
      ·
        refine ⟨24033733930973197680804715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32044978574630930241072953 24033733930973197680804715)
        ·
          refine ⟨36050600896459796521207073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24033733930973197680804715 36050600896459796521207073)
          ·
            refine ⟨27037950672344847390905305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36050600896459796521207073 27037950672344847390905305)
            ·
              refine ⟨20278463004258635543178979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27037950672344847390905305 20278463004258635543178979)
              ·
                refine ⟨30417694506387953314768469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20278463004258635543178979 30417694506387953314768469)
                ·
                  refine ⟨356457357496733827907443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30417694506387953314768469 356457357496733827907443)
                  ·
                    rfl

theorem cell21_1561946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_1561946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561946 prefixEnd_1561946 := by exact prefixLift 1561946
  have htrace : WordTrace (prefixWord ++ tailWord_1561946) baseStart_1561946 baseEnd_1561946 := by
    simpa [prefixWord, tailWord_1561946, baseEnd_1561946] using wordTrace_append hprefix tailTrace_1561946
  have hstable : (prefixWord ++ tailWord_1561946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561946).length < 2 ^ (prefixWord ++ tailWord_1561946).sum := by decide
  have hdescent : baseEnd_1561946 < baseStart_1561946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1561977 : List Nat := [1, 2, 1, 3, 2, 1, 5, 6]
def baseStart_1561977 : Nat := 118140960795 + 1561977 * 2 ^ 59
def prefixEnd_1561977 : Nat := 4983230072969 + 3 ^ 40 * 1561977 * 2
def baseEnd_1561977 : Nat := 118821477373028220963571

theorem tailTrace_1561977 : CollatzResearch.WordTrace tailWord_1561977 prefixEnd_1561977 118821477373028220963571 := by
  unfold tailWord_1561977
  simp only [CollatzResearch.WordTrace]
  refine ⟨56969981462231568278508185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37979987641487712185672123 56969981462231568278508185)
  ·
    refine ⟨42727486096673676208881139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56969981462231568278508185 42727486096673676208881139)
    ·
      refine ⟨64091229145010514313321709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42727486096673676208881139 64091229145010514313321709)
      ·
        refine ⟨24034210929378942867495641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64091229145010514313321709 24034210929378942867495641)
        ·
          refine ⟨18025658197034207150621731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24034210929378942867495641 18025658197034207150621731)
          ·
            refine ⟨27038487295551310725932597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18025658197034207150621731 27038487295551310725932597)
            ·
              refine ⟨2534858183957935380556181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27038487295551310725932597 2534858183957935380556181)
              ·
                refine ⟨118821477373028220963571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2534858183957935380556181 118821477373028220963571)
                ·
                  rfl

theorem cell21_1561977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 6].length) (baseStart_1561977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1561977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1561977 prefixEnd_1561977 := by exact prefixLift 1561977
  have htrace : WordTrace (prefixWord ++ tailWord_1561977) baseStart_1561977 baseEnd_1561977 := by
    simpa [prefixWord, tailWord_1561977, baseEnd_1561977] using wordTrace_append hprefix tailTrace_1561977
  have hstable : (prefixWord ++ tailWord_1561977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1561977).length < 2 ^ (prefixWord ++ tailWord_1561977).sum := by decide
  have hdescent : baseEnd_1561977 < baseStart_1561977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1561977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562014 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1562014 : Nat := 118140960795 + 1562014 * 2 ^ 59
def prefixEnd_1562014 : Nat := 4983230072969 + 3 ^ 40 * 1562014 * 2
def baseEnd_1562014 : Nat := 356472876023180820773971

theorem tailTrace_1562014 : CollatzResearch.WordTrace tailWord_1562014 prefixEnd_1562014 356472876023180820773971 := by
  unfold tailWord_1562014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121416370387190449700637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37980887308731682398403397 7121416370387190449700637)
  ·
    refine ⟨2670531138895196418637739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7121416370387190449700637 2670531138895196418637739)
    ·
      refine ⟨4005796708342794627956609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670531138895196418637739 4005796708342794627956609)
      ·
        refine ⟨3004347531257095970967457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4005796708342794627956609 3004347531257095970967457)
        ·
          refine ⟨2253260648442821978225593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3004347531257095970967457 2253260648442821978225593)
          ·
            refine ⟨1689945486332116483669195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2253260648442821978225593 1689945486332116483669195)
            ·
              refine ⟨2534918229498174725503793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689945486332116483669195 2534918229498174725503793)
              ·
                refine ⟨1901188672123631044127845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534918229498174725503793 1901188672123631044127845)
                ·
                  refine ⟨356472876023180820773971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901188672123631044127845 356472876023180820773971)
                  ·
                    rfl

theorem cell21_1562014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1562014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562014 prefixEnd_1562014 := by exact prefixLift 1562014
  have htrace : WordTrace (prefixWord ++ tailWord_1562014) baseStart_1562014 baseEnd_1562014 := by
    simpa [prefixWord, tailWord_1562014, baseEnd_1562014] using wordTrace_append hprefix tailTrace_1562014
  have hstable : (prefixWord ++ tailWord_1562014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562014).length < 2 ^ (prefixWord ++ tailWord_1562014).sum := by decide
  have hdescent : baseEnd_1562014 < baseStart_1562014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562070 : List Nat := [5, 2, 1, 1, 1, 2, 9]
def baseStart_1562070 : Nat := 118140960795 + 1562070 * 2 ^ 59
def prefixEnd_1562070 : Nat := 4983230072969 + 3 ^ 40 * 1562070 * 2
def baseEnd_1562070 : Nat := 39609517331793018648947

theorem tailTrace_1562070 : CollatzResearch.WordTrace tailWord_1562070 prefixEnd_1562070 39609517331793018648947 := by
  unfold tailWord_1562070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560835840680915322602729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37982248967263096774429109 3560835840680915322602729)
  ·
    refine ⟨2670626880510686491952047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3560835840680915322602729 2670626880510686491952047)
    ·
      refine ⟨4005940320766029737928071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670626880510686491952047 4005940320766029737928071)
      ·
        refine ⟨6008910481149044606892107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005940320766029737928071 6008910481149044606892107)
        ·
          refine ⟨9013365721723566910338161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008910481149044606892107 9013365721723566910338161)
          ·
            refine ⟨6760024291292675182753621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013365721723566910338161 6760024291292675182753621)
            ·
              refine ⟨39609517331793018648947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6760024291292675182753621 39609517331793018648947)
              ·
                rfl

theorem cell21_1562070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 9].length) (baseStart_1562070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562070 prefixEnd_1562070 := by exact prefixLift 1562070
  have htrace : WordTrace (prefixWord ++ tailWord_1562070) baseStart_1562070 baseEnd_1562070 := by
    simpa [prefixWord, tailWord_1562070, baseEnd_1562070] using wordTrace_append hprefix tailTrace_1562070
  have hstable : (prefixWord ++ tailWord_1562070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562070).length < 2 ^ (prefixWord ++ tailWord_1562070).sum := by decide
  have hdescent : baseEnd_1562070 < baseStart_1562070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562090 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_1562090 : Nat := 118140960795 + 1562090 * 2 ^ 59
def prefixEnd_1562090 : Nat := 4983230072969 + 3 ^ 40 * 1562090 * 2
def baseEnd_1562090 : Nat := 356490220258621577507149

theorem tailTrace_1562090 : CollatzResearch.WordTrace tailWord_1562090 prefixEnd_1562090 356490220258621577507149 := by
  unfold tailWord_1562090
  simp only [CollatzResearch.WordTrace]
  refine ⟨14243525727705547144342931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37982735273881459051581149 14243525727705547144342931)
  ·
    refine ⟨21365288591558320716514397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14243525727705547144342931 21365288591558320716514397)
    ·
      refine ⟨8011983221834370268692899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21365288591558320716514397 8011983221834370268692899)
      ·
        refine ⟨12017974832751555403039349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8011983221834370268692899 12017974832751555403039349)
        ·
          refine ⟨1126685140570458319034939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12017974832751555403039349 1126685140570458319034939)
          ·
            refine ⟨1690027710855687478552409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126685140570458319034939 1690027710855687478552409)
            ·
              refine ⟨1267520783141765608914307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690027710855687478552409 1267520783141765608914307)
              ·
                refine ⟨1901281174712648413371461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267520783141765608914307 1901281174712648413371461)
                ·
                  refine ⟨356490220258621577507149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901281174712648413371461 356490220258621577507149)
                  ·
                    rfl

theorem cell21_1562090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_1562090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562090 prefixEnd_1562090 := by exact prefixLift 1562090
  have htrace : WordTrace (prefixWord ++ tailWord_1562090) baseStart_1562090 baseEnd_1562090 := by
    simpa [prefixWord, tailWord_1562090, baseEnd_1562090] using wordTrace_append hprefix tailTrace_1562090
  have hstable : (prefixWord ++ tailWord_1562090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562090).length < 2 ^ (prefixWord ++ tailWord_1562090).sum := by decide
  have hdescent : baseEnd_1562090 < baseStart_1562090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562222 : List Nat := [4, 1, 2, 2, 3, 1, 1, 7]
def baseStart_1562222 : Nat := 118140960795 + 1562222 * 2 ^ 59
def prefixEnd_1562222 : Nat := 4983230072969 + 3 ^ 40 * 1562222 * 2
def baseEnd_1562222 : Nat := 118840114819006227102293

theorem tailTrace_1562222 : CollatzResearch.WordTrace tailWord_1562222 prefixEnd_1562222 118840114819006227102293 := by
  unfold tailWord_1562222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7122364668292996890147115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37985944897562650080784613 7122364668292996890147115)
  ·
    refine ⟨10683547002439495335220673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7122364668292996890147115 10683547002439495335220673)
    ·
      refine ⟨8012660251829621501415505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10683547002439495335220673 8012660251829621501415505)
      ·
        refine ⟨6009495188872216126061629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8012660251829621501415505 6009495188872216126061629)
        ·
          refine ⟨2253560695827081047273111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6009495188872216126061629 2253560695827081047273111)
          ·
            refine ⟨3380341043740621570909667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253560695827081047273111 3380341043740621570909667)
            ·
              refine ⟨5070511565610932356364501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380341043740621570909667 5070511565610932356364501)
              ·
                refine ⟨118840114819006227102293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5070511565610932356364501 118840114819006227102293)
                ·
                  rfl

theorem cell21_1562222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_1562222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562222 prefixEnd_1562222 := by exact prefixLift 1562222
  have htrace : WordTrace (prefixWord ++ tailWord_1562222) baseStart_1562222 baseEnd_1562222 := by
    simpa [prefixWord, tailWord_1562222, baseEnd_1562222] using wordTrace_append hprefix tailTrace_1562222
  have hstable : (prefixWord ++ tailWord_1562222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562222).length < 2 ^ (prefixWord ++ tailWord_1562222).sum := by decide
  have hdescent : baseEnd_1562222 < baseStart_1562222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562371 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 5]
def baseStart_1562371 : Nat := 118140960795 + 1562371 * 2 ^ 59
def prefixEnd_1562371 : Nat := 4983230072969 + 3 ^ 40 * 1562371 * 2
def baseEnd_1562371 : Nat := 356554348287027533323241

theorem tailTrace_1562371 : CollatzResearch.WordTrace tailWord_1562371 prefixEnd_1562371 356554348287027533323241 := by
  unfold tailWord_1562371
  simp only [CollatzResearch.WordTrace]
  refine ⟨56984351822804173568350967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37989567881869449045567311 56984351822804173568350967)
  ·
    refine ⟨85476527734206260352526451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56984351822804173568350967 85476527734206260352526451)
    ·
      refine ⟨128214791601309390528789677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85476527734206260352526451 128214791601309390528789677)
      ·
        refine ⟨48080546850491021448296129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128214791601309390528789677 48080546850491021448296129)
        ·
          refine ⟨36060410137868266086222097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48080546850491021448296129 36060410137868266086222097)
          ·
            refine ⟨27045307603401199564666573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36060410137868266086222097 27045307603401199564666573)
            ·
              refine ⟨10141990351275449836749965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27045307603401199564666573 10141990351275449836749965)
              ·
                refine ⟨3803246381728293688781237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10141990351275449836749965 3803246381728293688781237)
                ·
                  refine ⟨356554348287027533323241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3803246381728293688781237 356554348287027533323241)
                  ·
                    rfl

theorem cell21_1562371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_1562371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562371 prefixEnd_1562371 := by exact prefixLift 1562371
  have htrace : WordTrace (prefixWord ++ tailWord_1562371) baseStart_1562371 baseEnd_1562371 := by
    simpa [prefixWord, tailWord_1562371, baseEnd_1562371] using wordTrace_append hprefix tailTrace_1562371
  have hstable : (prefixWord ++ tailWord_1562371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562371).length < 2 ^ (prefixWord ++ tailWord_1562371).sum := by decide
  have hdescent : baseEnd_1562371 < baseStart_1562371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562402 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1562402 : Nat := 118140960795 + 1562402 * 2 ^ 59
def prefixEnd_1562402 : Nat := 4983230072969 + 3 ^ 40 * 1562402 * 2
def baseEnd_1562402 : Nat := 356561422909378368306511

theorem tailTrace_1562402 : CollatzResearch.WordTrace tailWord_1562402 prefixEnd_1562402 356561422909378368306511 := by
  unfold tailWord_1562402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14246370621422966465682365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37990321657127910575152973 14246370621422966465682365)
  ·
    refine ⟨5342388983033612424630887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14246370621422966465682365 5342388983033612424630887)
    ·
      refine ⟨8013583474550418636946331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5342388983033612424630887 8013583474550418636946331)
      ·
        refine ⟨12020375211825627955419497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8013583474550418636946331 12020375211825627955419497)
        ·
          refine ⟨9015281408869220966564623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12020375211825627955419497 9015281408869220966564623)
          ·
            refine ⟨13522922113303831449846935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9015281408869220966564623 13522922113303831449846935)
            ·
              refine ⟨20284383169955747174770403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13522922113303831449846935 20284383169955747174770403)
              ·
                refine ⟨30426574754933620762155605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20284383169955747174770403 30426574754933620762155605)
                ·
                  refine ⟨356561422909378368306511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30426574754933620762155605 356561422909378368306511)
                  ·
                    rfl

theorem cell21_1562402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1562402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562402 prefixEnd_1562402 := by exact prefixLift 1562402
  have htrace : WordTrace (prefixWord ++ tailWord_1562402) baseStart_1562402 baseEnd_1562402 := by
    simpa [prefixWord, tailWord_1562402, baseEnd_1562402] using wordTrace_append hprefix tailTrace_1562402
  have hstable : (prefixWord ++ tailWord_1562402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562402).length < 2 ^ (prefixWord ++ tailWord_1562402).sum := by decide
  have hdescent : baseEnd_1562402 < baseStart_1562402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562405 : List Nat := [1, 3, 1, 2, 3, 2, 3, 3, 3]
def baseStart_1562405 : Nat := 118140960795 + 1562405 * 2 ^ 59
def prefixEnd_1562405 : Nat := 4983230072969 + 3 ^ 40 * 1562405 * 2
def baseEnd_1562405 : Nat := 356562107550251029756505

theorem tailTrace_1562405 : CollatzResearch.WordTrace tailWord_1562405 prefixEnd_1562405 356562107550251029756505 := by
  unfold tailWord_1562405
  simp only [CollatzResearch.WordTrace]
  refine ⟨56985591904680997375088669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37990394603120664916725779 56985591904680997375088669)
  ·
    refine ⟨21369596964255374015658251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56985591904680997375088669 21369596964255374015658251)
    ·
      refine ⟨32054395446383061023487377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21369596964255374015658251 32054395446383061023487377)
      ·
        refine ⟨24040796584787295767615533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32054395446383061023487377 24040796584787295767615533)
        ·
          refine ⟨9015298719295235912855825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24040796584787295767615533 9015298719295235912855825)
          ·
            refine ⟨6761474039471426934641869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9015298719295235912855825 6761474039471426934641869)
            ·
              refine ⟨2535552764801785100490701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6761474039471426934641869 2535552764801785100490701)
              ·
                refine ⟨950832286800669412684013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2535552764801785100490701 950832286800669412684013)
                ·
                  refine ⟨356562107550251029756505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950832286800669412684013 356562107550251029756505)
                  ·
                    rfl

theorem cell21_1562405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_1562405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562405 prefixEnd_1562405 := by exact prefixLift 1562405
  have htrace : WordTrace (prefixWord ++ tailWord_1562405) baseStart_1562405 baseEnd_1562405 := by
    simpa [prefixWord, tailWord_1562405, baseEnd_1562405] using wordTrace_append hprefix tailTrace_1562405
  have hstable : (prefixWord ++ tailWord_1562405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562405).length < 2 ^ (prefixWord ++ tailWord_1562405).sum := by decide
  have hdescent : baseEnd_1562405 < baseStart_1562405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562422 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1562422 : Nat := 118140960795 + 1562422 * 2 ^ 59
def prefixEnd_1562422 : Nat := 4983230072969 + 3 ^ 40 * 1562422 * 2
def baseEnd_1562422 : Nat := 356565987181862777973137

theorem tailTrace_1562422 : CollatzResearch.WordTrace tailWord_1562422 prefixEnd_1562422 356565987181862777973137 := by
  unfold tailWord_1562422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561638246601213079903595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37990807963746272852305013 3561638246601213079903595)
  ·
    refine ⟨5342457369901819619855393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3561638246601213079903595 5342457369901819619855393)
    ·
      refine ⟨4006843027426364714891545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5342457369901819619855393 4006843027426364714891545)
      ·
        refine ⟨3005132270569773536168659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4006843027426364714891545 3005132270569773536168659)
        ·
          refine ⟨4507698405854660304252989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005132270569773536168659 4507698405854660304252989)
          ·
            refine ⟨1690386902195497614094871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4507698405854660304252989 1690386902195497614094871)
            ·
              refine ⟨2535580353293246421142307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690386902195497614094871 2535580353293246421142307)
              ·
                refine ⟨3803370529939869631713461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535580353293246421142307 3803370529939869631713461)
                ·
                  refine ⟨356565987181862777973137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3803370529939869631713461 356565987181862777973137)
                  ·
                    rfl

theorem cell21_1562422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1562422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562422 prefixEnd_1562422 := by exact prefixLift 1562422
  have htrace : WordTrace (prefixWord ++ tailWord_1562422) baseStart_1562422 baseEnd_1562422 := by
    simpa [prefixWord, tailWord_1562422, baseEnd_1562422] using wordTrace_append hprefix tailTrace_1562422
  have hstable : (prefixWord ++ tailWord_1562422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562422).length < 2 ^ (prefixWord ++ tailWord_1562422).sum := by decide
  have hdescent : baseEnd_1562422 < baseStart_1562422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562529 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 4]
def baseStart_1562529 : Nat := 118140960795 + 1562529 * 2 ^ 59
def prefixEnd_1562529 : Nat := 4983230072969 + 3 ^ 40 * 1562529 * 2
def baseEnd_1562529 : Nat := 356590406039654369689585

theorem tailTrace_1562529 : CollatzResearch.WordTrace tailWord_1562529 prefixEnd_1562529 356590406039654369689585 := by
  unfold tailWord_1562529
  simp only [CollatzResearch.WordTrace]
  refine ⟨56990114556231766552602641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37993409704154511035068427 56990114556231766552602641)
  ·
    refine ⟨42742585917173824914451981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56990114556231766552602641 42742585917173824914451981)
    ·
      refine ⟨16028469718940184342919493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42742585917173824914451981 16028469718940184342919493)
      ·
        refine ⟨3005338072301284564297405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16028469718940184342919493 3005338072301284564297405)
        ·
          refine ⟨1127001777112981711611527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3005338072301284564297405 1127001777112981711611527)
          ·
            refine ⟨1690502665669472567417291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127001777112981711611527 1690502665669472567417291)
            ·
              refine ⟨2535753998504208851125937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690502665669472567417291 2535753998504208851125937)
              ·
                refine ⟨1901815498878156638344453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535753998504208851125937 1901815498878156638344453)
                ·
                  refine ⟨356590406039654369689585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1901815498878156638344453 356590406039654369689585)
                  ·
                    rfl

theorem cell21_1562529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_1562529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562529 prefixEnd_1562529 := by exact prefixLift 1562529
  have htrace : WordTrace (prefixWord ++ tailWord_1562529) baseStart_1562529 baseEnd_1562529 := by
    simpa [prefixWord, tailWord_1562529, baseEnd_1562529] using wordTrace_append hprefix tailTrace_1562529
  have hstable : (prefixWord ++ tailWord_1562529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562529).length < 2 ^ (prefixWord ++ tailWord_1562529).sum := by decide
  have hdescent : baseEnd_1562529 < baseStart_1562529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562585 : List Nat := [1, 2, 1, 2, 6, 2, 7]
def baseStart_1562585 : Nat := 118140960795 + 1562585 * 2 ^ 59
def prefixEnd_1562585 : Nat := 4983230072969 + 3 ^ 40 * 1562585 * 2
def baseEnd_1562585 : Nat := 39622576222512301861793

theorem tailTrace_1562585 : CollatzResearch.WordTrace tailWord_1562585 prefixEnd_1562585 39622576222512301861793 := by
  unfold tailWord_1562585
  simp only [CollatzResearch.WordTrace]
  refine ⟨56992157044028888116641209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37994771362685925411094139 56992157044028888116641209)
  ·
    refine ⟨42744117783021666087480907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56992157044028888116641209 42744117783021666087480907)
    ·
      refine ⟨64116176674532499131221361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42744117783021666087480907 64116176674532499131221361)
      ·
        refine ⟨48087132505899374348416021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64116176674532499131221361 48087132505899374348416021)
        ·
          refine ⟨2254084336214033172582001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48087132505899374348416021 2254084336214033172582001)
          ·
            refine ⟨1690563252160524879436501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254084336214033172582001 1690563252160524879436501)
            ·
              refine ⟨39622576222512301861793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1690563252160524879436501 39622576222512301861793)
              ·
                rfl

theorem cell21_1562585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 7].length) (baseStart_1562585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562585 prefixEnd_1562585 := by exact prefixLift 1562585
  have htrace : WordTrace (prefixWord ++ tailWord_1562585) baseStart_1562585 baseEnd_1562585 := by
    simpa [prefixWord, tailWord_1562585, baseEnd_1562585] using wordTrace_append hprefix tailTrace_1562585
  have hstable : (prefixWord ++ tailWord_1562585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562585).length < 2 ^ (prefixWord ++ tailWord_1562585).sum := by decide
  have hdescent : baseEnd_1562585 < baseStart_1562585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562650 : List Nat := [3, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_1562650 : Nat := 118140960795 + 1562650 * 2 ^ 59
def prefixEnd_1562650 : Nat := 4983230072969 + 3 ^ 40 * 1562650 * 2
def baseEnd_1562650 : Nat := 356618019888185048172671

theorem tailTrace_1562650 : CollatzResearch.WordTrace tailWord_1562650 prefixEnd_1562650 356618019888185048172671 := by
  unfold tailWord_1562650
  simp only [CollatzResearch.WordTrace]
  refine ⟨14248631947198351054439351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37996351859195602811838269 14248631947198351054439351)
  ·
    refine ⟨21372947920797526581659027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14248631947198351054439351 21372947920797526581659027)
    ·
      refine ⟨32059421881196289872488541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21372947920797526581659027 32059421881196289872488541)
      ·
        refine ⟨12022283205448608702183203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32059421881196289872488541 12022283205448608702183203)
        ·
          refine ⟨18033424808172913053274805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12022283205448608702183203 18033424808172913053274805)
          ·
            refine ⟨1690633575766210598744513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18033424808172913053274805 1690633575766210598744513)
            ·
              refine ⟨1267975181824657949058385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690633575766210598744513 1267975181824657949058385)
              ·
                refine ⟨950981386368493461793789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267975181824657949058385 950981386368493461793789)
                ·
                  refine ⟨356618019888185048172671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 950981386368493461793789 356618019888185048172671)
                  ·
                    rfl

theorem cell21_1562650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_1562650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562650 prefixEnd_1562650 := by exact prefixLift 1562650
  have htrace : WordTrace (prefixWord ++ tailWord_1562650) baseStart_1562650 baseEnd_1562650 := by
    simpa [prefixWord, tailWord_1562650, baseEnd_1562650] using wordTrace_append hprefix tailTrace_1562650
  have hstable : (prefixWord ++ tailWord_1562650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562650).length < 2 ^ (prefixWord ++ tailWord_1562650).sum := by decide
  have hdescent : baseEnd_1562650 < baseStart_1562650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562661 : List Nat := [1, 3, 1, 2, 2, 5, 1, 6]
def baseStart_1562661 : Nat := 118140960795 + 1562661 * 2 ^ 59
def prefixEnd_1562661 : Nat := 4983230072969 + 3 ^ 40 * 1562661 * 2
def baseEnd_1562661 : Nat := 118873510079350491163105

theorem tailTrace_1562661 : CollatzResearch.WordTrace tailWord_1562661 prefixEnd_1562661 118873510079350491163105 := by
  unfold tailWord_1562661
  simp only [CollatzResearch.WordTrace]
  refine ⟨56994928991753553096407837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37996619327835702064271891 56994928991753553096407837)
  ·
    refine ⟨21373098371907582411152939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56994928991753553096407837 21373098371907582411152939)
    ·
      refine ⟨32059647557861373616729409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21373098371907582411152939 32059647557861373616729409)
      ·
        refine ⟨24044735668396030212547057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32059647557861373616729409 24044735668396030212547057)
        ·
          refine ⟨18033551751297022659410293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24044735668396030212547057 18033551751297022659410293)
          ·
            refine ⟨1690645476684095874319715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18033551751297022659410293 1690645476684095874319715)
            ·
              refine ⟨2535968215026143811479573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690645476684095874319715 2535968215026143811479573)
              ·
                refine ⟨118873510079350491163105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2535968215026143811479573 118873510079350491163105)
                ·
                  rfl

theorem cell21_1562661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 6].length) (baseStart_1562661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562661 prefixEnd_1562661 := by exact prefixLift 1562661
  have htrace : WordTrace (prefixWord ++ tailWord_1562661) baseStart_1562661 baseEnd_1562661 := by
    simpa [prefixWord, tailWord_1562661, baseEnd_1562661] using wordTrace_append hprefix tailTrace_1562661
  have hstable : (prefixWord ++ tailWord_1562661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562661).length < 2 ^ (prefixWord ++ tailWord_1562661).sum := by decide
  have hdescent : baseEnd_1562661 < baseStart_1562661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562678 : List Nat := [5, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1562678 : Nat := 118140960795 + 1562678 * 2 ^ 59
def prefixEnd_1562678 : Nat := 4983230072969 + 3 ^ 40 * 1562678 * 2
def baseEnd_1562678 : Nat := 118874803289887740568649

theorem tailTrace_1562678 : CollatzResearch.WordTrace tailWord_1562678 prefixEnd_1562678 118874803289887740568649 := by
  unfold tailWord_1562678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562221814543247812486043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37997032688461309999851125 3562221814543247812486043)
  ·
    refine ⟨5343332721814871718729065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3562221814543247812486043 5343332721814871718729065)
    ·
      refine ⟨4007499541361153789046799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5343332721814871718729065 4007499541361153789046799)
      ·
        refine ⟨6011249312041730683570199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4007499541361153789046799 6011249312041730683570199)
        ·
          refine ⟨9016873968062596025355299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6011249312041730683570199 9016873968062596025355299)
          ·
            refine ⟨13525310952093894038032949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9016873968062596025355299 13525310952093894038032949)
            ·
              refine ⟨1267997901758802566065589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13525310952093894038032949 1267997901758802566065589)
              ·
                refine ⟨118874803289887740568649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1267997901758802566065589 118874803289887740568649)
                ·
                  rfl

theorem cell21_1562678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1562678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562678 prefixEnd_1562678 := by exact prefixLift 1562678
  have htrace : WordTrace (prefixWord ++ tailWord_1562678) baseStart_1562678 baseEnd_1562678 := by
    simpa [prefixWord, tailWord_1562678, baseEnd_1562678] using wordTrace_append hprefix tailTrace_1562678
  have hstable : (prefixWord ++ tailWord_1562678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562678).length < 2 ^ (prefixWord ++ tailWord_1562678).sum := by decide
  have hdescent : baseEnd_1562678 < baseStart_1562678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562903 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 5]
def baseStart_1562903 : Nat := 118140960795 + 1562903 * 2 ^ 59
def prefixEnd_1562903 : Nat := 4983230072969 + 3 ^ 40 * 1562903 * 2
def baseEnd_1562903 : Nat := 356675757935112830455487

theorem tailTrace_1562903 : CollatzResearch.WordTrace tailWord_1562903 prefixEnd_1562903 356675757935112830455487 := by
  unfold tailWord_1562903
  simp only [CollatzResearch.WordTrace]
  refine ⟨57003755456876828426717363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38002503637917885617811575 57003755456876828426717363)
  ·
    refine ⟨85505633185315242640076045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57003755456876828426717363 85505633185315242640076045)
    ·
      refine ⟨32064612444493215990028517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85505633185315242640076045 32064612444493215990028517)
      ·
        refine ⟨6012114833342477998130347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32064612444493215990028517 6012114833342477998130347)
        ·
          refine ⟨9018172250013716997195521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6012114833342477998130347 9018172250013716997195521)
          ·
            refine ⟨6763629187510287747896641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9018172250013716997195521 6763629187510287747896641)
            ·
              refine ⟨5072721890632715810922481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6763629187510287747896641 5072721890632715810922481)
              ·
                refine ⟨3804541417974536858191861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5072721890632715810922481 3804541417974536858191861)
                ·
                  refine ⟨356675757935112830455487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3804541417974536858191861 356675757935112830455487)
                  ·
                    rfl

theorem cell21_1562903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_1562903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562903 prefixEnd_1562903 := by exact prefixLift 1562903
  have htrace : WordTrace (prefixWord ++ tailWord_1562903) baseStart_1562903 baseEnd_1562903 := by
    simpa [prefixWord, tailWord_1562903, baseEnd_1562903] using wordTrace_append hprefix tailTrace_1562903
  have hstable : (prefixWord ++ tailWord_1562903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562903).length < 2 ^ (prefixWord ++ tailWord_1562903).sum := by decide
  have hdescent : baseEnd_1562903 < baseStart_1562903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1562906 : List Nat := [3, 1, 1, 3, 4, 2, 2, 5]
def baseStart_1562906 : Nat := 118140960795 + 1562906 * 2 ^ 59
def prefixEnd_1562906 : Nat := 4983230072969 + 3 ^ 40 * 1562906 * 2
def baseEnd_1562906 : Nat := 118892147525328497301827

theorem tailTrace_1562906 : CollatzResearch.WordTrace tailWord_1562906 prefixEnd_1562906 118892147525328497301827 := by
  unfold tailWord_1562906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14250966218966489984769143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38002576583910639959384381 14250966218966489984769143)
  ·
    refine ⟨21376449328449734977153715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14250966218966489984769143 21376449328449734977153715)
    ·
      refine ⟨32064673992674602465730573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21376449328449734977153715 32064673992674602465730573)
      ·
        refine ⟨12024252747252975924648965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32064673992674602465730573 12024252747252975924648965)
        ·
          refine ⟨2254547390109932985871681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12024252747252975924648965 2254547390109932985871681)
          ·
            refine ⟨1690910542582449739403761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254547390109932985871681 1690910542582449739403761)
            ·
              refine ⟨1268182906936837304552821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690910542582449739403761 1268182906936837304552821)
              ·
                refine ⟨118892147525328497301827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1268182906936837304552821 118892147525328497301827)
                ·
                  rfl

theorem cell21_1562906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_1562906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1562906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1562906 prefixEnd_1562906 := by exact prefixLift 1562906
  have htrace : WordTrace (prefixWord ++ tailWord_1562906) baseStart_1562906 baseEnd_1562906 := by
    simpa [prefixWord, tailWord_1562906, baseEnd_1562906] using wordTrace_append hprefix tailTrace_1562906
  have hstable : (prefixWord ++ tailWord_1562906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1562906).length < 2 ^ (prefixWord ++ tailWord_1562906).sum := by decide
  have hdescent : baseEnd_1562906 < baseStart_1562906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1562906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563041 : List Nat := [1, 2, 3, 5, 1, 1, 8]
def baseStart_1563041 : Nat := 118140960795 + 1563041 * 2 ^ 59
def prefixEnd_1563041 : Nat := 4983230072969 + 3 ^ 40 * 1563041 * 2
def baseEnd_1563041 : Nat := 39634139046139473017245

theorem tailTrace_1563041 : CollatzResearch.WordTrace tailWord_1563041 prefixEnd_1563041 39634139046139473017245 := by
  unfold tailWord_1563041
  simp only [CollatzResearch.WordTrace]
  refine ⟨57008788730376877995240977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38005859153584585330160651 57008788730376877995240977)
  ·
    refine ⟨42756591547782658496430733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57008788730376877995240977 42756591547782658496430733)
    ·
      refine ⟨16033721830418496936161525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42756591547782658496430733 16033721830418496936161525)
      ·
        refine ⟨1503161421601734087765143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16033721830418496936161525 1503161421601734087765143)
        ·
          refine ⟨2254742132402601131647715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503161421601734087765143 2254742132402601131647715)
          ·
            refine ⟨3382113198603901697471573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254742132402601131647715 3382113198603901697471573)
            ·
              refine ⟨39634139046139473017245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3382113198603901697471573 39634139046139473017245)
              ·
                rfl

theorem cell21_1563041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 8].length) (baseStart_1563041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563041 prefixEnd_1563041 := by exact prefixLift 1563041
  have htrace : WordTrace (prefixWord ++ tailWord_1563041) baseStart_1563041 baseEnd_1563041 := by
    simpa [prefixWord, tailWord_1563041, baseEnd_1563041] using wordTrace_append hprefix tailTrace_1563041
  have hstable : (prefixWord ++ tailWord_1563041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563041).length < 2 ^ (prefixWord ++ tailWord_1563041).sum := by decide
  have hdescent : baseEnd_1563041 < baseStart_1563041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563106 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1563106 : Nat := 118140960795 + 1563106 * 2 ^ 59
def prefixEnd_1563106 : Nat := 4983230072969 + 3 ^ 40 * 1563106 * 2
def baseEnd_1563106 : Nat := 356722085300829588571739

theorem tailTrace_1563106 : CollatzResearch.WordTrace tailWord_1563106 prefixEnd_1563106 356722085300829588571739 := by
  unfold tailWord_1563106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252789868785348524089293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38007439650094262730904781 14252789868785348524089293)
  ·
    refine ⟨5344796200794505696533485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14252789868785348524089293 5344796200794505696533485)
    ·
      refine ⟨2004298575297939636200057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5344796200794505696533485 2004298575297939636200057)
      ·
        refine ⟨1503223931473454727150043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2004298575297939636200057 1503223931473454727150043)
        ·
          refine ⟨2254835897210182090725065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503223931473454727150043 2254835897210182090725065)
          ·
            refine ⟨1691126922907636568043799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254835897210182090725065 1691126922907636568043799)
            ·
              refine ⟨2536690384361454852065699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691126922907636568043799 2536690384361454852065699)
              ·
                refine ⟨3805035576542182278098549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536690384361454852065699 3805035576542182278098549)
                ·
                  refine ⟨356722085300829588571739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3805035576542182278098549 356722085300829588571739)
                  ·
                    rfl

theorem cell21_1563106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1563106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563106 prefixEnd_1563106 := by exact prefixLift 1563106
  have htrace : WordTrace (prefixWord ++ tailWord_1563106) baseStart_1563106 baseEnd_1563106 := by
    simpa [prefixWord, tailWord_1563106, baseEnd_1563106] using wordTrace_append hprefix tailTrace_1563106
  have hstable : (prefixWord ++ tailWord_1563106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563106).length < 2 ^ (prefixWord ++ tailWord_1563106).sum := by decide
  have hdescent : baseEnd_1563106 < baseStart_1563106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563117 : List Nat := [1, 5, 1, 3, 1, 2, 2, 6]
def baseStart_1563117 : Nat := 118140960795 + 1563117 * 2 ^ 59
def prefixEnd_1563117 : Nat := 4983230072969 + 3 ^ 40 * 1563117 * 2
def baseEnd_1563117 : Nat := 118908198550232004629461

theorem tailTrace_1563117 : CollatzResearch.WordTrace tailWord_1563117 prefixEnd_1563117 118908198550232004629461 := by
  unfold tailWord_1563117
  simp only [CollatzResearch.WordTrace]
  refine ⟨57011560678101542975007605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38007707118734361983338403 57011560678101542975007605)
  ·
    refine ⟨5344833813572019653906963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57011560678101542975007605 5344833813572019653906963)
    ·
      refine ⟨8017250720358029480860445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5344833813572019653906963 8017250720358029480860445)
      ·
        refine ⟨3006469020134261055322667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8017250720358029480860445 3006469020134261055322667)
        ·
          refine ⟨4509703530201391582984001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006469020134261055322667 4509703530201391582984001)
          ·
            refine ⟨3382277647651043687238001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4509703530201391582984001 3382277647651043687238001)
            ·
              refine ⟨2536708235738282765428501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3382277647651043687238001 2536708235738282765428501)
              ·
                refine ⟨118908198550232004629461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2536708235738282765428501 118908198550232004629461)
                ·
                  rfl

theorem cell21_1563117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 6].length) (baseStart_1563117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563117 prefixEnd_1563117 := by exact prefixLift 1563117
  have htrace : WordTrace (prefixWord ++ tailWord_1563117) baseStart_1563117 baseEnd_1563117 := by
    simpa [prefixWord, tailWord_1563117, baseEnd_1563117] using wordTrace_append hprefix tailTrace_1563117
  have hstable : (prefixWord ++ tailWord_1563117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563117).length < 2 ^ (prefixWord ++ tailWord_1563117).sum := by decide
  have hdescent : baseEnd_1563117 < baseStart_1563117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563165 : List Nat := [1, 4, 2, 2, 1, 2, 4, 2, 3]
def baseStart_1563165 : Nat := 118140960795 + 1563165 * 2 ^ 59
def prefixEnd_1563165 : Nat := 4983230072969 + 3 ^ 40 * 1563165 * 2
def baseEnd_1563165 : Nat := 356735549904658597088285

theorem tailTrace_1563165 : CollatzResearch.WordTrace tailWord_1563165 prefixEnd_1563165 356735549904658597088285 := by
  unfold tailWord_1563165
  simp only [CollatzResearch.WordTrace]
  refine ⟨57013311381927647172754949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38008874254618431448503299 57013311381927647172754949)
  ·
    refine ⟨10689995884111433844891553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57013311381927647172754949 10689995884111433844891553)
    ·
      refine ⟨8017496913083575383668665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10689995884111433844891553 8017496913083575383668665)
      ·
        refine ⟨6013122684812681537751499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8017496913083575383668665 6013122684812681537751499)
        ·
          refine ⟨9019684027219022306627249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6013122684812681537751499 9019684027219022306627249)
          ·
            refine ⟨6764763020414266729970437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9019684027219022306627249 6764763020414266729970437)
            ·
              refine ⟨1268393066327675011869457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6764763020414266729970437 1268393066327675011869457)
              ·
                refine ⟨951294799745756258902093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268393066327675011869457 951294799745756258902093)
                ·
                  refine ⟨356735549904658597088285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951294799745756258902093 356735549904658597088285)
                  ·
                    rfl

theorem cell21_1563165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_1563165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563165 prefixEnd_1563165 := by exact prefixLift 1563165
  have htrace : WordTrace (prefixWord ++ tailWord_1563165) baseStart_1563165 baseEnd_1563165 := by
    simpa [prefixWord, tailWord_1563165, baseEnd_1563165] using wordTrace_append hprefix tailTrace_1563165
  have hstable : (prefixWord ++ tailWord_1563165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563165).length < 2 ^ (prefixWord ++ tailWord_1563165).sum := by decide
  have hdescent : baseEnd_1563165 < baseStart_1563165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563230 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1563230 : Nat := 118140960795 + 1563230 * 2 ^ 59
def prefixEnd_1563230 : Nat := 4983230072969 + 3 ^ 40 * 1563230 * 2
def baseEnd_1563230 : Nat := 356750383790232928504819

theorem tailTrace_1563230 : CollatzResearch.WordTrace tailWord_1563230 prefixEnd_1563230 356750383790232928504819 := by
  unfold tailWord_1563230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126960265836520409233893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38010454751128108849247429 7126960265836520409233893)
  ·
    refine ⟨1336305049844347576731355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7126960265836520409233893 1336305049844347576731355)
    ·
      refine ⟨2004457574766521365097033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336305049844347576731355 2004457574766521365097033)
      ·
        refine ⟨1503343181074891023822775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2004457574766521365097033 1503343181074891023822775)
        ·
          refine ⟨2255014771612336535734163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503343181074891023822775 2255014771612336535734163)
          ·
            refine ⟨3382522157418504803601245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255014771612336535734163 3382522157418504803601245)
            ·
              refine ⟨1268445809031939301350467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3382522157418504803601245 1268445809031939301350467)
              ·
                refine ⟨1902668713547908952025701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268445809031939301350467 1902668713547908952025701)
                ·
                  refine ⟨356750383790232928504819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1902668713547908952025701 356750383790232928504819)
                  ·
                    rfl

theorem cell21_1563230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1563230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563230 prefixEnd_1563230 := by exact prefixLift 1563230
  have htrace : WordTrace (prefixWord ++ tailWord_1563230) baseStart_1563230 baseEnd_1563230 := by
    simpa [prefixWord, tailWord_1563230, baseEnd_1563230] using wordTrace_append hprefix tailTrace_1563230
  have hstable : (prefixWord ++ tailWord_1563230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563230).length < 2 ^ (prefixWord ++ tailWord_1563230).sum := by decide
  have hdescent : baseEnd_1563230 < baseStart_1563230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563235 : List Nat := [1, 1, 1, 5, 1, 2, 2, 8]
def baseStart_1563235 : Nat := 118140960795 + 1563235 * 2 ^ 59
def prefixEnd_1563235 : Nat := 4983230072969 + 3 ^ 40 * 1563235 * 2
def baseEnd_1563235 : Nat := 118917174952784676973825

theorem tailTrace_1563235 : CollatzResearch.WordTrace tailWord_1563235 prefixEnd_1563235 118917174952784676973825 := by
  unfold tailWord_1563235
  simp only [CollatzResearch.WordTrace]
  refine ⟨57015864491674049127803159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38010576327782699418535439 57015864491674049127803159)
  ·
    refine ⟨85523796737511073691704739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57015864491674049127803159 85523796737511073691704739)
    ·
      refine ⟨128285695106266610537557109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85523796737511073691704739 128285695106266610537557109)
      ·
        refine ⟨12026783916212494737895979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128285695106266610537557109 12026783916212494737895979)
        ·
          refine ⟨18040175874318742106843969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12026783916212494737895979 18040175874318742106843969)
          ·
            refine ⟨13530131905739056580132977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18040175874318742106843969 13530131905739056580132977)
            ·
              refine ⟨10147598929304292435099733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13530131905739056580132977 10147598929304292435099733)
              ·
                refine ⟨118917174952784676973825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10147598929304292435099733 118917174952784676973825)
                ·
                  rfl

theorem cell21_1563235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 8].length) (baseStart_1563235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563235 prefixEnd_1563235 := by exact prefixLift 1563235
  have htrace : WordTrace (prefixWord ++ tailWord_1563235) baseStart_1563235 baseEnd_1563235 := by
    simpa [prefixWord, tailWord_1563235, baseEnd_1563235] using wordTrace_append hprefix tailTrace_1563235
  have hstable : (prefixWord ++ tailWord_1563235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563235).length < 2 ^ (prefixWord ++ tailWord_1563235).sum := by decide
  have hdescent : baseEnd_1563235 < baseStart_1563235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563311 : List Nat := [1, 1, 2, 1, 2, 5, 2, 7]
def baseStart_1563311 : Nat := 118140960795 + 1563311 * 2 ^ 59
def prefixEnd_1563311 : Nat := 4983230072969 + 3 ^ 40 * 1563311 * 2
def baseEnd_1563311 : Nat := 118922956364598262551551

theorem tailTrace_1563311 : CollatzResearch.WordTrace tailWord_1563311 prefixEnd_1563311 118922956364598262551551 := by
  unfold tailWord_1563311
  simp only [CollatzResearch.WordTrace]
  refine ⟨57018636439398714107569787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38012424292932476071713191 57018636439398714107569787)
  ·
    refine ⟨85527954659098071161354681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57018636439398714107569787 85527954659098071161354681)
    ·
      refine ⟨64145965994323553371016011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85527954659098071161354681 64145965994323553371016011)
      ·
        refine ⟨96218948991485330056524017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64145965994323553371016011 96218948991485330056524017)
        ·
          refine ⟨72164211743613997542393013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96218948991485330056524017 72164211743613997542393013)
          ·
            refine ⟨6765394850963812269599345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72164211743613997542393013 6765394850963812269599345)
            ·
              refine ⟨5074046138222859202199509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6765394850963812269599345 5074046138222859202199509)
              ·
                refine ⟨118922956364598262551551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5074046138222859202199509 118922956364598262551551)
                ·
                  rfl

theorem cell21_1563311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 7].length) (baseStart_1563311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563311 prefixEnd_1563311 := by exact prefixLift 1563311
  have htrace : WordTrace (prefixWord ++ tailWord_1563311) baseStart_1563311 baseEnd_1563311 := by
    simpa [prefixWord, tailWord_1563311, baseEnd_1563311] using wordTrace_append hprefix tailTrace_1563311
  have hstable : (prefixWord ++ tailWord_1563311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563311).length < 2 ^ (prefixWord ++ tailWord_1563311).sum := by decide
  have hdescent : baseEnd_1563311 < baseStart_1563311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563373 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1563373 : Nat := 118140960795 + 1563373 * 2 ^ 59
def prefixEnd_1563373 : Nat := 4983230072969 + 3 ^ 40 * 1563373 * 2
def baseEnd_1563373 : Nat := 356783018338496457621193

theorem tailTrace_1563373 : CollatzResearch.WordTrace tailWord_1563373 prefixEnd_1563373 356783018338496457621193 := by
  unfold tailWord_1563373
  simp only [CollatzResearch.WordTrace]
  refine ⟨57020897765174098696326773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38013931843449399130884515 57020897765174098696326773)
  ·
    refine ⟨5345709165485071752780635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57020897765174098696326773 5345709165485071752780635)
    ·
      refine ⟨8018563748227607629170953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5345709165485071752780635 8018563748227607629170953)
      ·
        refine ⟨6013922811170705721878215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8018563748227607629170953 6013922811170705721878215)
        ·
          refine ⟨9020884216756058582817323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6013922811170705721878215 9020884216756058582817323)
          ·
            refine ⟨13531326325134087874225985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9020884216756058582817323 13531326325134087874225985)
            ·
              refine ⟨10148494743850565905669489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13531326325134087874225985 10148494743850565905669489)
              ·
                refine ⟨7611371057887924429252117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10148494743850565905669489 7611371057887924429252117)
                ·
                  refine ⟨356783018338496457621193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7611371057887924429252117 356783018338496457621193)
                  ·
                    rfl

theorem cell21_1563373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1563373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563373 prefixEnd_1563373 := by exact prefixLift 1563373
  have htrace : WordTrace (prefixWord ++ tailWord_1563373) baseStart_1563373 baseEnd_1563373 := by
    simpa [prefixWord, tailWord_1563373, baseEnd_1563373] using wordTrace_append hprefix tailTrace_1563373
  have hstable : (prefixWord ++ tailWord_1563373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563373).length < 2 ^ (prefixWord ++ tailWord_1563373).sum := by decide
  have hdescent : baseEnd_1563373 < baseStart_1563373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563390 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1563390 : Nat := 118140960795 + 1563390 * 2 ^ 59
def prefixEnd_1563390 : Nat := 4983230072969 + 3 ^ 40 * 1563390 * 2
def baseEnd_1563390 : Nat := 356786897970108205837825

theorem tailTrace_1563390 : CollatzResearch.WordTrace tailWord_1563390 prefixEnd_1563390 356786897970108205837825 := by
  unfold tailWord_1563390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7127689725764063824961953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38014345204075007066463749 7127689725764063824961953)
  ·
    refine ⟨5345767294323047868721465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7127689725764063824961953 5345767294323047868721465)
    ·
      refine ⟨4009325470742285901541099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5345767294323047868721465 4009325470742285901541099)
      ·
        refine ⟨6013988206113428852311649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4009325470742285901541099 6013988206113428852311649)
        ·
          refine ⟨4510491154585071639233737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6013988206113428852311649 4510491154585071639233737)
          ·
            refine ⟨3382868365938803729425303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4510491154585071639233737 3382868365938803729425303)
            ·
              refine ⟨5074302548908205594137955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382868365938803729425303 5074302548908205594137955)
              ·
                refine ⟨7611453823362308391206933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074302548908205594137955 7611453823362308391206933)
                ·
                  refine ⟨356786897970108205837825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7611453823362308391206933 356786897970108205837825)
                  ·
                    rfl

theorem cell21_1563390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1563390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563390 prefixEnd_1563390 := by exact prefixLift 1563390
  have htrace : WordTrace (prefixWord ++ tailWord_1563390) baseStart_1563390 baseEnd_1563390 := by
    simpa [prefixWord, tailWord_1563390, baseEnd_1563390] using wordTrace_append hprefix tailTrace_1563390
  have hstable : (prefixWord ++ tailWord_1563390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563390).length < 2 ^ (prefixWord ++ tailWord_1563390).sum := by decide
  have hdescent : baseEnd_1563390 < baseStart_1563390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563418 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1563418 : Nat := 118140960795 + 1563418 * 2 ^ 59
def prefixEnd_1563418 : Nat := 4983230072969 + 3 ^ 40 * 1563418 * 2
def baseEnd_1563418 : Nat := 356793287951586379371101

theorem tailTrace_1563418 : CollatzResearch.WordTrace tailWord_1563418 prefixEnd_1563418 356793287951586379371101 := by
  unfold tailWord_1563418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14255634762502767845428727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38015026033340714254476605 14255634762502767845428727)
  ·
    refine ⟨21383452143754151768143091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14255634762502767845428727 21383452143754151768143091)
    ·
      refine ⟨32075178215631227652214637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21383452143754151768143091 32075178215631227652214637)
      ·
        refine ⟨12028191830861710369580489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32075178215631227652214637 12028191830861710369580489)
        ·
          refine ⟨9021143873146282777185367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12028191830861710369580489 9021143873146282777185367)
          ·
            refine ⟨13531715809719424165778051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9021143873146282777185367 13531715809719424165778051)
            ·
              refine ⟨20297573714579136248667077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13531715809719424165778051 20297573714579136248667077)
              ·
                refine ⟨3805795071483588046625077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20297573714579136248667077 3805795071483588046625077)
                ·
                  refine ⟨356793287951586379371101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3805795071483588046625077 356793287951586379371101)
                  ·
                    rfl

theorem cell21_1563418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1563418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563418 prefixEnd_1563418 := by exact prefixLift 1563418
  have htrace : WordTrace (prefixWord ++ tailWord_1563418) baseStart_1563418 baseEnd_1563418 := by
    simpa [prefixWord, tailWord_1563418, baseEnd_1563418] using wordTrace_append hprefix tailTrace_1563418
  have hstable : (prefixWord ++ tailWord_1563418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563418).length < 2 ^ (prefixWord ++ tailWord_1563418).sum := by decide
  have hdescent : baseEnd_1563418 < baseStart_1563418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563421 : List Nat := [1, 4, 2, 4, 1, 1, 1, 7]
def baseStart_1563421 : Nat := 118140960795 + 1563421 * 2 ^ 59
def prefixEnd_1563421 : Nat := 4983230072969 + 3 ^ 40 * 1563421 * 2
def baseEnd_1563421 : Nat := 118931324197486346940365

theorem tailTrace_1563421 : CollatzResearch.WordTrace tailWord_1563421 prefixEnd_1563421 118931324197486346940365 := by
  unfold tailWord_1563421
  simp only [CollatzResearch.WordTrace]
  refine ⟨57022648469000202894074117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38015098979333468596049411 57022648469000202894074117)
  ·
    refine ⟨10691746587937538042638897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57022648469000202894074117 10691746587937538042638897)
    ·
      refine ⟨8018809940953153531979173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10691746587937538042638897 8018809940953153531979173)
      ·
        refine ⟨1503526863928716287246095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8018809940953153531979173 1503526863928716287246095)
        ·
          refine ⟨2255290295893074430869143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503526863928716287246095 2255290295893074430869143)
          ·
            refine ⟨3382935443839611646303715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255290295893074430869143 3382935443839611646303715)
            ·
              refine ⟨5074403165759417469455573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382935443839611646303715 5074403165759417469455573)
              ·
                refine ⟨118931324197486346940365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5074403165759417469455573 118931324197486346940365)
                ·
                  rfl

theorem cell21_1563421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 7].length) (baseStart_1563421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563421 prefixEnd_1563421 := by exact prefixLift 1563421
  have htrace : WordTrace (prefixWord ++ tailWord_1563421) baseStart_1563421 baseEnd_1563421 := by
    simpa [prefixWord, tailWord_1563421, baseEnd_1563421] using wordTrace_append hprefix tailTrace_1563421
  have hstable : (prefixWord ++ tailWord_1563421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563421).length < 2 ^ (prefixWord ++ tailWord_1563421).sum := by decide
  have hdescent : baseEnd_1563421 < baseStart_1563421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563525 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 4]
def baseStart_1563525 : Nat := 118140960795 + 1563525 * 2 ^ 59
def prefixEnd_1563525 : Nat := 4983230072969 + 3 ^ 40 * 1563525 * 2
def baseEnd_1563525 : Nat := 356817706809377971087549

theorem tailTrace_1563525 : CollatzResearch.WordTrace tailWord_1563525 prefixEnd_1563525 356817706809377971087549 := by
  unfold tailWord_1563525
  simp only [CollatzResearch.WordTrace]
  refine ⟨57026441660623428655860029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38017627773748952437240019 57026441660623428655860029)
  ·
    refine ⟨21384915622733785745947511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57026441660623428655860029 21384915622733785745947511)
    ·
      refine ⟨32077373434100678618921267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21384915622733785745947511 32077373434100678618921267)
      ·
        refine ⟨48116060151151017928381901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32077373434100678618921267 48116060151151017928381901)
        ·
          refine ⟨18043522556681631723143213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48116060151151017928381901 18043522556681631723143213)
          ·
            refine ⟨6766320958755611896178705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18043522556681631723143213 6766320958755611896178705)
            ·
              refine ⟨5074740719066708922134029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6766320958755611896178705 5074740719066708922134029)
              ·
                refine ⟨1903027769650015845800261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5074740719066708922134029 1903027769650015845800261)
                ·
                  refine ⟨356817706809377971087549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1903027769650015845800261 356817706809377971087549)
                  ·
                    rfl

theorem cell21_1563525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_1563525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563525 prefixEnd_1563525 := by exact prefixLift 1563525
  have htrace : WordTrace (prefixWord ++ tailWord_1563525) baseStart_1563525 baseEnd_1563525 := by
    simpa [prefixWord, tailWord_1563525, baseEnd_1563525] using wordTrace_append hprefix tailTrace_1563525
  have hstable : (prefixWord ++ tailWord_1563525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563525).length < 2 ^ (prefixWord ++ tailWord_1563525).sum := by decide
  have hdescent : baseEnd_1563525 < baseStart_1563525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563559 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 4]
def baseStart_1563559 : Nat := 118140960795 + 1563559 * 2 ^ 59
def prefixEnd_1563559 : Nat := 4983230072969 + 3 ^ 40 * 1563559 * 2
def baseEnd_1563559 : Nat := 356825466072601467520813

theorem tailTrace_1563559 : CollatzResearch.WordTrace tailWord_1563559 prefixEnd_1563559 356825466072601467520813 := by
  unfold tailWord_1563559
  simp only [CollatzResearch.WordTrace]
  refine ⟨57027681742500252462597731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38018454495000168308398487 57027681742500252462597731)
  ·
    refine ⟨85541522613750378693896597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57027681742500252462597731 85541522613750378693896597)
    ·
      refine ⟨4009758872519549001276403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85541522613750378693896597 4009758872519549001276403)
      ·
        refine ⟨6014638308779323501914605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4009758872519549001276403 6014638308779323501914605)
        ·
          refine ⟨2255489365792246313217977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6014638308779323501914605 2255489365792246313217977)
          ·
            refine ⟨1691617024344184734913483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2255489365792246313217977 1691617024344184734913483)
            ·
              refine ⟨2537425536516277102370225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691617024344184734913483 2537425536516277102370225)
              ·
                refine ⟨1903069152387207826777669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537425536516277102370225 1903069152387207826777669)
                ·
                  refine ⟨356825466072601467520813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1903069152387207826777669 356825466072601467520813)
                  ·
                    rfl

theorem cell21_1563559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 4].length) (baseStart_1563559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563559 prefixEnd_1563559 := by exact prefixLift 1563559
  have htrace : WordTrace (prefixWord ++ tailWord_1563559) baseStart_1563559 baseEnd_1563559 := by
    simpa [prefixWord, tailWord_1563559, baseEnd_1563559] using wordTrace_append hprefix tailTrace_1563559
  have hstable : (prefixWord ++ tailWord_1563559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563559).length < 2 ^ (prefixWord ++ tailWord_1563559).sum := by decide
  have hdescent : baseEnd_1563559 < baseStart_1563559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563604 : List Nat := [2, 4, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1563604 : Nat := 118140960795 + 1563604 * 2 ^ 59
def prefixEnd_1563604 : Nat := 4983230072969 + 3 ^ 40 * 1563604 * 2
def baseEnd_1563604 : Nat := 356835735685691389270721

theorem tailTrace_1563604 : CollatzResearch.WordTrace tailWord_1563604 prefixEnd_1563604 356835735685691389270721 := by
  unfold tailWord_1563604
  simp only [CollatzResearch.WordTrace]
  refine ⟨28514661513668612573992933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38019548684891483431990577 28514661513668612573992933)
  ·
    refine ⟨5346499033812864857623675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28514661513668612573992933 5346499033812864857623675)
    ·
      refine ⟨8019748550719297286435513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5346499033812864857623675 8019748550719297286435513)
      ·
        refine ⟨6014811413039472964826635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8019748550719297286435513 6014811413039472964826635)
        ·
          refine ⟨9022217119559209447239953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6014811413039472964826635 9022217119559209447239953)
          ·
            refine ⟨6766662839669407085429965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9022217119559209447239953 6766662839669407085429965)
            ·
              refine ⟨2537498564876027657036237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6766662839669407085429965 2537498564876027657036237)
              ·
                refine ⟨951561961828510371388589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2537498564876027657036237 951561961828510371388589)
                ·
                  refine ⟨356835735685691389270721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951561961828510371388589 356835735685691389270721)
                  ·
                    rfl

theorem cell21_1563604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1563604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563604 prefixEnd_1563604 := by exact prefixLift 1563604
  have htrace : WordTrace (prefixWord ++ tailWord_1563604) baseStart_1563604 baseEnd_1563604 := by
    simpa [prefixWord, tailWord_1563604, baseEnd_1563604] using wordTrace_append hprefix tailTrace_1563604
  have hstable : (prefixWord ++ tailWord_1563604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563604).length < 2 ^ (prefixWord ++ tailWord_1563604).sum := by decide
  have hdescent : baseEnd_1563604 < baseStart_1563604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563618 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1563618 : Nat := 118140960795 + 1563618 * 2 ^ 59
def prefixEnd_1563618 : Nat := 4983230072969 + 3 ^ 40 * 1563618 * 2
def baseEnd_1563618 : Nat := 356838930676430476037359

theorem tailTrace_1563618 : CollatzResearch.WordTrace tailWord_1563618 prefixEnd_1563618 356838930676430476037359 := by
  unfold tailWord_1563618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257458412321626384748877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38019889099524337025997005 14257458412321626384748877)
  ·
    refine ⟨5346546904620609894280829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14257458412321626384748877 5346546904620609894280829)
    ·
      refine ⟨2004955089232728710355311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5346546904620609894280829 2004955089232728710355311)
      ·
        refine ⟨3007432633849093065532967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004955089232728710355311 3007432633849093065532967)
        ·
          refine ⟨4511148950773639598299451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007432633849093065532967 4511148950773639598299451)
          ·
            refine ⟨6766723426160459397449177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4511148950773639598299451 6766723426160459397449177)
            ·
              refine ⟨5075042569620344548086883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6766723426160459397449177 5075042569620344548086883)
              ·
                refine ⟨7612563854430516822130325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5075042569620344548086883 7612563854430516822130325)
                ·
                  refine ⟨356838930676430476037359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7612563854430516822130325 356838930676430476037359)
                  ·
                    rfl

theorem cell21_1563618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1563618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563618 prefixEnd_1563618 := by exact prefixLift 1563618
  have htrace : WordTrace (prefixWord ++ tailWord_1563618) baseStart_1563618 baseEnd_1563618 := by
    simpa [prefixWord, tailWord_1563618, baseEnd_1563618] using wordTrace_append hprefix tailTrace_1563618
  have hstable : (prefixWord ++ tailWord_1563618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563618).length < 2 ^ (prefixWord ++ tailWord_1563618).sum := by decide
  have hdescent : baseEnd_1563618 < baseStart_1563618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563621 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 5]
def baseStart_1563621 : Nat := 118140960795 + 1563621 * 2 ^ 59
def prefixEnd_1563621 : Nat := 4983230072969 + 3 ^ 40 * 1563621 * 2
def baseEnd_1563621 : Nat := 356839615317303137487353

theorem tailTrace_1563621 : CollatzResearch.WordTrace tailWord_1563621 prefixEnd_1563621 356839615317303137487353 := by
  unfold tailWord_1563621
  simp only [CollatzResearch.WordTrace]
  refine ⟨57029943068275637051354717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38019962045517091367569811 57029943068275637051354717)
  ·
    refine ⟨21386228650603363894258019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57029943068275637051354717 21386228650603363894258019)
    ·
      refine ⟨32079342975905045841387029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21386228650603363894258019 32079342975905045841387029)
      ·
        refine ⟨1503719201995549023815017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32079342975905045841387029 1503719201995549023815017)
        ·
          refine ⟨1127789401496661767861263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503719201995549023815017 1127789401496661767861263)
          ·
            refine ⟨1691684102244992651791895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127789401496661767861263 1691684102244992651791895)
            ·
              refine ⟨2537526153367488977687843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691684102244992651791895 2537526153367488977687843)
              ·
                refine ⟨3806289230051233466531765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537526153367488977687843 3806289230051233466531765)
                ·
                  refine ⟨356839615317303137487353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3806289230051233466531765 356839615317303137487353)
                  ·
                    rfl

theorem cell21_1563621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_1563621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563621 prefixEnd_1563621 := by exact prefixLift 1563621
  have htrace : WordTrace (prefixWord ++ tailWord_1563621) baseStart_1563621 baseEnd_1563621 := by
    simpa [prefixWord, tailWord_1563621, baseEnd_1563621] using wordTrace_append hprefix tailTrace_1563621
  have hstable : (prefixWord ++ tailWord_1563621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563621).length < 2 ^ (prefixWord ++ tailWord_1563621).sum := by decide
  have hdescent : baseEnd_1563621 < baseStart_1563621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563666 : List Nat := [3, 2, 5, 1, 2, 8]
def baseStart_1563666 : Nat := 118140960795 + 1563666 * 2 ^ 59
def prefixEnd_1563666 : Nat := 4983230072969 + 3 ^ 40 * 1563666 * 2
def baseEnd_1563666 : Nat := 13216662404829372564343

theorem tailTrace_1563666 : CollatzResearch.WordTrace tailWord_1563666 prefixEnd_1563666 13216662404829372564343 := by
  unfold tailWord_1563666
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257896088278152434185713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38021056235408406491161901 14257896088278152434185713)
  ·
    refine ⟨10693422066208614325639285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14257896088278152434185713 10693422066208614325639285)
    ·
      refine ⟨1002508318707057593028683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10693422066208614325639285 1002508318707057593028683)
      ·
        refine ⟨1503762478060586389543025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002508318707057593028683 1503762478060586389543025)
        ·
          refine ⟨1127821858545439792157269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503762478060586389543025 1127821858545439792157269)
          ·
            refine ⟨13216662404829372564343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1127821858545439792157269 13216662404829372564343)
            ·
              rfl

theorem cell21_1563666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 8].length) (baseStart_1563666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563666 prefixEnd_1563666 := by exact prefixLift 1563666
  have htrace : WordTrace (prefixWord ++ tailWord_1563666) baseStart_1563666 baseEnd_1563666 := by
    simpa [prefixWord, tailWord_1563666, baseEnd_1563666] using wordTrace_append hprefix tailTrace_1563666
  have hstable : (prefixWord ++ tailWord_1563666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563666).length < 2 ^ (prefixWord ++ tailWord_1563666).sum := by decide
  have hdescent : baseEnd_1563666 < baseStart_1563666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563708 : List Nat := [2, 2, 2, 2, 2, 3, 3, 5]
def baseStart_1563708 : Nat := 118140960795 + 1563708 * 2 ^ 59
def prefixEnd_1563708 : Nat := 4983230072969 + 3 ^ 40 * 1563708 * 2
def baseEnd_1563708 : Nat := 118953156634203439845725

theorem tailTrace_1563708 : CollatzResearch.WordTrace tailWord_1563708 prefixEnd_1563708 118953156634203439845725 := by
  unfold tailWord_1563708
  simp only [CollatzResearch.WordTrace]
  refine ⟨28516558109480225454885889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38022077479306967273181185 28516558109480225454885889)
  ·
    refine ⟨21387418582110169091164417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28516558109480225454885889 21387418582110169091164417)
    ·
      refine ⟨16040563936582626818373313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21387418582110169091164417 16040563936582626818373313)
      ·
        refine ⟨12030422952436970113779985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16040563936582626818373313 12030422952436970113779985)
        ·
          refine ⟨9022817214327727585334989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12030422952436970113779985 9022817214327727585334989)
          ·
            refine ⟨3383556455372897844500621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9022817214327727585334989 3383556455372897844500621)
            ·
              refine ⟨1268833670764836691687733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3383556455372897844500621 1268833670764836691687733)
              ·
                refine ⟨118953156634203439845725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1268833670764836691687733 118953156634203439845725)
                ·
                  rfl

theorem cell21_1563708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_1563708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563708 prefixEnd_1563708 := by exact prefixLift 1563708
  have htrace : WordTrace (prefixWord ++ tailWord_1563708) baseStart_1563708 baseEnd_1563708 := by
    simpa [prefixWord, tailWord_1563708, baseEnd_1563708] using wordTrace_append hprefix tailTrace_1563708
  have hstable : (prefixWord ++ tailWord_1563708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563708).length < 2 ^ (prefixWord ++ tailWord_1563708).sum := by decide
  have hdescent : baseEnd_1563708 < baseStart_1563708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563736 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_1563736 : Nat := 118140960795 + 1563736 * 2 ^ 59
def prefixEnd_1563736 : Nat := 4983230072969 + 3 ^ 40 * 1563736 * 2
def baseEnd_1563736 : Nat := 356865859884088493070451

theorem tailTrace_1563736 : CollatzResearch.WordTrace tailWord_1563736 prefixEnd_1563736 356865859884088493070451 := by
  unfold tailWord_1563736
  simp only [CollatzResearch.WordTrace]
  refine ⟨28517068731429505845895531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38022758308572674461194041 28517068731429505845895531)
  ·
    refine ⟨42775603097144258768843297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28517068731429505845895531 42775603097144258768843297)
    ·
      refine ⟨32081702322858194076632473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42775603097144258768843297 32081702322858194076632473)
      ·
        refine ⟨24061276742143645557474355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32081702322858194076632473 24061276742143645557474355)
        ·
          refine ⟨36091915113215468336211533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24061276742143645557474355 36091915113215468336211533)
          ·
            refine ⟨13534468167455800626079325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36091915113215468336211533 13534468167455800626079325)
            ·
              refine ⟨5075425562795925234779747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13534468167455800626079325 5075425562795925234779747)
              ·
                refine ⟨7613138344193887852169621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5075425562795925234779747 7613138344193887852169621)
                ·
                  refine ⟨356865859884088493070451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7613138344193887852169621 356865859884088493070451)
                  ·
                    rfl

theorem cell21_1563736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_1563736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563736 prefixEnd_1563736 := by exact prefixLift 1563736
  have htrace : WordTrace (prefixWord ++ tailWord_1563736) baseStart_1563736 baseEnd_1563736 := by
    simpa [prefixWord, tailWord_1563736, baseEnd_1563736] using wordTrace_append hprefix tailTrace_1563736
  have hstable : (prefixWord ++ tailWord_1563736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563736).length < 2 ^ (prefixWord ++ tailWord_1563736).sum := by decide
  have hdescent : baseEnd_1563736 < baseStart_1563736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563784 : List Nat := [2, 1, 3, 4, 2, 2, 7]
def baseStart_1563784 : Nat := 118140960795 + 1563784 * 2 ^ 59
def prefixEnd_1563784 : Nat := 4983230072969 + 3 ^ 40 * 1563784 * 2
def baseEnd_1563784 : Nat := 39652979348672341807817

theorem tailTrace_1563784 : CollatzResearch.WordTrace tailWord_1563784 prefixEnd_1563784 39652979348672341807817 := by
  unfold tailWord_1563784
  simp only [CollatzResearch.WordTrace]
  refine ⟨28517944083342557944769203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38023925444456743926358937 28517944083342557944769203)
  ·
    refine ⟨42776916125013836917153805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28517944083342557944769203 42776916125013836917153805)
    ·
      refine ⟨16041343546880188843932677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42776916125013836917153805 16041343546880188843932677)
      ·
        refine ⟨3007751915040035408237377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16041343546880188843932677 3007751915040035408237377)
        ·
          refine ⟨2255813936280026556178033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3007751915040035408237377 2255813936280026556178033)
          ·
            refine ⟨1691860452210019917133525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2255813936280026556178033 1691860452210019917133525)
            ·
              refine ⟨39652979348672341807817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1691860452210019917133525 39652979348672341807817)
              ·
                rfl

theorem cell21_1563784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 7].length) (baseStart_1563784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563784 prefixEnd_1563784 := by exact prefixLift 1563784
  have htrace : WordTrace (prefixWord ++ tailWord_1563784) baseStart_1563784 baseEnd_1563784 := by
    simpa [prefixWord, tailWord_1563784, baseEnd_1563784] using wordTrace_append hprefix tailTrace_1563784
  have hstable : (prefixWord ++ tailWord_1563784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563784).length < 2 ^ (prefixWord ++ tailWord_1563784).sum := by decide
  have hdescent : baseEnd_1563784 < baseStart_1563784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563857 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 5]
def baseStart_1563857 : Nat := 118140960795 + 1563857 * 2 ^ 59
def prefixEnd_1563857 : Nat := 4983230072969 + 3 ^ 40 * 1563857 * 2
def baseEnd_1563857 : Nat := 356893473732619171553537

theorem tailTrace_1563857 : CollatzResearch.WordTrace tailWord_1563857 prefixEnd_1563857 356893473732619171553537 := by
  unfold tailWord_1563857
  simp only [CollatzResearch.WordTrace]
  refine ⟨57038550695420649356945825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38025700463613766237963883 57038550695420649356945825)
  ·
    refine ⟨42778913021565487017709369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57038550695420649356945825 42778913021565487017709369)
    ·
      refine ⟨32084184766174115263282027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42778913021565487017709369 32084184766174115263282027)
      ·
        refine ⟨48126277149261172894923041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32084184766174115263282027 48126277149261172894923041)
        ·
          refine ⟨36094707861945879671192281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48126277149261172894923041 36094707861945879671192281)
          ·
            refine ⟨27071030896459409753394211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36094707861945879671192281 27071030896459409753394211)
            ·
              refine ⟨40606546344689114630091317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27071030896459409753394211 40606546344689114630091317)
              ·
                refine ⟨3806863719814604496571061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40606546344689114630091317 3806863719814604496571061)
                ·
                  refine ⟨356893473732619171553537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3806863719814604496571061 356893473732619171553537)
                  ·
                    rfl

theorem cell21_1563857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_1563857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563857 prefixEnd_1563857 := by exact prefixLift 1563857
  have htrace : WordTrace (prefixWord ++ tailWord_1563857) baseStart_1563857 baseEnd_1563857 := by
    simpa [prefixWord, tailWord_1563857, baseEnd_1563857] using wordTrace_append hprefix tailTrace_1563857
  have hstable : (prefixWord ++ tailWord_1563857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563857).length < 2 ^ (prefixWord ++ tailWord_1563857).sum := by decide
  have hdescent : baseEnd_1563857 < baseStart_1563857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563891 : List Nat := [1, 1, 1, 2, 2, 6, 2, 3, 3]
def baseStart_1563891 : Nat := 118140960795 + 1563891 * 2 ^ 59
def prefixEnd_1563891 : Nat := 4983230072969 + 3 ^ 40 * 1563891 * 2
def baseEnd_1563891 : Nat := 356901232995842667986801

theorem tailTrace_1563891 : CollatzResearch.WordTrace tailWord_1563891 prefixEnd_1563891 356901232995842667986801 := by
  unfold tailWord_1563891
  simp only [CollatzResearch.WordTrace]
  refine ⟨57039790777297473163683527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38026527184864982109122351 57039790777297473163683527)
  ·
    refine ⟨85559686165946209745525291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57039790777297473163683527 85559686165946209745525291)
    ·
      refine ⟨128339529248919314618287937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85559686165946209745525291 128339529248919314618287937)
      ·
        refine ⟨96254646936689485963715953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128339529248919314618287937 96254646936689485963715953)
        ·
          refine ⟨72190985202517114472786965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96254646936689485963715953 72190985202517114472786965)
          ·
            refine ⟨3383952431367989740911889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72190985202517114472786965 3383952431367989740911889)
            ·
              refine ⟨2537964323525992305683917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3383952431367989740911889 2537964323525992305683917)
              ·
                refine ⟨951736621322247114631469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2537964323525992305683917 951736621322247114631469)
                ·
                  refine ⟨356901232995842667986801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951736621322247114631469 356901232995842667986801)
                  ·
                    rfl

theorem cell21_1563891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 3].length) (baseStart_1563891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563891 prefixEnd_1563891 := by exact prefixLift 1563891
  have htrace : WordTrace (prefixWord ++ tailWord_1563891) baseStart_1563891 baseEnd_1563891 := by
    simpa [prefixWord, tailWord_1563891, baseEnd_1563891] using wordTrace_append hprefix tailTrace_1563891
  have hstable : (prefixWord ++ tailWord_1563891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563891).length < 2 ^ (prefixWord ++ tailWord_1563891).sum := by decide
  have hdescent : baseEnd_1563891 < baseStart_1563891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563905 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 4]
def baseStart_1563905 : Nat := 118140960795 + 1563905 * 2 ^ 59
def prefixEnd_1563905 : Nat := 4983230072969 + 3 ^ 40 * 1563905 * 2
def baseEnd_1563905 : Nat := 356904427986581754753439

theorem tailTrace_1563905 : CollatzResearch.WordTrace tailWord_1563905 prefixEnd_1563905 356904427986581754753439 := by
  unfold tailWord_1563905
  simp only [CollatzResearch.WordTrace]
  refine ⟨57040301399246753554693169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38026867599497835703128779 57040301399246753554693169)
  ·
    refine ⟨42780226049435065166019877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57040301399246753554693169 42780226049435065166019877)
    ·
      refine ⟨8021292384269074718628727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42780226049435065166019877 8021292384269074718628727)
      ·
        refine ⟨12031938576403612077943091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8021292384269074718628727 12031938576403612077943091)
        ·
          refine ⟨18047907864605418116914637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12031938576403612077943091 18047907864605418116914637)
          ·
            refine ⟨6767965449227031793842989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18047907864605418116914637 6767965449227031793842989)
            ·
              refine ⟨2537987043460136922691121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6767965449227031793842989 2537987043460136922691121)
              ·
                refine ⟨1903490282595102692018341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537987043460136922691121 1903490282595102692018341)
                ·
                  refine ⟨356904427986581754753439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1903490282595102692018341 356904427986581754753439)
                  ·
                    rfl

theorem cell21_1563905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_1563905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563905 prefixEnd_1563905 := by exact prefixLift 1563905
  have htrace : WordTrace (prefixWord ++ tailWord_1563905) baseStart_1563905 baseEnd_1563905 := by
    simpa [prefixWord, tailWord_1563905, baseEnd_1563905] using wordTrace_append hprefix tailTrace_1563905
  have hstable : (prefixWord ++ tailWord_1563905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563905).length < 2 ^ (prefixWord ++ tailWord_1563905).sum := by decide
  have hdescent : baseEnd_1563905 < baseStart_1563905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1563964 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_1563964 : Nat := 118140960795 + 1563964 * 2 ^ 59
def prefixEnd_1563964 : Nat := 4983230072969 + 3 ^ 40 * 1563964 * 2
def baseEnd_1563964 : Nat := 356917892590410763269985

theorem tailTrace_1563964 : CollatzResearch.WordTrace tailWord_1563964 prefixEnd_1563964 356917892590410763269985 := by
  unfold tailWord_1563964
  simp only [CollatzResearch.WordTrace]
  refine ⟨28521226653016503315545473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38028302204022004420727297 28521226653016503315545473)
  ·
    refine ⟨21390919989762377486659105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28521226653016503315545473 21390919989762377486659105)
    ·
      refine ⟨16043189992321783114994329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21390919989762377486659105 16043189992321783114994329)
      ·
        refine ⟨12032392494241337336245747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16043189992321783114994329 12032392494241337336245747)
        ·
          refine ⟨18048588741362006004368621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12032392494241337336245747 18048588741362006004368621)
          ·
            refine ⟨6768220778010752251638233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18048588741362006004368621 6768220778010752251638233)
            ·
              refine ⟨5076165583508064188728675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6768220778010752251638233 5076165583508064188728675)
              ·
                refine ⟨7614248375262096283093013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5076165583508064188728675 7614248375262096283093013)
                ·
                  refine ⟨356917892590410763269985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7614248375262096283093013 356917892590410763269985)
                  ·
                    rfl

theorem cell21_1563964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_1563964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1563964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1563964 prefixEnd_1563964 := by exact prefixLift 1563964
  have htrace : WordTrace (prefixWord ++ tailWord_1563964) baseStart_1563964 baseEnd_1563964 := by
    simpa [prefixWord, tailWord_1563964, baseEnd_1563964] using wordTrace_append hprefix tailTrace_1563964
  have hstable : (prefixWord ++ tailWord_1563964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1563964).length < 2 ^ (prefixWord ++ tailWord_1563964).sum := by decide
  have hdescent : baseEnd_1563964 < baseStart_1563964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1563964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564026 : List Nat := [3, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_1564026 : Nat := 118140960795 + 1564026 * 2 ^ 59
def prefixEnd_1564026 : Nat := 4983230072969 + 3 ^ 40 * 1564026 * 2
def baseEnd_1564026 : Nat := 356932041835112433236525

theorem tailTrace_1564026 : CollatzResearch.WordTrace tailWord_1564026 prefixEnd_1564026 356932041835112433236525 := by
  unfold tailWord_1564026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14261178657952097804961983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38029809754538927479898621 14261178657952097804961983)
  ·
    refine ⟨21391767986928146707442975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14261178657952097804961983 21391767986928146707442975)
    ·
      refine ⟨32087651980392220061164463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21391767986928146707442975 32087651980392220061164463)
      ·
        refine ⟨48131477970588330091746695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32087651980392220061164463 48131477970588330091746695)
        ·
          refine ⟨72197216955882495137620043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48131477970588330091746695 72197216955882495137620043)
          ·
            refine ⟨108295825433823742706430065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72197216955882495137620043 108295825433823742706430065)
            ·
              refine ⟨81221869075367807029822549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108295825433823742706430065 81221869075367807029822549)
              ·
                refine ⟨951818778226966488630733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 81221869075367807029822549 951818778226966488630733)
                ·
                  refine ⟨356932041835112433236525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951818778226966488630733 356932041835112433236525)
                  ·
                    rfl

theorem cell21_1564026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_1564026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564026 prefixEnd_1564026 := by exact prefixLift 1564026
  have htrace : WordTrace (prefixWord ++ tailWord_1564026) baseStart_1564026 baseEnd_1564026 := by
    simpa [prefixWord, tailWord_1564026, baseEnd_1564026] using wordTrace_append hprefix tailTrace_1564026
  have hstable : (prefixWord ++ tailWord_1564026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564026).length < 2 ^ (prefixWord ++ tailWord_1564026).sum := by decide
  have hdescent : baseEnd_1564026 < baseStart_1564026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564150 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1564150 : Nat := 118140960795 + 1564150 * 2 ^ 59
def prefixEnd_1564150 : Nat := 4983230072969 + 3 ^ 40 * 1564150 * 2
def baseEnd_1564150 : Nat := 356960340324515773169605

theorem tailTrace_1564150 : CollatzResearch.WordTrace tailWord_1564150 prefixEnd_1564150 356960340324515773169605 := by
  unfold tailWord_1564150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565577330209947524835119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38032824855572773598241269 3565577330209947524835119)
  ·
    refine ⟨5348365995314921287252679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3565577330209947524835119 5348365995314921287252679)
    ·
      refine ⟨8022548992972381930879019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5348365995314921287252679 8022548992972381930879019)
      ·
        refine ⟨12033823489458572896318529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8022548992972381930879019 12033823489458572896318529)
        ·
          refine ⟨9025367617093929672238897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12033823489458572896318529 9025367617093929672238897)
          ·
            refine ⟨6769025712820447254179173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9025367617093929672238897 6769025712820447254179173)
            ·
              refine ⟨1269192321153833860158595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6769025712820447254179173 1269192321153833860158595)
              ·
                refine ⟨1903788481730750790237893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269192321153833860158595 1903788481730750790237893)
                ·
                  refine ⟨356960340324515773169605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1903788481730750790237893 356960340324515773169605)
                  ·
                    rfl

theorem cell21_1564150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1564150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564150 prefixEnd_1564150 := by exact prefixLift 1564150
  have htrace : WordTrace (prefixWord ++ tailWord_1564150) baseStart_1564150 baseEnd_1564150 := by
    simpa [prefixWord, tailWord_1564150, baseEnd_1564150] using wordTrace_append hprefix tailTrace_1564150
  have hstable : (prefixWord ++ tailWord_1564150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564150).length < 2 ^ (prefixWord ++ tailWord_1564150).sum := by decide
  have hdescent : baseEnd_1564150 < baseStart_1564150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564195 : List Nat := [1, 1, 1, 4, 5, 1, 1, 4, 3]
def baseStart_1564195 : Nat := 118140960795 + 1564195 * 2 ^ 59
def prefixEnd_1564195 : Nat := 4983230072969 + 3 ^ 40 * 1564195 * 2
def baseEnd_1564195 : Nat := 356970609937605694919513

theorem tailTrace_1564195 : CollatzResearch.WordTrace tailWord_1564195 prefixEnd_1564195 356970609937605694919513 := by
  unfold tailWord_1564195
  simp only [CollatzResearch.WordTrace]
  refine ⟨57050878568196133082750039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38033919045464088721833359 57050878568196133082750039)
  ·
    refine ⟨85576317852294199624125059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57050878568196133082750039 85576317852294199624125059)
    ·
      refine ⟨128364476778441299436187589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85576317852294199624125059 128364476778441299436187589)
      ·
        refine ⟨24068339395957743644285173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128364476778441299436187589 24068339395957743644285173)
        ·
          refine ⟨2256406818371038466651735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24068339395957743644285173 2256406818371038466651735)
          ·
            refine ⟨3384610227556557699977603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256406818371038466651735 3384610227556557699977603)
            ·
              refine ⟨5076915341334836549966405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384610227556557699977603 5076915341334836549966405)
              ·
                refine ⟨951921626500281853118701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5076915341334836549966405 951921626500281853118701)
                ·
                  refine ⟨356970609937605694919513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 951921626500281853118701 356970609937605694919513)
                  ·
                    rfl

theorem cell21_1564195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 3].length) (baseStart_1564195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564195 prefixEnd_1564195 := by exact prefixLift 1564195
  have htrace : WordTrace (prefixWord ++ tailWord_1564195) baseStart_1564195 baseEnd_1564195 := by
    simpa [prefixWord, tailWord_1564195, baseEnd_1564195] using wordTrace_append hprefix tailTrace_1564195
  have hstable : (prefixWord ++ tailWord_1564195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564195).length < 2 ^ (prefixWord ++ tailWord_1564195).sum := by decide
  have hdescent : baseEnd_1564195 < baseStart_1564195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564223 : List Nat := [1, 1, 2, 2, 3, 4, 3, 5]
def baseStart_1564223 : Nat := 118140960795 + 1564223 * 2 ^ 59
def prefixEnd_1564223 : Nat := 4983230072969 + 3 ^ 40 * 1564223 * 2
def baseEnd_1564223 : Nat := 118992333306361289484263

theorem tailTrace_1564223 : CollatzResearch.WordTrace tailWord_1564223 prefixEnd_1564223 118992333306361289484263 := by
  unfold tailWord_1564223
  simp only [CollatzResearch.WordTrace]
  refine ⟨57051899812094693864769323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38034599874729795909846215 57051899812094693864769323)
  ·
    refine ⟨85577849718142040797153985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57051899812094693864769323 85577849718142040797153985)
    ·
      refine ⟨64183387288606530597865489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85577849718142040797153985 64183387288606530597865489)
      ·
        refine ⟨48137540466454897948399117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64183387288606530597865489 48137540466454897948399117)
        ·
          refine ⟨18051577674920586730649669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48137540466454897948399117 18051577674920586730649669)
          ·
            refine ⟨3384670814047610011996813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18051577674920586730649669 3384670814047610011996813)
            ·
              refine ⟨1269251555267853754498805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3384670814047610011996813 1269251555267853754498805)
              ·
                refine ⟨118992333306361289484263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1269251555267853754498805 118992333306361289484263)
                ·
                  rfl

theorem cell21_1564223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 5].length) (baseStart_1564223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564223 prefixEnd_1564223 := by exact prefixLift 1564223
  have htrace : WordTrace (prefixWord ++ tailWord_1564223) baseStart_1564223 baseEnd_1564223 := by
    simpa [prefixWord, tailWord_1564223, baseEnd_1564223] using wordTrace_append hprefix tailTrace_1564223
  have hstable : (prefixWord ++ tailWord_1564223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564223).length < 2 ^ (prefixWord ++ tailWord_1564223).sum := by decide
  have hdescent : baseEnd_1564223 < baseStart_1564223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564319 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 4]
def baseStart_1564319 : Nat := 118140960795 + 1564319 * 2 ^ 59
def prefixEnd_1564319 : Nat := 4983230072969 + 3 ^ 40 * 1564319 * 2
def baseEnd_1564319 : Nat := 356998908427009034852593

theorem tailTrace_1564319 : CollatzResearch.WordTrace tailWord_1564319 prefixEnd_1564319 356998908427009034852593 := by
  unfold tailWord_1564319
  simp only [CollatzResearch.WordTrace]
  refine ⟨57055401219746902260264011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38036934146497934840176007 57055401219746902260264011)
  ·
    refine ⟨85583101829620353390396017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57055401219746902260264011 85583101829620353390396017)
    ·
      refine ⟨64187326372215265042797013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85583101829620353390396017 64187326372215265042797013)
      ·
        refine ⟨1504390461848795274440555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 64187326372215265042797013 1504390461848795274440555)
        ·
          refine ⟨2256585692773192911660833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504390461848795274440555 2256585692773192911660833)
          ·
            refine ⟨1692439269579894683745625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2256585692773192911660833 1692439269579894683745625)
            ·
              refine ⟨1269329452184921012809219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692439269579894683745625 1269329452184921012809219)
              ·
                refine ⟨1903994178277381519213829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269329452184921012809219 1903994178277381519213829)
                ·
                  refine ⟨356998908427009034852593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1903994178277381519213829 356998908427009034852593)
                  ·
                    rfl

theorem cell21_1564319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 4].length) (baseStart_1564319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564319 prefixEnd_1564319 := by exact prefixLift 1564319
  have htrace : WordTrace (prefixWord ++ tailWord_1564319) baseStart_1564319 baseEnd_1564319 := by
    simpa [prefixWord, tailWord_1564319, baseEnd_1564319] using wordTrace_append hprefix tailTrace_1564319
  have hstable : (prefixWord ++ tailWord_1564319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564319).length < 2 ^ (prefixWord ++ tailWord_1564319).sum := by decide
  have hdescent : baseEnd_1564319 < baseStart_1564319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564389 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 5]
def baseStart_1564389 : Nat := 118140960795 + 1564389 * 2 ^ 59
def prefixEnd_1564389 : Nat := 4983230072969 + 3 ^ 40 * 1564389 * 2
def baseEnd_1564389 : Nat := 357014883380704468685783

theorem tailTrace_1564389 : CollatzResearch.WordTrace tailWord_1564389 prefixEnd_1564389 357014883380704468685783 := by
  unfold tailWord_1564389
  simp only [CollatzResearch.WordTrace]
  refine ⟨57057954329493304215312221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38038636219662202810208147 57057954329493304215312221)
  ·
    refine ⟨21396732873559989080742083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57057954329493304215312221 21396732873559989080742083)
    ·
      refine ⟨32095099310339983621113125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21396732873559989080742083 32095099310339983621113125)
      ·
        refine ⟨6017831120688746928958711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32095099310339983621113125 6017831120688746928958711)
        ·
          refine ⟨9026746681033120393438067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017831120688746928958711 9026746681033120393438067)
          ·
            refine ⟨13540120021549680590157101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9026746681033120393438067 13540120021549680590157101)
            ·
              refine ⟨5077545008081130221308913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13540120021549680590157101 5077545008081130221308913)
              ·
                refine ⟨3808158756060847665981685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5077545008081130221308913 3808158756060847665981685)
                ·
                  refine ⟨357014883380704468685783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3808158756060847665981685 357014883380704468685783)
                  ·
                    rfl

theorem cell21_1564389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_1564389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564389 prefixEnd_1564389 := by exact prefixLift 1564389
  have htrace : WordTrace (prefixWord ++ tailWord_1564389) baseStart_1564389 baseEnd_1564389 := by
    simpa [prefixWord, tailWord_1564389, baseEnd_1564389] using wordTrace_append hprefix tailTrace_1564389
  have hstable : (prefixWord ++ tailWord_1564389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564389).length < 2 ^ (prefixWord ++ tailWord_1564389).sum := by decide
  have hdescent : baseEnd_1564389 < baseStart_1564389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564420 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_1564420 : Nat := 118140960795 + 1564420 * 2 ^ 59
def prefixEnd_1564420 : Nat := 4983230072969 + 3 ^ 40 * 1564420 * 2
def baseEnd_1564420 : Nat := 357021958003055303669053

theorem tailTrace_1564420 : CollatzResearch.WordTrace tailWord_1564420 prefixEnd_1564420 357021958003055303669053 := by
  unfold tailWord_1564420
  simp only [CollatzResearch.WordTrace]
  refine ⟨28529542496190498254845357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38039389994920664339793809 28529542496190498254845357)
  ·
    refine ⟨10698578436071436845567009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28529542496190498254845357 10698578436071436845567009)
    ·
      refine ⟨8023933827053577634175257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10698578436071436845567009 8023933827053577634175257)
      ·
        refine ⟨6017950370290183225631443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8023933827053577634175257 6017950370290183225631443)
        ·
          refine ⟨9026925555435274838447165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017950370290183225631443 9026925555435274838447165)
          ·
            refine ⟨3385097083288228064417687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9026925555435274838447165 3385097083288228064417687)
            ·
              refine ⟨5077645624932342096626531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3385097083288228064417687 5077645624932342096626531)
              ·
                refine ⟨7616468437398513144939797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077645624932342096626531 7616468437398513144939797)
                ·
                  refine ⟨357021958003055303669053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7616468437398513144939797 357021958003055303669053)
                  ·
                    rfl

theorem cell21_1564420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_1564420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564420 prefixEnd_1564420 := by exact prefixLift 1564420
  have htrace : WordTrace (prefixWord ++ tailWord_1564420) baseStart_1564420 baseEnd_1564420 := by
    simpa [prefixWord, tailWord_1564420, baseEnd_1564420] using wordTrace_append hprefix tailTrace_1564420
  have hstable : (prefixWord ++ tailWord_1564420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564420).length < 2 ^ (prefixWord ++ tailWord_1564420).sum := by decide
  have hdescent : baseEnd_1564420 < baseStart_1564420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564429 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1564429 : Nat := 118140960795 + 1564429 * 2 ^ 59
def prefixEnd_1564429 : Nat := 4983230072969 + 3 ^ 40 * 1564429 * 2
def baseEnd_1564429 : Nat := 357024011925673288019035

theorem tailTrace_1564429 : CollatzResearch.WordTrace tailWord_1564429 prefixEnd_1564429 357024011925673288019035 := by
  unfold tailWord_1564429
  simp only [CollatzResearch.WordTrace]
  refine ⟨57059413249348391046768341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38039608832898927364512227 57059413249348391046768341)
  ·
    refine ⟨1337329998031602915158633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 57059413249348391046768341 1337329998031602915158633)
    ·
      refine ⟨1002997498523702186368975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1337329998031602915158633 1002997498523702186368975)
      ·
        refine ⟨1504496247785553279553463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002997498523702186368975 1504496247785553279553463)
        ·
          refine ⟨2256744371678329919330195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504496247785553279553463 2256744371678329919330195)
          ·
            refine ⟨3385116557517494878995293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256744371678329919330195 3385116557517494878995293)
            ·
              refine ⟨1269418709069060579623235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385116557517494878995293 1269418709069060579623235)
              ·
                refine ⟨1904128063603590869434853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269418709069060579623235 1904128063603590869434853)
                ·
                  refine ⟨357024011925673288019035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904128063603590869434853 357024011925673288019035)
                  ·
                    rfl

theorem cell21_1564429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1564429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564429 prefixEnd_1564429 := by exact prefixLift 1564429
  have htrace : WordTrace (prefixWord ++ tailWord_1564429) baseStart_1564429 baseEnd_1564429 := by
    simpa [prefixWord, tailWord_1564429, baseEnd_1564429] using wordTrace_append hprefix tailTrace_1564429
  have hstable : (prefixWord ++ tailWord_1564429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564429).length < 2 ^ (prefixWord ++ tailWord_1564429).sum := by decide
  have hdescent : baseEnd_1564429 < baseStart_1564429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564437 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 4]
def baseStart_1564437 : Nat := 118140960795 + 1564437 * 2 ^ 59
def prefixEnd_1564437 : Nat := 4983230072969 + 3 ^ 40 * 1564437 * 2
def baseEnd_1564437 : Nat := 357025837634667051885685

theorem tailTrace_1564437 : CollatzResearch.WordTrace tailWord_1564437 prefixEnd_1564437 357025837634667051885685 := by
  unfold tailWord_1564437
  simp only [CollatzResearch.WordTrace]
  refine ⟨57059705033319408413059565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38039803355546272275373043 57059705033319408413059565)
  ·
    refine ⟨21397389387494778154897337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57059705033319408413059565 21397389387494778154897337)
    ·
      refine ⟨16048042040621083616173003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21397389387494778154897337 16048042040621083616173003)
      ·
        refine ⟨24072063060931625424259505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16048042040621083616173003 24072063060931625424259505)
        ·
          refine ⟨18054047295698719068194629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24072063060931625424259505 18054047295698719068194629)
          ·
            refine ⟨3385133867943509825286493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18054047295698719068194629 3385133867943509825286493)
            ·
              refine ⟨1269425200478816184482435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385133867943509825286493 1269425200478816184482435)
              ·
                refine ⟨1904137800718224276723653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269425200478816184482435 1904137800718224276723653)
                ·
                  refine ⟨357025837634667051885685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904137800718224276723653 357025837634667051885685)
                  ·
                    rfl

theorem cell21_1564437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_1564437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564437 prefixEnd_1564437 := by exact prefixLift 1564437
  have htrace : WordTrace (prefixWord ++ tailWord_1564437) baseStart_1564437 baseEnd_1564437 := by
    simpa [prefixWord, tailWord_1564437, baseEnd_1564437] using wordTrace_append hprefix tailTrace_1564437
  have hstable : (prefixWord ++ tailWord_1564437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564437).length < 2 ^ (prefixWord ++ tailWord_1564437).sum := by decide
  have hdescent : baseEnd_1564437 < baseStart_1564437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564569 : List Nat := [1, 2, 1, 2, 1, 3, 2, 9]
def baseStart_1564569 : Nat := 118140960795 + 1564569 * 2 ^ 59
def prefixEnd_1564569 : Nat := 4983230072969 + 3 ^ 40 * 1564569 * 2
def baseEnd_1564569 : Nat := 119018653944354718561805

theorem tailTrace_1564569 : CollatzResearch.WordTrace tailWord_1564569 prefixEnd_1564569 119018653944354718561805 := by
  unfold tailWord_1564569
  simp only [CollatzResearch.WordTrace]
  refine ⟨57064519468841194956864761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38043012979227463304576507 57064519468841194956864761)
  ·
    refine ⟨42798389601630896217648571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57064519468841194956864761 42798389601630896217648571)
    ·
      refine ⟨64197584402446344326472857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42798389601630896217648571 64197584402446344326472857)
      ·
        refine ⟨48148188301834758244854643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64197584402446344326472857 48148188301834758244854643)
        ·
          refine ⟨72222282452752137367281965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48148188301834758244854643 72222282452752137367281965)
          ·
            refine ⟨27083355919782051512730737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72222282452752137367281965 27083355919782051512730737)
            ·
              refine ⟨20312516939836538634548053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27083355919782051512730737 20312516939836538634548053)
              ·
                refine ⟨119018653944354718561805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20312516939836538634548053 119018653944354718561805)
                ·
                  rfl

theorem cell21_1564569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 9].length) (baseStart_1564569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564569 prefixEnd_1564569 := by exact prefixLift 1564569
  have htrace : WordTrace (prefixWord ++ tailWord_1564569) baseStart_1564569 baseEnd_1564569 := by
    simpa [prefixWord, tailWord_1564569, baseEnd_1564569] using wordTrace_append hprefix tailTrace_1564569
  have hstable : (prefixWord ++ tailWord_1564569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564569).length < 2 ^ (prefixWord ++ tailWord_1564569).sum := by decide
  have hdescent : baseEnd_1564569 < baseStart_1564569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564575 : List Nat := [1, 1, 2, 5, 3, 1, 2, 3, 3]
def baseStart_1564575 : Nat := 118140960795 + 1564575 * 2 ^ 59
def prefixEnd_1564575 : Nat := 4983230072969 + 3 ^ 40 * 1564575 * 2
def baseEnd_1564575 : Nat := 357057331114809478585403

theorem tailTrace_1564575 : CollatzResearch.WordTrace tailWord_1564575 prefixEnd_1564575 357057331114809478585403 := by
  unfold tailWord_1564575
  simp only [CollatzResearch.WordTrace]
  refine ⟨57064738306819457981583179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38043158871212971987722119 57064738306819457981583179)
  ·
    refine ⟨85597107460229186972374769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57064738306819457981583179 85597107460229186972374769)
    ·
      refine ⟨64197830595171890229281077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85597107460229186972374769 64197830595171890229281077)
      ·
        refine ⟨6018546618297364708995101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64197830595171890229281077 6018546618297364708995101)
        ·
          refine ⟨2256954981861511765873163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6018546618297364708995101 2256954981861511765873163)
          ·
            refine ⟨3385432472792267648809745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256954981861511765873163 3385432472792267648809745)
            ·
              refine ⟨2539074354594200736607309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3385432472792267648809745 2539074354594200736607309)
              ·
                refine ⟨952152882972825276227741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2539074354594200736607309 952152882972825276227741)
                ·
                  refine ⟨357057331114809478585403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952152882972825276227741 357057331114809478585403)
                  ·
                    rfl

theorem cell21_1564575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 3].length) (baseStart_1564575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564575 prefixEnd_1564575 := by exact prefixLift 1564575
  have htrace : WordTrace (prefixWord ++ tailWord_1564575) baseStart_1564575 baseEnd_1564575 := by
    simpa [prefixWord, tailWord_1564575, baseEnd_1564575] using wordTrace_append hprefix tailTrace_1564575
  have hstable : (prefixWord ++ tailWord_1564575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564575).length < 2 ^ (prefixWord ++ tailWord_1564575).sum := by decide
  have hdescent : baseEnd_1564575 < baseStart_1564575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564665 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 4]
def baseStart_1564665 : Nat := 118140960795 + 1564665 * 2 ^ 59
def prefixEnd_1564665 : Nat := 4983230072969 + 3 ^ 40 * 1564665 * 2
def baseEnd_1564665 : Nat := 357077870340989322085219

theorem tailTrace_1564665 : CollatzResearch.WordTrace tailWord_1564665 prefixEnd_1564665 357077870340989322085219 := by
  unfold tailWord_1564665
  simp only [CollatzResearch.WordTrace]
  refine ⟨57068020876493403352359449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38045347250995602234906299 57068020876493403352359449)
  ·
    refine ⟨42801015657370052514269587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57068020876493403352359449 42801015657370052514269587)
    ·
      refine ⟨64201523486055078771404381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42801015657370052514269587 64201523486055078771404381)
      ·
        refine ⟨24075571307270654539276643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64201523486055078771404381 24075571307270654539276643)
        ·
          refine ⟨36113356960905981808914965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24075571307270654539276643 36113356960905981808914965)
          ·
            refine ⟨1692813607542467897292889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36113356960905981808914965 1692813607542467897292889)
            ·
              refine ⟨1269610205656850922969667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692813607542467897292889 1269610205656850922969667)
              ·
                refine ⟨1904415308485276384454501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269610205656850922969667 1904415308485276384454501)
                ·
                  refine ⟨357077870340989322085219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904415308485276384454501 357077870340989322085219)
                  ·
                    rfl

theorem cell21_1564665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_1564665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564665 prefixEnd_1564665 := by exact prefixLift 1564665
  have htrace : WordTrace (prefixWord ++ tailWord_1564665) baseStart_1564665 baseEnd_1564665 := by
    simpa [prefixWord, tailWord_1564665, baseEnd_1564665] using wordTrace_append hprefix tailTrace_1564665
  have hstable : (prefixWord ++ tailWord_1564665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564665).length < 2 ^ (prefixWord ++ tailWord_1564665).sum := by decide
  have hdescent : baseEnd_1564665 < baseStart_1564665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564758 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1564758 : Nat := 118140960795 + 1564758 * 2 ^ 59
def prefixEnd_1564758 : Nat := 4983230072969 + 3 ^ 40 * 1564758 * 2
def baseEnd_1564758 : Nat := 357099094208041827035029

theorem tailTrace_1564758 : CollatzResearch.WordTrace tailWord_1564758 prefixEnd_1564758 357099094208041827035029 := by
  unfold tailWord_1564758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3566963304072280014718433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38047608576770986823663285 3566963304072280014718433)
  ·
    refine ⟨2675222478054210011038825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3566963304072280014718433 2675222478054210011038825)
    ·
      refine ⟨2006416858540657508279119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2675222478054210011038825 2006416858540657508279119)
      ·
        refine ⟨3009625287810986262418679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006416858540657508279119 3009625287810986262418679)
        ·
          refine ⟨4514437931716479393628019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009625287810986262418679 4514437931716479393628019)
          ·
            refine ⟨6771656897574719090442029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514437931716479393628019 6771656897574719090442029)
            ·
              refine ⟨2539371336590519658915761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6771656897574719090442029 2539371336590519658915761)
              ·
                refine ⟨1904528502442889744186821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2539371336590519658915761 1904528502442889744186821)
                ·
                  refine ⟨357099094208041827035029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904528502442889744186821 357099094208041827035029)
                  ·
                    rfl

theorem cell21_1564758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1564758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564758 prefixEnd_1564758 := by exact prefixLift 1564758
  have htrace : WordTrace (prefixWord ++ tailWord_1564758) baseStart_1564758 baseEnd_1564758 := by
    simpa [prefixWord, tailWord_1564758, baseEnd_1564758] using wordTrace_append hprefix tailTrace_1564758
  have hstable : (prefixWord ++ tailWord_1564758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564758).length < 2 ^ (prefixWord ++ tailWord_1564758).sum := by decide
  have hdescent : baseEnd_1564758 < baseStart_1564758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564820 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1564820 : Nat := 118140960795 + 1564820 * 2 ^ 59
def prefixEnd_1564820 : Nat := 4983230072969 + 3 ^ 40 * 1564820 * 2
def baseEnd_1564820 : Nat := 357113243452743497001569

theorem tailTrace_1564820 : CollatzResearch.WordTrace tailWord_1564820 prefixEnd_1564820 357113243452743497001569 := by
  unfold tailWord_1564820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28536837095465932412125957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38049116127287909882834609 28536837095465932412125957)
  ·
    refine ⟨5350656955399862327273617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28536837095465932412125957 5350656955399862327273617)
    ·
      refine ⟨4012992716549896745455213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5350656955399862327273617 4012992716549896745455213)
      ·
        refine ⟨1504872268706211279545705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4012992716549896745455213 1504872268706211279545705)
        ·
          refine ⟨1128654201529658459659279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1504872268706211279545705 1128654201529658459659279)
          ·
            refine ⟨1692981302294487689488919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128654201529658459659279 1692981302294487689488919)
            ·
              refine ⟨2539471953441731534233379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692981302294487689488919 2539471953441731534233379)
              ·
                refine ⟨3809207930162597301350069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539471953441731534233379 3809207930162597301350069)
                ·
                  refine ⟨357113243452743497001569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3809207930162597301350069 357113243452743497001569)
                  ·
                    rfl

theorem cell21_1564820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1564820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564820 prefixEnd_1564820 := by exact prefixLift 1564820
  have htrace : WordTrace (prefixWord ++ tailWord_1564820) baseStart_1564820 baseEnd_1564820 := by
    simpa [prefixWord, tailWord_1564820, baseEnd_1564820] using wordTrace_append hprefix tailTrace_1564820
  have hstable : (prefixWord ++ tailWord_1564820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564820).length < 2 ^ (prefixWord ++ tailWord_1564820).sum := by decide
  have hdescent : baseEnd_1564820 < baseStart_1564820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564834 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1564834 : Nat := 118140960795 + 1564834 * 2 ^ 59
def prefixEnd_1564834 : Nat := 4983230072969 + 3 ^ 40 * 1564834 * 2
def baseEnd_1564834 : Nat := 357116438443482583768207

theorem tailTrace_1564834 : CollatzResearch.WordTrace tailWord_1564834 prefixEnd_1564834 357116438443482583768207 := by
  unfold tailWord_1564834
  simp only [CollatzResearch.WordTrace]
  refine ⟨14268546203220286303815389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38049456541920763476841037 14268546203220286303815389)
  ·
    refine ⟨5350704826207607363930771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14268546203220286303815389 5350704826207607363930771)
    ·
      refine ⟨8026057239311411045896157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5350704826207607363930771 8026057239311411045896157)
      ·
        refine ⟨3009771464741779142211059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8026057239311411045896157 3009771464741779142211059)
        ·
          refine ⟨4514657197112668713316589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009771464741779142211059 4514657197112668713316589)
          ·
            refine ⟨1692996448917250767493721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4514657197112668713316589 1692996448917250767493721)
            ·
              refine ⟨1269747336687938075620291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692996448917250767493721 1269747336687938075620291)
              ·
                refine ⟨1904621005031907113430437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269747336687938075620291 1904621005031907113430437)
                ·
                  refine ⟨357116438443482583768207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904621005031907113430437 357116438443482583768207)
                  ·
                    rfl

theorem cell21_1564834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1564834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564834 prefixEnd_1564834 := by exact prefixLift 1564834
  have htrace : WordTrace (prefixWord ++ tailWord_1564834) baseStart_1564834 baseEnd_1564834 := by
    simpa [prefixWord, tailWord_1564834, baseEnd_1564834] using wordTrace_append hprefix tailTrace_1564834
  have hstable : (prefixWord ++ tailWord_1564834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564834).length < 2 ^ (prefixWord ++ tailWord_1564834).sum := by decide
  have hdescent : baseEnd_1564834 < baseStart_1564834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564904 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_1564904 : Nat := 118140960795 + 1564904 * 2 ^ 59
def prefixEnd_1564904 : Nat := 4983230072969 + 3 ^ 40 * 1564904 * 2
def baseEnd_1564904 : Nat := 357132413397178017601397

theorem tailTrace_1564904 : CollatzResearch.WordTrace tailWord_1564904 prefixEnd_1564904 357132413397178017601397 := by
  unfold tailWord_1564904
  simp only [CollatzResearch.WordTrace]
  refine ⟨28538368961313773585154883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38051158615085031446873177 28538368961313773585154883)
  ·
    refine ⟨42807553441970660377732325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28538368961313773585154883 42807553441970660377732325)
    ·
      refine ⟨8026416270369498820824811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42807553441970660377732325 8026416270369498820824811)
      ·
        refine ⟨12039624405554248231237217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8026416270369498820824811 12039624405554248231237217)
        ·
          refine ⟨9029718304165686173427913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12039624405554248231237217 9029718304165686173427913)
          ·
            refine ⟨6772288728124264630070935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9029718304165686173427913 6772288728124264630070935)
            ·
              refine ⟨10158433092186396945106403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6772288728124264630070935 10158433092186396945106403)
              ·
                refine ⟨15237649638279595417659605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10158433092186396945106403 15237649638279595417659605)
                ·
                  refine ⟨357132413397178017601397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15237649638279595417659605 357132413397178017601397)
                  ·
                    rfl

theorem cell21_1564904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_1564904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564904 prefixEnd_1564904 := by exact prefixLift 1564904
  have htrace : WordTrace (prefixWord ++ tailWord_1564904) baseStart_1564904 baseEnd_1564904 := by
    simpa [prefixWord, tailWord_1564904, baseEnd_1564904] using wordTrace_append hprefix tailTrace_1564904
  have hstable : (prefixWord ++ tailWord_1564904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564904).length < 2 ^ (prefixWord ++ tailWord_1564904).sum := by decide
  have hdescent : baseEnd_1564904 < baseStart_1564904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1564952 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_1564952 : Nat := 118140960795 + 1564952 * 2 ^ 59
def prefixEnd_1564952 : Nat := 4983230072969 + 3 ^ 40 * 1564952 * 2
def baseEnd_1564952 : Nat := 357143367651140600801299

theorem tailTrace_1564952 : CollatzResearch.WordTrace tailWord_1564952 prefixEnd_1564952 357143367651140600801299 := by
  unfold tailWord_1564952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28539244313226825684028555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38052325750969100912038073 28539244313226825684028555)
  ·
    refine ⟨42808866469840238526042833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28539244313226825684028555 42808866469840238526042833)
    ·
      refine ⟨32106649852380178894532125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42808866469840238526042833 32106649852380178894532125)
      ·
        refine ⟨12039993694642567085449547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32106649852380178894532125 12039993694642567085449547)
        ·
          refine ⟨18059990541963850628174321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12039993694642567085449547 18059990541963850628174321)
          ·
            refine ⟨13544992906472887971130741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18059990541963850628174321 13544992906472887971130741)
            ·
              refine ⟨1269843084981833247293507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13544992906472887971130741 1269843084981833247293507)
              ·
                refine ⟨1904764627472749870940261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269843084981833247293507 1904764627472749870940261)
                ·
                  refine ⟨357143367651140600801299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1904764627472749870940261 357143367651140600801299)
                  ·
                    rfl

theorem cell21_1564952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_1564952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1564952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1564952 prefixEnd_1564952 := by exact prefixLift 1564952
  have htrace : WordTrace (prefixWord ++ tailWord_1564952) baseStart_1564952 baseEnd_1564952 := by
    simpa [prefixWord, tailWord_1564952, baseEnd_1564952] using wordTrace_append hprefix tailTrace_1564952
  have hstable : (prefixWord ++ tailWord_1564952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1564952).length < 2 ^ (prefixWord ++ tailWord_1564952).sum := by decide
  have hdescent : baseEnd_1564952 < baseStart_1564952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1564952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565039 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 9]
def baseStart_1565039 : Nat := 118140960795 + 1565039 * 2 ^ 59
def prefixEnd_1565039 : Nat := 4983230072969 + 3 ^ 40 * 1565039 * 2
def baseEnd_1565039 : Nat := 357163222236447782851121

theorem tailTrace_1565039 : CollatzResearch.WordTrace tailWord_1565039 prefixEnd_1565039 357163222236447782851121 := by
  unfold tailWord_1565039
  simp only [CollatzResearch.WordTrace]
  refine ⟨57081661777138465226474171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38054441184758976817649447 57081661777138465226474171)
  ·
    refine ⟨85622492665707697839711257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57081661777138465226474171 85622492665707697839711257)
    ·
      refine ⟨64216869499280773379783443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85622492665707697839711257 64216869499280773379783443)
      ·
        refine ⟨96325304248921160069675165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64216869499280773379783443 96325304248921160069675165)
        ·
          refine ⟨36121989093345435026128187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96325304248921160069675165 36121989093345435026128187)
          ·
            refine ⟨54182983640018152539192281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36121989093345435026128187 54182983640018152539192281)
            ·
              refine ⟨40637237730013614404394211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54182983640018152539192281 40637237730013614404394211)
              ·
                refine ⟨60955856595020421606591317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40637237730013614404394211 60955856595020421606591317)
                ·
                  refine ⟨357163222236447782851121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60955856595020421606591317 357163222236447782851121)
                  ·
                    rfl

theorem cell21_1565039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_1565039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565039 prefixEnd_1565039 := by exact prefixLift 1565039
  have htrace : WordTrace (prefixWord ++ tailWord_1565039) baseStart_1565039 baseEnd_1565039 := by
    simpa [prefixWord, tailWord_1565039, baseEnd_1565039] using wordTrace_append hprefix tailTrace_1565039
  have hstable : (prefixWord ++ tailWord_1565039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565039).length < 2 ^ (prefixWord ++ tailWord_1565039).sum := by decide
  have hdescent : baseEnd_1565039 < baseStart_1565039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565059 : List Nat := [1, 1, 1, 3, 7, 1, 1, 6]
def baseStart_1565059 : Nat := 118140960795 + 1565059 * 2 ^ 59
def prefixEnd_1565059 : Nat := 4983230072969 + 3 ^ 40 * 1565059 * 2
def baseEnd_1565059 : Nat := 119055928836310730839249

theorem tailTrace_1565059 : CollatzResearch.WordTrace tailWord_1565059 prefixEnd_1565059 119055928836310730839249 := by
  unfold tailWord_1565059
  simp only [CollatzResearch.WordTrace]
  refine ⟨57082391237066008642202231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38054927491377339094801487 57082391237066008642202231)
  ·
    refine ⟨85623586855599012963303347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57082391237066008642202231 85623586855599012963303347)
    ·
      refine ⟨128435380283398519444955021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85623586855599012963303347 128435380283398519444955021)
      ·
        refine ⟨48163267606274444791858133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128435380283398519444955021 48163267606274444791858133)
        ·
          refine ⟨1128826584522057299809175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48163267606274444791858133 1128826584522057299809175)
          ·
            refine ⟨1693239876783085949713763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128826584522057299809175 1693239876783085949713763)
            ·
              refine ⟨2539859815174628924570645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693239876783085949713763 2539859815174628924570645)
              ·
                refine ⟨119055928836310730839249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2539859815174628924570645 119055928836310730839249)
                ·
                  rfl

theorem cell21_1565059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 6].length) (baseStart_1565059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565059 prefixEnd_1565059 := by exact prefixLift 1565059
  have htrace : WordTrace (prefixWord ++ tailWord_1565059) baseStart_1565059 baseEnd_1565059 := by
    simpa [prefixWord, tailWord_1565059, baseEnd_1565059] using wordTrace_append hprefix tailTrace_1565059
  have hstable : (prefixWord ++ tailWord_1565059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565059).length < 2 ^ (prefixWord ++ tailWord_1565059).sum := by decide
  have hdescent : baseEnd_1565059 < baseStart_1565059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565090 : List Nat := [3, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_1565090 : Nat := 118140960795 + 1565090 * 2 ^ 59
def prefixEnd_1565090 : Nat := 4983230072969 + 3 ^ 40 * 1565090 * 2
def baseEnd_1565090 : Nat := 357174861131283027501017

theorem tailTrace_1565090 : CollatzResearch.WordTrace tailWord_1565090 prefixEnd_1565090 357174861131283027501017 := by
  unfold tailWord_1565090
  simp only [CollatzResearch.WordTrace]
  refine ⟨14270880474988425234145181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38055681266635800624387149 14270880474988425234145181)
  ·
    refine ⟨5351580178120659462804443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14270880474988425234145181 5351580178120659462804443)
    ·
      refine ⟨8027370267180989194206665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5351580178120659462804443 8027370267180989194206665)
      ·
        refine ⟨6020527700385741895654999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8027370267180989194206665 6020527700385741895654999)
        ·
          refine ⟨9030791550578612843482499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020527700385741895654999 9030791550578612843482499)
          ·
            refine ⟨13546187325867919265223749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9030791550578612843482499 13546187325867919265223749)
            ·
              refine ⟨2539910123600234862229453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13546187325867919265223749 2539910123600234862229453)
              ·
                refine ⟨952466296350088073336045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2539910123600234862229453 952466296350088073336045)
                ·
                  refine ⟨357174861131283027501017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952466296350088073336045 357174861131283027501017)
                  ·
                    rfl

theorem cell21_1565090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_1565090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565090 prefixEnd_1565090 := by exact prefixLift 1565090
  have htrace : WordTrace (prefixWord ++ tailWord_1565090) baseStart_1565090 baseEnd_1565090 := by
    simpa [prefixWord, tailWord_1565090, baseEnd_1565090] using wordTrace_append hprefix tailTrace_1565090
  have hstable : (prefixWord ++ tailWord_1565090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565090).length < 2 ^ (prefixWord ++ tailWord_1565090).sum := by decide
  have hdescent : baseEnd_1565090 < baseStart_1565090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565146 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1565146 : Nat := 118140960795 + 1565146 * 2 ^ 59
def prefixEnd_1565146 : Nat := 4983230072969 + 3 ^ 40 * 1565146 * 2
def baseEnd_1565146 : Nat := 357187641094239374567569

theorem tailTrace_1565146 : CollatzResearch.WordTrace tailWord_1565146 prefixEnd_1565146 357187641094239374567569 := by
  unfold tailWord_1565146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14271391096937705625154823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38057042925167215000412861 14271391096937705625154823)
  ·
    refine ⟨21407086645406558437732235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14271391096937705625154823 21407086645406558437732235)
    ·
      refine ⟨32110629968109837656598353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21407086645406558437732235 32110629968109837656598353)
      ·
        refine ⟨24082972476082378242448765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32110629968109837656598353 24082972476082378242448765)
        ·
          refine ⟨9031114678530891840918287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24082972476082378242448765 9031114678530891840918287)
          ·
            refine ⟨13546672017796337761377431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9031114678530891840918287 13546672017796337761377431)
            ·
              refine ⟨20320008026694506642066147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13546672017796337761377431 20320008026694506642066147)
              ·
                refine ⟨30480012040041759963099221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20320008026694506642066147 30480012040041759963099221)
                ·
                  refine ⟨357187641094239374567569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30480012040041759963099221 357187641094239374567569)
                  ·
                    rfl

theorem cell21_1565146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1565146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565146 prefixEnd_1565146 := by exact prefixLift 1565146
  have htrace : WordTrace (prefixWord ++ tailWord_1565146) baseStart_1565146 baseEnd_1565146 := by
    simpa [prefixWord, tailWord_1565146, baseEnd_1565146] using wordTrace_append hprefix tailTrace_1565146
  have hstable : (prefixWord ++ tailWord_1565146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565146).length < 2 ^ (prefixWord ++ tailWord_1565146).sum := by decide
  have hdescent : baseEnd_1565146 < baseStart_1565146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565284 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_1565284 : Nat := 118140960795 + 1565284 * 2 ^ 59
def prefixEnd_1565284 : Nat := 4983230072969 + 3 ^ 40 * 1565284 * 2
def baseEnd_1565284 : Nat := 357219134574381801267287

theorem tailTrace_1565284 : CollatzResearch.WordTrace tailWord_1565284 prefixEnd_1565284 357219134574381801267287 := by
  unfold tailWord_1565284
  simp only [CollatzResearch.WordTrace]
  refine ⟨28545298830625436034571453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38060398440833914712761937 28545298830625436034571453)
  ·
    refine ⟨10704487061484538512964295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28545298830625436034571453 10704487061484538512964295)
    ·
      refine ⟨16056730592226807769446443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10704487061484538512964295 16056730592226807769446443)
      ·
        refine ⟨24085095888340211654169665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16056730592226807769446443 24085095888340211654169665)
        ·
          refine ⟨18063821916255158740627249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24085095888340211654169665 18063821916255158740627249)
          ·
            refine ⟨13547866437191369055470437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18063821916255158740627249 13547866437191369055470437)
            ·
              refine ⟨2540224956973381697900707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13547866437191369055470437 2540224956973381697900707)
              ·
                refine ⟨3810337435460072546851061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540224956973381697900707 3810337435460072546851061)
                ·
                  refine ⟨357219134574381801267287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3810337435460072546851061 357219134574381801267287)
                  ·
                    rfl

theorem cell21_1565284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_1565284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565284 prefixEnd_1565284 := by exact prefixLift 1565284
  have htrace : WordTrace (prefixWord ++ tailWord_1565284) baseStart_1565284 baseEnd_1565284 := by
    simpa [prefixWord, tailWord_1565284, baseEnd_1565284] using wordTrace_append hprefix tailTrace_1565284
  have hstable : (prefixWord ++ tailWord_1565284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565284).length < 2 ^ (prefixWord ++ tailWord_1565284).sum := by decide
  have hdescent : baseEnd_1565284 < baseStart_1565284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565394 : List Nat := [3, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_1565394 : Nat := 118140960795 + 1565394 * 2 ^ 59
def prefixEnd_1565394 : Nat := 4983230072969 + 3 ^ 40 * 1565394 * 2
def baseEnd_1565394 : Nat := 357244238073046054433729

theorem tailTrace_1565394 : CollatzResearch.WordTrace tailWord_1565394 prefixEnd_1565394 357244238073046054433729 := by
  unfold tailWord_1565394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14273652422713090213911809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38063073127234907237098157 14273652422713090213911809)
  ·
    refine ⟨10705239317034817660433857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14273652422713090213911809 10705239317034817660433857)
    ·
      refine ⟨8028929487776113245325393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10705239317034817660433857 8028929487776113245325393)
      ·
        refine ⟨6021697115832084933994045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8028929487776113245325393 6021697115832084933994045)
        ·
          refine ⟨2258136418437031850247767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6021697115832084933994045 2258136418437031850247767)
          ·
            refine ⟨3387204627655547775371651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258136418437031850247767 3387204627655547775371651)
            ·
              refine ⟨5080806941483321663057477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3387204627655547775371651 5080806941483321663057477)
              ·
                refine ⟨952651301528122811823277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5080806941483321663057477 952651301528122811823277)
                ·
                  refine ⟨357244238073046054433729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952651301528122811823277 357244238073046054433729)
                  ·
                    rfl

theorem cell21_1565394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_1565394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565394 prefixEnd_1565394 := by exact prefixLift 1565394
  have htrace : WordTrace (prefixWord ++ tailWord_1565394) baseStart_1565394 baseEnd_1565394 := by
    simpa [prefixWord, tailWord_1565394, baseEnd_1565394] using wordTrace_append hprefix tailTrace_1565394
  have hstable : (prefixWord ++ tailWord_1565394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565394).length < 2 ^ (prefixWord ++ tailWord_1565394).sum := by decide
  have hdescent : baseEnd_1565394 < baseStart_1565394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565422 : List Nat := [4, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1565422 : Nat := 118140960795 + 1565422 * 2 ^ 59
def prefixEnd_1565422 : Nat := 4983230072969 + 3 ^ 40 * 1565422 * 2
def baseEnd_1565422 : Nat := 119083542684841409322335

theorem tailTrace_1565422 : CollatzResearch.WordTrace tailWord_1565422 prefixEnd_1565422 119083542684841409322335 := by
  unfold tailWord_1565422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7136953866843865204708315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38063753956500614425111013 7136953866843865204708315)
  ·
    refine ⟨10705430800265797807062473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7136953866843865204708315 10705430800265797807062473)
    ·
      refine ⟨8029073100199348355296855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10705430800265797807062473 8029073100199348355296855)
      ·
        refine ⟨12043609650299022532945283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8029073100199348355296855 12043609650299022532945283)
        ·
          refine ⟨18065414475448533799417925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12043609650299022532945283 18065414475448533799417925)
          ·
            refine ⟨3387265214146600087390861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18065414475448533799417925 3387265214146600087390861)
            ·
              refine ⟨1270224455304975032771573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3387265214146600087390861 1270224455304975032771573)
              ·
                refine ⟨119083542684841409322335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1270224455304975032771573 119083542684841409322335)
                ·
                  rfl

theorem cell21_1565422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1565422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565422 prefixEnd_1565422 := by exact prefixLift 1565422
  have htrace : WordTrace (prefixWord ++ tailWord_1565422) baseStart_1565422 baseEnd_1565422 := by
    simpa [prefixWord, tailWord_1565422, baseEnd_1565422] using wordTrace_append hprefix tailTrace_1565422
  have hstable : (prefixWord ++ tailWord_1565422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565422).length < 2 ^ (prefixWord ++ tailWord_1565422).sum := by decide
  have hdescent : baseEnd_1565422 < baseStart_1565422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565428 : List Nat := [2, 6, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1565428 : Nat := 118140960795 + 1565428 * 2 ^ 59
def prefixEnd_1565428 : Nat := 4983230072969 + 3 ^ 40 * 1565428 * 2
def baseEnd_1565428 : Nat := 357251997336269550866993

theorem tailTrace_1565428 : CollatzResearch.WordTrace tailWord_1565428 prefixEnd_1565428 357251997336269550866993 := by
  unfold tailWord_1565428
  simp only [CollatzResearch.WordTrace]
  refine ⟨28547924886364592331192469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38063899848486123108256625 28547924886364592331192469)
  ·
    refine ⟨1338183979048340265524647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28547924886364592331192469 1338183979048340265524647)
    ·
      refine ⟨2007275968572510398286971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338183979048340265524647 2007275968572510398286971)
      ·
        refine ⟨3010913952858765597430457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007275968572510398286971 3010913952858765597430457)
        ·
          refine ⟨2258185464644074198072843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3010913952858765597430457 2258185464644074198072843)
          ·
            refine ⟨3387278196966111297109265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258185464644074198072843 3387278196966111297109265)
            ·
              refine ⟨2540458647724583472831949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3387278196966111297109265 2540458647724583472831949)
              ·
                refine ⟨952671992896718802311981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2540458647724583472831949 952671992896718802311981)
                ·
                  refine ⟨357251997336269550866993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952671992896718802311981 357251997336269550866993)
                  ·
                    rfl

theorem cell21_1565428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1565428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565428 prefixEnd_1565428 := by exact prefixLift 1565428
  have htrace : WordTrace (prefixWord ++ tailWord_1565428) baseStart_1565428 baseEnd_1565428 := by
    simpa [prefixWord, tailWord_1565428, baseEnd_1565428] using wordTrace_append hprefix tailTrace_1565428
  have hstable : (prefixWord ++ tailWord_1565428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565428).length < 2 ^ (prefixWord ++ tailWord_1565428).sum := by decide
  have hdescent : baseEnd_1565428 < baseStart_1565428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565450 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_1565450 : Nat := 118140960795 + 1565450 * 2 ^ 59
def prefixEnd_1565450 : Nat := 4983230072969 + 3 ^ 40 * 1565450 * 2
def baseEnd_1565450 : Nat := 357257018036002401500281

theorem tailTrace_1565450 : CollatzResearch.WordTrace tailWord_1565450 prefixEnd_1565450 357257018036002401500281 := by
  unfold tailWord_1565450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274163044662370604921451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38064434785766321613123869 14274163044662370604921451)
  ·
    refine ⟨21411244566993555907382177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14274163044662370604921451 21411244566993555907382177)
    ·
      refine ⟨16058433425245166930536633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21411244566993555907382177 16058433425245166930536633)
      ·
        refine ⟨12043825068933875197902475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16058433425245166930536633 12043825068933875197902475)
        ·
          refine ⟨18065737603400812796853713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12043825068933875197902475 18065737603400812796853713)
          ·
            refine ⟨13549303202550609597640285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18065737603400812796853713 13549303202550609597640285)
            ·
              refine ⟨5080988700956478599115107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13549303202550609597640285 5080988700956478599115107)
              ·
                refine ⟨7621483051434717898672661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5080988700956478599115107 7621483051434717898672661)
                ·
                  refine ⟨357257018036002401500281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7621483051434717898672661 357257018036002401500281)
                  ·
                    rfl

theorem cell21_1565450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_1565450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565450 prefixEnd_1565450 := by exact prefixLift 1565450
  have htrace : WordTrace (prefixWord ++ tailWord_1565450) baseStart_1565450 baseEnd_1565450 := by
    simpa [prefixWord, tailWord_1565450, baseEnd_1565450] using wordTrace_append hprefix tailTrace_1565450
  have hstable : (prefixWord ++ tailWord_1565450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565450).length < 2 ^ (prefixWord ++ tailWord_1565450).sum := by decide
  have hdescent : baseEnd_1565450 < baseStart_1565450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565464 : List Nat := [2, 1, 2, 3, 1, 1, 1, 10]
def baseStart_1565464 : Nat := 118140960795 + 1565464 * 2 ^ 59
def prefixEnd_1565464 : Nat := 4983230072969 + 3 ^ 40 * 1565464 * 2
def baseEnd_1565464 : Nat := 119086737675580496088973

theorem tailTrace_1565464 : CollatzResearch.WordTrace tailWord_1565464 prefixEnd_1565464 119086737675580496088973 := by
  unfold tailWord_1565464
  simp only [CollatzResearch.WordTrace]
  refine ⟨28548581400299381405347723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38064775200399175207130297 28548581400299381405347723)
  ·
    refine ⟨42822872100449072108021585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28548581400299381405347723 42822872100449072108021585)
    ·
      refine ⟨32117154075336804081016189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42822872100449072108021585 32117154075336804081016189)
      ·
        refine ⟨12043932778251301530381071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32117154075336804081016189 12043932778251301530381071)
        ·
          refine ⟨18065899167376952295571607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12043932778251301530381071 18065899167376952295571607)
          ·
            refine ⟨27098848751065428443357411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18065899167376952295571607 27098848751065428443357411)
            ·
              refine ⟨40648273126598142665036117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27098848751065428443357411 40648273126598142665036117)
              ·
                refine ⟨119086737675580496088973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40648273126598142665036117 119086737675580496088973)
                ·
                  rfl

theorem cell21_1565464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_1565464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565464 prefixEnd_1565464 := by exact prefixLift 1565464
  have htrace : WordTrace (prefixWord ++ tailWord_1565464) baseStart_1565464 baseEnd_1565464 := by
    simpa [prefixWord, tailWord_1565464, baseEnd_1565464] using wordTrace_append hprefix tailTrace_1565464
  have hstable : (prefixWord ++ tailWord_1565464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565464).length < 2 ^ (prefixWord ++ tailWord_1565464).sum := by decide
  have hdescent : baseEnd_1565464 < baseStart_1565464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565498 : List Nat := [3, 1, 1, 1, 7, 1, 7]
def baseStart_1565498 : Nat := 118140960795 + 1565498 * 2 ^ 59
def prefixEnd_1565498 : Nat := 4983230072969 + 3 ^ 40 * 1565498 * 2
def baseEnd_1565498 : Nat := 39696441365551664966687

theorem tailTrace_1565498 : CollatzResearch.WordTrace tailWord_1565498 prefixEnd_1565498 39696441365551664966687 := by
  unfold tailWord_1565498
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274600720618896654358287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38065601921650391078288765 14274600720618896654358287)
  ·
    refine ⟨21411901080928344981537431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14274600720618896654358287 21411901080928344981537431)
    ·
      refine ⟨32117851621392517472306147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21411901080928344981537431 32117851621392517472306147)
      ·
        refine ⟨48176777432088776208459221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32117851621392517472306147 48176777432088776208459221)
        ·
          refine ⟨1129143221064580692385763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48176777432088776208459221 1129143221064580692385763)
          ·
            refine ⟨1693714831596871038578645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129143221064580692385763 1693714831596871038578645)
            ·
              refine ⟨39696441365551664966687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1693714831596871038578645 39696441365551664966687)
              ·
                rfl

theorem cell21_1565498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 7].length) (baseStart_1565498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565498 prefixEnd_1565498 := by exact prefixLift 1565498
  have htrace : WordTrace (prefixWord ++ tailWord_1565498) baseStart_1565498 baseEnd_1565498 := by
    simpa [prefixWord, tailWord_1565498, baseEnd_1565498] using wordTrace_append hprefix tailTrace_1565498
  have hstable : (prefixWord ++ tailWord_1565498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565498).length < 2 ^ (prefixWord ++ tailWord_1565498).sum := by decide
  have hdescent : baseEnd_1565498 < baseStart_1565498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565571 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 5]
def baseStart_1565571 : Nat := 118140960795 + 1565571 * 2 ^ 59
def prefixEnd_1565571 : Nat := 4983230072969 + 3 ^ 40 * 1565571 * 2
def baseEnd_1565571 : Nat := 357284631884533079983367

theorem tailTrace_1565571 : CollatzResearch.WordTrace tailWord_1565571 prefixEnd_1565571 357284631884533079983367 := by
  unfold tailWord_1565571
  simp only [CollatzResearch.WordTrace]
  refine ⟨57101065411211120084840567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38067376940807413389893711 57101065411211120084840567)
  ·
    refine ⟨85651598116816680127260851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57101065411211120084840567 85651598116816680127260851)
    ·
      refine ⟨128477397175225020190891277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85651598116816680127260851 128477397175225020190891277)
      ·
        refine ⟨48179023940709382571584229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128477397175225020190891277 48179023940709382571584229)
        ·
          refine ⟨9033566988883009232172043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48179023940709382571584229 9033566988883009232172043)
          ·
            refine ⟨13550350483324513848258065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033566988883009232172043 13550350483324513848258065)
            ·
              refine ⟨10162762862493385386193549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13550350483324513848258065 10162762862493385386193549)
              ·
                refine ⟨3811036073435019519822581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10162762862493385386193549 3811036073435019519822581)
                ·
                  refine ⟨357284631884533079983367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811036073435019519822581 357284631884533079983367)
                  ·
                    rfl

theorem cell21_1565571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_1565571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565571 prefixEnd_1565571 := by exact prefixLift 1565571
  have htrace : WordTrace (prefixWord ++ tailWord_1565571) baseStart_1565571 baseEnd_1565571 := by
    simpa [prefixWord, tailWord_1565571, baseEnd_1565571] using wordTrace_append hprefix tailTrace_1565571
  have hstable : (prefixWord ++ tailWord_1565571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565571).length < 2 ^ (prefixWord ++ tailWord_1565571).sum := by decide
  have hdescent : baseEnd_1565571 < baseStart_1565571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565585 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 8]
def baseStart_1565585 : Nat := 118140960795 + 1565585 * 2 ^ 59
def prefixEnd_1565585 : Nat := 4983230072969 + 3 ^ 40 * 1565585 * 2
def baseEnd_1565585 : Nat := 357287826875272166750005

theorem tailTrace_1565585 : CollatzResearch.WordTrace tailWord_1565585 prefixEnd_1565585 357287826875272166750005 := by
  unfold tailWord_1565585
  simp only [CollatzResearch.WordTrace]
  refine ⟨57101576033160400475850209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38067717355440266983900139 57101576033160400475850209)
  ·
    refine ⟨42826182024870300356887657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57101576033160400475850209 42826182024870300356887657)
    ·
      refine ⟨32119636518652725267665743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42826182024870300356887657 32119636518652725267665743)
      ·
        refine ⟨48179454777979087901498615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32119636518652725267665743 48179454777979087901498615)
        ·
          refine ⟨72269182166968631852247923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48179454777979087901498615 72269182166968631852247923)
          ·
            refine ⟨108403773250452947778371885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72269182166968631852247923 108403773250452947778371885)
            ·
              refine ⟨40651414968919855416889457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108403773250452947778371885 40651414968919855416889457)
              ·
                refine ⟨30488561226689891562667093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40651414968919855416889457 30488561226689891562667093)
                ·
                  refine ⟨357287826875272166750005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30488561226689891562667093 357287826875272166750005)
                  ·
                    rfl

theorem cell21_1565585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_1565585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565585 prefixEnd_1565585 := by exact prefixLift 1565585
  have htrace : WordTrace (prefixWord ++ tailWord_1565585) baseStart_1565585 baseEnd_1565585 := by
    simpa [prefixWord, tailWord_1565585, baseEnd_1565585] using wordTrace_append hprefix tailTrace_1565585
  have hstable : (prefixWord ++ tailWord_1565585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565585).length < 2 ^ (prefixWord ++ tailWord_1565585).sum := by decide
  have hdescent : baseEnd_1565585 < baseStart_1565585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565588 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1565588 : Nat := 118140960795 + 1565588 * 2 ^ 59
def prefixEnd_1565588 : Nat := 4983230072969 + 3 ^ 40 * 1565588 * 2
def baseEnd_1565588 : Nat := 357288511516144828199999

theorem tailTrace_1565588 : CollatzResearch.WordTrace tailWord_1565588 prefixEnd_1565588 357288511516144828199999 := by
  unfold tailWord_1565588
  simp only [CollatzResearch.WordTrace]
  refine ⟨28550842726074765994104709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38067790301433021325472945 28550842726074765994104709)
  ·
    refine ⟨5353283011139018623894633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28550842726074765994104709 5353283011139018623894633)
    ·
      refine ⟨4014962258354263967920975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5353283011139018623894633 4014962258354263967920975)
      ·
        refine ⟨6022443387531395951881463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014962258354263967920975 6022443387531395951881463)
        ·
          refine ⟨9033665081297093927822195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6022443387531395951881463 9033665081297093927822195)
          ·
            refine ⟨13550497621945640891733293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9033665081297093927822195 13550497621945640891733293)
            ·
              refine ⟨5081436608229615334399985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13550497621945640891733293 5081436608229615334399985)
              ·
                refine ⟨3811077456172211500799989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081436608229615334399985 3811077456172211500799989)
                ·
                  refine ⟨357288511516144828199999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811077456172211500799989 357288511516144828199999)
                  ·
                    rfl

theorem cell21_1565588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1565588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565588 prefixEnd_1565588 := by exact prefixLift 1565588
  have htrace : WordTrace (prefixWord ++ tailWord_1565588) baseStart_1565588 baseEnd_1565588 := by
    simpa [prefixWord, tailWord_1565588, baseEnd_1565588] using wordTrace_append hprefix tailTrace_1565588
  have hstable : (prefixWord ++ tailWord_1565588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565588).length < 2 ^ (prefixWord ++ tailWord_1565588).sum := by decide
  have hdescent : baseEnd_1565588 < baseStart_1565588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565647 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 5]
def baseStart_1565647 : Nat := 118140960795 + 1565647 * 2 ^ 59
def prefixEnd_1565647 : Nat := 4983230072969 + 3 ^ 40 * 1565647 * 2
def baseEnd_1565647 : Nat := 357301976119973836716545

theorem tailTrace_1565647 : CollatzResearch.WordTrace tailWord_1565647 prefixEnd_1565647 357301976119973836716545 := by
  unfold tailWord_1565647
  simp only [CollatzResearch.WordTrace]
  refine ⟨57103837358935785064607195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38069224905957190043071463 57103837358935785064607195)
  ·
    refine ⟨85655756038403677596910793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57103837358935785064607195 85655756038403677596910793)
    ·
      refine ⟨64241817028802758197683095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85655756038403677596910793 64241817028802758197683095)
      ·
        refine ⟨96362725543204137296524643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64241817028802758197683095 96362725543204137296524643)
        ·
          refine ⟨144544088314806205944786965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96362725543204137296524643 144544088314806205944786965)
          ·
            refine ⟨6775504139756540903661889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144544088314806205944786965 6775504139756540903661889)
            ·
              refine ⟨5081628104817405677746417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6775504139756540903661889 5081628104817405677746417)
              ·
                refine ⟨3811221078613054258309813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5081628104817405677746417 3811221078613054258309813)
                ·
                  refine ⟨357301976119973836716545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811221078613054258309813 357301976119973836716545)
                  ·
                    rfl

theorem cell21_1565647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_1565647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565647 prefixEnd_1565647 := by exact prefixLift 1565647
  have htrace : WordTrace (prefixWord ++ tailWord_1565647) baseStart_1565647 baseEnd_1565647 := by
    simpa [prefixWord, tailWord_1565647, baseEnd_1565647] using wordTrace_append hprefix tailTrace_1565647
  have hstable : (prefixWord ++ tailWord_1565647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565647).length < 2 ^ (prefixWord ++ tailWord_1565647).sum := by decide
  have hdescent : baseEnd_1565647 < baseStart_1565647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565650 : List Nat := [3, 2, 2, 3, 1, 1, 4, 5]
def baseStart_1565650 : Nat := 118140960795 + 1565650 * 2 ^ 59
def prefixEnd_1565650 : Nat := 4983230072969 + 3 ^ 40 * 1565650 * 2
def baseEnd_1565650 : Nat := 119100886920282166055513

theorem tailTrace_1565650 : CollatzResearch.WordTrace tailWord_1565650 prefixEnd_1565650 119100886920282166055513 := by
  unfold tailWord_1565650
  simp only [CollatzResearch.WordTrace]
  refine ⟨14275986694481229144241601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38069297851949944384644269 14275986694481229144241601)
  ·
    refine ⟨10706990020860921858181201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14275986694481229144241601 10706990020860921858181201)
    ·
      refine ⟨8030242515645691393635901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10706990020860921858181201 8030242515645691393635901)
      ·
        refine ⟨3011340943367134272613463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8030242515645691393635901 3011340943367134272613463)
        ·
          refine ⟨4517011415050701408920195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011340943367134272613463 4517011415050701408920195)
          ·
            refine ⟨6775517122576052113380293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517011415050701408920195 6775517122576052113380293)
            ·
              refine ⟨1270409460483009771258805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6775517122576052113380293 1270409460483009771258805)
              ·
                refine ⟨119100886920282166055513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1270409460483009771258805 119100886920282166055513)
                ·
                  rfl

theorem cell21_1565650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_1565650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565650 prefixEnd_1565650 := by exact prefixLift 1565650
  have htrace : WordTrace (prefixWord ++ tailWord_1565650) baseStart_1565650 baseEnd_1565650 := by
    simpa [prefixWord, tailWord_1565650, baseEnd_1565650] using wordTrace_append hprefix tailTrace_1565650
  have hstable : (prefixWord ++ tailWord_1565650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565650).length < 2 ^ (prefixWord ++ tailWord_1565650).sum := by decide
  have hdescent : baseEnd_1565650 < baseStart_1565650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565692 : List Nat := [2, 2, 2, 1, 2, 3, 1, 8]
def baseStart_1565692 : Nat := 118140960795 + 1565692 * 2 ^ 59
def prefixEnd_1565692 : Nat := 4983230072969 + 3 ^ 40 * 1565692 * 2
def baseEnd_1565692 : Nat := 119104081911021252822151

theorem tailTrace_1565692 : CollatzResearch.WordTrace tailWord_1565692 prefixEnd_1565692 119104081911021252822151 := by
  unfold tailWord_1565692
  simp only [CollatzResearch.WordTrace]
  refine ⟨28552739321886378874997665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38070319095848505166663553 28552739321886378874997665)
  ·
    refine ⟨21414554491414784156248249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28552739321886378874997665 21414554491414784156248249)
    ·
      refine ⟨16060915868561088117186187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21414554491414784156248249 16060915868561088117186187)
      ·
        refine ⟨24091373802841632175779281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16060915868561088117186187 24091373802841632175779281)
        ·
          refine ⟨18068530352131224131834461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24091373802841632175779281 18068530352131224131834461)
          ·
            refine ⟨6775698882049209049437923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18068530352131224131834461 6775698882049209049437923)
            ·
              refine ⟨10163548323073813574156885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6775698882049209049437923 10163548323073813574156885)
              ·
                refine ⟨119104081911021252822151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10163548323073813574156885 119104081911021252822151)
                ·
                  rfl

theorem cell21_1565692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_1565692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565692 prefixEnd_1565692 := by exact prefixLift 1565692
  have htrace : WordTrace (prefixWord ++ tailWord_1565692) baseStart_1565692 baseEnd_1565692 := by
    simpa [prefixWord, tailWord_1565692, baseEnd_1565692] using wordTrace_append hprefix tailTrace_1565692
  have hstable : (prefixWord ++ tailWord_1565692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565692).length < 2 ^ (prefixWord ++ tailWord_1565692).sum := by decide
  have hdescent : baseEnd_1565692 < baseStart_1565692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565740 : List Nat := [2, 2, 1, 1, 1, 2, 5, 4, 3]
def baseStart_1565740 : Nat := 118140960795 + 1565740 * 2 ^ 59
def prefixEnd_1565740 : Nat := 4983230072969 + 3 ^ 40 * 1565740 * 2
def baseEnd_1565740 : Nat := 357323199987026341666355

theorem tailTrace_1565740 : CollatzResearch.WordTrace tailWord_1565740 prefixEnd_1565740 357323199987026341666355 := by
  unfold tailWord_1565740
  simp only [CollatzResearch.WordTrace]
  refine ⟨28553614673799430973871337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38071486231732574631828449 28553614673799430973871337)
  ·
    refine ⟨21415211005349573230403503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28553614673799430973871337 21415211005349573230403503)
    ·
      refine ⟨32122816508024359845605255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21415211005349573230403503 32122816508024359845605255)
      ·
        refine ⟨48184224762036539768407883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32122816508024359845605255 48184224762036539768407883)
        ·
          refine ⟨72276337143054809652611825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48184224762036539768407883 72276337143054809652611825)
          ·
            refine ⟨54207252857291107239458869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72276337143054809652611825 54207252857291107239458869)
            ·
              refine ⟨5081929955371041303699269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54207252857291107239458869 5081929955371041303699269)
              ·
                refine ⟨952861866632070244443613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5081929955371041303699269 952861866632070244443613)
                ·
                  refine ⟨357323199987026341666355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952861866632070244443613 357323199987026341666355)
                  ·
                    rfl

theorem cell21_1565740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_1565740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565740 prefixEnd_1565740 := by exact prefixLift 1565740
  have htrace : WordTrace (prefixWord ++ tailWord_1565740) baseStart_1565740 baseEnd_1565740 := by
    simpa [prefixWord, tailWord_1565740, baseEnd_1565740] using wordTrace_append hprefix tailTrace_1565740
  have hstable : (prefixWord ++ tailWord_1565740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565740).length < 2 ^ (prefixWord ++ tailWord_1565740).sum := by decide
  have hdescent : baseEnd_1565740 < baseStart_1565740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565754 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_1565754 : Nat := 118140960795 + 1565754 * 2 ^ 59
def prefixEnd_1565754 : Nat := 4983230072969 + 3 ^ 40 * 1565754 * 2
def baseEnd_1565754 : Nat := 357326394977765428432993

theorem tailTrace_1565754 : CollatzResearch.WordTrace tailWord_1565754 prefixEnd_1565754 357326394977765428432993 := by
  unfold tailWord_1565754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14276934992387035584688079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38071826646365428225834877 14276934992387035584688079)
  ·
    refine ⟨21415402488580553377032119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14276934992387035584688079 21415402488580553377032119)
    ·
      refine ⟨32123103732870830065548179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21415402488580553377032119 32123103732870830065548179)
      ·
        refine ⟨48184655599306245098322269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32123103732870830065548179 48184655599306245098322269)
        ·
          refine ⟨18069245849739841911870851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48184655599306245098322269 18069245849739841911870851)
          ·
            refine ⟨27103868774609762867806277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18069245849739841911870851 27103868774609762867806277)
            ·
              refine ⟨5081975395239330537713677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27103868774609762867806277 5081975395239330537713677)
              ·
                refine ⟨1905740773214748951642629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5081975395239330537713677 1905740773214748951642629)
                ·
                  refine ⟨357326394977765428432993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1905740773214748951642629 357326394977765428432993)
                  ·
                    rfl

theorem cell21_1565754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_1565754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565754 prefixEnd_1565754 := by exact prefixLift 1565754
  have htrace : WordTrace (prefixWord ++ tailWord_1565754) baseStart_1565754 baseEnd_1565754 := by
    simpa [prefixWord, tailWord_1565754, baseEnd_1565754] using wordTrace_append hprefix tailTrace_1565754
  have hstable : (prefixWord ++ tailWord_1565754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565754).length < 2 ^ (prefixWord ++ tailWord_1565754).sum := by decide
  have hdescent : baseEnd_1565754 < baseStart_1565754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565799 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 5]
def baseStart_1565799 : Nat := 118140960795 + 1565799 * 2 ^ 59
def prefixEnd_1565799 : Nat := 4983230072969 + 3 ^ 40 * 1565799 * 2
def baseEnd_1565799 : Nat := 357336664590855350182901

theorem tailTrace_1565799 : CollatzResearch.WordTrace tailWord_1565799 prefixEnd_1565799 357336664590855350182901 := by
  unfold tailWord_1565799
  simp only [CollatzResearch.WordTrace]
  refine ⟨57109381254385115024140451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38072920836256743349426967 57109381254385115024140451)
  ·
    refine ⟨85664071881577672536210677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57109381254385115024140451 85664071881577672536210677)
    ·
      refine ⟨8031006738897906800269751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85664071881577672536210677 8031006738897906800269751)
      ·
        refine ⟨12046510108346860200404627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8031006738897906800269751 12046510108346860200404627)
        ·
          refine ⟨18069765162520290300606941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12046510108346860200404627 18069765162520290300606941)
          ·
            refine ⟨6776161935945108862727603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18069765162520290300606941 6776161935945108862727603)
            ·
              refine ⟨10164242903917663294091405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6776161935945108862727603 10164242903917663294091405)
              ·
                refine ⟨3811591088969123735284277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10164242903917663294091405 3811591088969123735284277)
                ·
                  refine ⟨357336664590855350182901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3811591088969123735284277 357336664590855350182901)
                  ·
                    rfl

theorem cell21_1565799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_1565799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565799 prefixEnd_1565799 := by exact prefixLift 1565799
  have htrace : WordTrace (prefixWord ++ tailWord_1565799) baseStart_1565799 baseEnd_1565799 := by
    simpa [prefixWord, tailWord_1565799, baseEnd_1565799] using wordTrace_append hprefix tailTrace_1565799
  have hstable : (prefixWord ++ tailWord_1565799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565799).length < 2 ^ (prefixWord ++ tailWord_1565799).sum := by decide
  have hdescent : baseEnd_1565799 < baseStart_1565799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565833 : List Nat := [1, 2, 1, 1, 4, 5, 1, 3, 3]
def baseStart_1565833 : Nat := 118140960795 + 1565833 * 2 ^ 59
def prefixEnd_1565833 : Nat := 4983230072969 + 3 ^ 40 * 1565833 * 2
def baseEnd_1565833 : Nat := 357344423854078846616165

theorem tailTrace_1565833 : CollatzResearch.WordTrace tailWord_1565833 prefixEnd_1565833 357344423854078846616165 := by
  unfold tailWord_1565833
  simp only [CollatzResearch.WordTrace]
  refine ⟨57110621336261938830878153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38073747557507959220585435 57110621336261938830878153)
  ·
    refine ⟨42832966002196454123158615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57110621336261938830878153 42832966002196454123158615)
    ·
      refine ⟨64249449003294681184737923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42832966002196454123158615 64249449003294681184737923)
      ·
        refine ⟨96374173504942021777106885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64249449003294681184737923 96374173504942021777106885)
        ·
          refine ⟨18070157532176629083207541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96374173504942021777106885 18070157532176629083207541)
          ·
            refine ⟨1694077268641558976550707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18070157532176629083207541 1694077268641558976550707)
            ·
              refine ⟨2541115902962338464826061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694077268641558976550707 2541115902962338464826061)
              ·
                refine ⟨952918463610876924309773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2541115902962338464826061 952918463610876924309773)
                ·
                  refine ⟨357344423854078846616165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952918463610876924309773 357344423854078846616165)
                  ·
                    rfl

theorem cell21_1565833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_1565833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565833 prefixEnd_1565833 := by exact prefixLift 1565833
  have htrace : WordTrace (prefixWord ++ tailWord_1565833) baseStart_1565833 baseEnd_1565833 := by
    simpa [prefixWord, tailWord_1565833, baseEnd_1565833] using wordTrace_append hprefix tailTrace_1565833
  have hstable : (prefixWord ++ tailWord_1565833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565833).length < 2 ^ (prefixWord ++ tailWord_1565833).sum := by decide
  have hdescent : baseEnd_1565833 < baseStart_1565833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565850 : List Nat := [3, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_1565850 : Nat := 118140960795 + 1565850 * 2 ^ 59
def prefixEnd_1565850 : Nat := 4983230072969 + 3 ^ 40 * 1565850 * 2
def baseEnd_1565850 : Nat := 357348303485690594832797

theorem tailTrace_1565850 : CollatzResearch.WordTrace tailWord_1565850 prefixEnd_1565850 357348303485690594832797 := by
  unfold tailWord_1565850
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277810344300087683561751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38074160918133567156164669 14277810344300087683561751)
  ·
    refine ⟨21416715516450131525342627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14277810344300087683561751 21416715516450131525342627)
    ·
      refine ⟨32125073274675197288013941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21416715516450131525342627 32125073274675197288013941)
      ·
        refine ⟨3011725619500799745751307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32125073274675197288013941 3011725619500799745751307)
        ·
          refine ⟨4517588429251199618626961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011725619500799745751307 4517588429251199618626961)
          ·
            refine ⟨3388191321938399713970221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4517588429251199618626961 3388191321938399713970221)
            ·
              refine ⟨1270571745726899892738833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3388191321938399713970221 1270571745726899892738833)
              ·
                refine ⟨952928809295174919554125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270571745726899892738833 952928809295174919554125)
                ·
                  refine ⟨357348303485690594832797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952928809295174919554125 357348303485690594832797)
                  ·
                    rfl

theorem cell21_1565850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_1565850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565850 prefixEnd_1565850 := by exact prefixLift 1565850
  have htrace : WordTrace (prefixWord ++ tailWord_1565850) baseStart_1565850 baseEnd_1565850 := by
    simpa [prefixWord, tailWord_1565850, baseEnd_1565850] using wordTrace_append hprefix tailTrace_1565850
  have hstable : (prefixWord ++ tailWord_1565850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565850).length < 2 ^ (prefixWord ++ tailWord_1565850).sum := by decide
  have hdescent : baseEnd_1565850 < baseStart_1565850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565901 : List Nat := [1, 6, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1565901 : Nat := 118140960795 + 1565901 * 2 ^ 59
def prefixEnd_1565901 : Nat := 4983230072969 + 3 ^ 40 * 1565901 * 2
def baseEnd_1565901 : Nat := 357359942380525839482693

theorem tailTrace_1565901 : CollatzResearch.WordTrace tailWord_1565901 prefixEnd_1565901 357359942380525839482693 := by
  unfold tailWord_1565901
  simp only [CollatzResearch.WordTrace]
  refine ⟨57113101500015586444353557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38075401000010390962902371 57113101500015586444353557)
  ·
    refine ⟨2677176632813230614579073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57113101500015586444353557 2677176632813230614579073)
    ·
      refine ⟨2007882474609922960934305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2677176632813230614579073 2007882474609922960934305)
      ·
        refine ⟨1505911855957442220700729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2007882474609922960934305 1505911855957442220700729)
        ·
          refine ⟨1129433891968081665525547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1505911855957442220700729 1129433891968081665525547)
          ·
            refine ⟨1694150837952122498288321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129433891968081665525547 1694150837952122498288321)
            ·
              refine ⟨1270613128464091873716241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694150837952122498288321 1270613128464091873716241)
              ·
                refine ⟨952959846348068905287181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270613128464091873716241 952959846348068905287181)
                ·
                  refine ⟨357359942380525839482693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952959846348068905287181 357359942380525839482693)
                  ·
                    rfl

theorem cell21_1565901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1565901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565901 prefixEnd_1565901 := by exact prefixLift 1565901
  have htrace : WordTrace (prefixWord ++ tailWord_1565901) baseStart_1565901 baseEnd_1565901 := by
    simpa [prefixWord, tailWord_1565901, baseEnd_1565901] using wordTrace_append hprefix tailTrace_1565901
  have hstable : (prefixWord ++ tailWord_1565901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565901).length < 2 ^ (prefixWord ++ tailWord_1565901).sum := by decide
  have hdescent : baseEnd_1565901 < baseStart_1565901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565909 : List Nat := [1, 3, 2, 4, 1, 2, 1, 4, 3]
def baseStart_1565909 : Nat := 118140960795 + 1565909 * 2 ^ 59
def prefixEnd_1565909 : Nat := 4983230072969 + 3 ^ 40 * 1565909 * 2
def baseEnd_1565909 : Nat := 357361768089519603349343

theorem tailTrace_1565909 : CollatzResearch.WordTrace tailWord_1565909 prefixEnd_1565909 357361768089519603349343 := by
  unfold tailWord_1565909
  simp only [CollatzResearch.WordTrace]
  refine ⟨57113393283986603810644781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38075595522657735873763187 57113393283986603810644781)
  ·
    refine ⟨21417522481494976428991793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57113393283986603810644781 21417522481494976428991793)
    ·
      refine ⟨16063141861121232321743845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21417522481494976428991793 16063141861121232321743845)
      ·
        refine ⟨3011839098960231060326971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16063141861121232321743845 3011839098960231060326971)
        ·
          refine ⟨4517758648440346590490457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011839098960231060326971 4517758648440346590490457)
          ·
            refine ⟨3388318986330259942867843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4517758648440346590490457 3388318986330259942867843)
            ·
              refine ⟨5082478479495389914301765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3388318986330259942867843 5082478479495389914301765)
              ·
                refine ⟨952964714905385608931581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5082478479495389914301765 952964714905385608931581)
                ·
                  refine ⟨357361768089519603349343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952964714905385608931581 357361768089519603349343)
                  ·
                    rfl

theorem cell21_1565909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_1565909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565909 prefixEnd_1565909 := by exact prefixLift 1565909
  have htrace : WordTrace (prefixWord ++ tailWord_1565909) baseStart_1565909 baseEnd_1565909 := by
    simpa [prefixWord, tailWord_1565909, baseEnd_1565909] using wordTrace_append hprefix tailTrace_1565909
  have hstable : (prefixWord ++ tailWord_1565909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565909).length < 2 ^ (prefixWord ++ tailWord_1565909).sum := by decide
  have hdescent : baseEnd_1565909 < baseStart_1565909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565920 : List Nat := [2, 1, 1, 3, 1, 4, 3, 6]
def baseStart_1565920 : Nat := 118140960795 + 1565920 * 2 ^ 59
def prefixEnd_1565920 : Nat := 4983230072969 + 3 ^ 40 * 1565920 * 2
def baseEnd_1565920 : Nat := 119121426146462009555329

theorem tailTrace_1565920 : CollatzResearch.WordTrace tailWord_1565920 prefixEnd_1565920 119121426146462009555329 := by
  unfold tailWord_1565920
  simp only [CollatzResearch.WordTrace]
  refine ⟨28556897243473376344647607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38075862991297835126196809 28556897243473376344647607)
  ·
    refine ⟨42835345865210064516971411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28556897243473376344647607 42835345865210064516971411)
    ·
      refine ⟨64253018797815096775457117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42835345865210064516971411 64253018797815096775457117)
      ·
        refine ⟨24094882049180661290796419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64253018797815096775457117 24094882049180661290796419)
        ·
          refine ⟨36142323073770991936194629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24094882049180661290796419 36142323073770991936194629)
          ·
            refine ⟨6776685576332060988036493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36142323073770991936194629 6776685576332060988036493)
            ·
              refine ⟨2541257091124522870513685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6776685576332060988036493 2541257091124522870513685)
              ·
                refine ⟨119121426146462009555329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2541257091124522870513685 119121426146462009555329)
                ·
                  rfl

theorem cell21_1565920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_1565920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565920 prefixEnd_1565920 := by exact prefixLift 1565920
  have htrace : WordTrace (prefixWord ++ tailWord_1565920) baseStart_1565920 baseEnd_1565920 := by
    simpa [prefixWord, tailWord_1565920, baseEnd_1565920] using wordTrace_append hprefix tailTrace_1565920
  have hstable : (prefixWord ++ tailWord_1565920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565920).length < 2 ^ (prefixWord ++ tailWord_1565920).sum := by decide
  have hdescent : baseEnd_1565920 < baseStart_1565920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1565979 : List Nat := [1, 1, 1, 1, 1, 1, 5, 10]
def baseStart_1565979 : Nat := 118140960795 + 1565979 * 2 ^ 59
def prefixEnd_1565979 : Nat := 4983230072969 + 3 ^ 40 * 1565979 * 2
def baseEnd_1565979 : Nat := 119125914347738345727511

theorem tailTrace_1565979 : CollatzResearch.WordTrace tailWord_1565979 prefixEnd_1565979 119125914347738345727511 := by
  unfold tailWord_1565979
  simp only [CollatzResearch.WordTrace]
  refine ⟨57115946393733005765692991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38077297595822003843795327 57115946393733005765692991)
  ·
    refine ⟨85673919590599508648539487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57115946393733005765692991 85673919590599508648539487)
    ·
      refine ⟨128510879385899262972809231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85673919590599508648539487 128510879385899262972809231)
      ·
        refine ⟨192766319078848894459213847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128510879385899262972809231 192766319078848894459213847)
        ·
          refine ⟨289149478618273341688820771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192766319078848894459213847 289149478618273341688820771)
          ·
            refine ⟨433724217927410012533231157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289149478618273341688820771 433724217927410012533231157)
            ·
              refine ⟨40661645430694688674990421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 433724217927410012533231157 40661645430694688674990421)
              ·
                refine ⟨119125914347738345727511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40661645430694688674990421 119125914347738345727511)
                ·
                  rfl

theorem cell21_1565979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 10].length) (baseStart_1565979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1565979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1565979 prefixEnd_1565979 := by exact prefixLift 1565979
  have htrace : WordTrace (prefixWord ++ tailWord_1565979) baseStart_1565979 baseEnd_1565979 := by
    simpa [prefixWord, tailWord_1565979, baseEnd_1565979] using wordTrace_append hprefix tailTrace_1565979
  have hstable : (prefixWord ++ tailWord_1565979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1565979).length < 2 ^ (prefixWord ++ tailWord_1565979).sum := by decide
  have hdescent : baseEnd_1565979 < baseStart_1565979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1565979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566089 : List Nat := [1, 2, 1, 1, 7, 2, 1, 6]
def baseStart_1566089 : Nat := 118140960795 + 1566089 * 2 ^ 59
def prefixEnd_1566089 : Nat := 4983230072969 + 3 ^ 40 * 1566089 * 2
def baseEnd_1566089 : Nat := 119134282180626430116325

theorem tailTrace_1566089 : CollatzResearch.WordTrace tailWord_1566089 prefixEnd_1566089 119134282180626430116325 := by
  unfold tailWord_1566089
  simp only [CollatzResearch.WordTrace]
  refine ⟨57119958423334494552197321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38079972282222996368131547 57119958423334494552197321)
  ·
    refine ⟨42839968817500870914147991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57119958423334494552197321 42839968817500870914147991)
    ·
      refine ⟨64259953226251306371221987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42839968817500870914147991 64259953226251306371221987)
      ·
        refine ⟨96389929839376959556832981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64259953226251306371221987 96389929839376959556832981)
        ·
          refine ⟨2259138980610397489613273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 96389929839376959556832981 2259138980610397489613273)
          ·
            refine ⟨1694354235457798117209955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259138980610397489613273 1694354235457798117209955)
            ·
              refine ⟨2541531353186697175814933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694354235457798117209955 2541531353186697175814933)
              ·
                refine ⟨119134282180626430116325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2541531353186697175814933 119134282180626430116325)
                ·
                  rfl

theorem cell21_1566089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 6].length) (baseStart_1566089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566089 prefixEnd_1566089 := by exact prefixLift 1566089
  have htrace : WordTrace (prefixWord ++ tailWord_1566089) baseStart_1566089 baseEnd_1566089 := by
    simpa [prefixWord, tailWord_1566089, baseEnd_1566089] using wordTrace_append hprefix tailTrace_1566089
  have hstable : (prefixWord ++ tailWord_1566089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566089).length < 2 ^ (prefixWord ++ tailWord_1566089).sum := by decide
  have hdescent : baseEnd_1566089 < baseStart_1566089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566193 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 6]
def baseStart_1566193 : Nat := 118140960795 + 1566193 * 2 ^ 59
def prefixEnd_1566193 : Nat := 4983230072969 + 3 ^ 40 * 1566193 * 2
def baseEnd_1566193 : Nat := 357426580758798220615429

theorem tailTrace_1566193 : CollatzResearch.WordTrace tailWord_1566193 prefixEnd_1566193 357426580758798220615429 := by
  unfold tailWord_1566193
  simp only [CollatzResearch.WordTrace]
  refine ⟨57123751614957720313983233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38082501076638480209322155 57123751614957720313983233)
  ·
    refine ⟨42842813711218290235487425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57123751614957720313983233 42842813711218290235487425)
    ·
      refine ⟨32132110283413717676615569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42842813711218290235487425 32132110283413717676615569)
      ·
        refine ⟨24099082712560288257461677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32132110283413717676615569 24099082712560288257461677)
        ·
          refine ⟨9037156017210108096548129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24099082712560288257461677 9037156017210108096548129)
          ·
            refine ⟨6777867012907581072411097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9037156017210108096548129 6777867012907581072411097)
            ·
              refine ⟨5083400259680685804308323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777867012907581072411097 5083400259680685804308323)
              ·
                refine ⟨7625100389521028706462485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083400259680685804308323 7625100389521028706462485)
                ·
                  refine ⟨357426580758798220615429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7625100389521028706462485 357426580758798220615429)
                  ·
                    rfl

theorem cell21_1566193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_1566193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566193 prefixEnd_1566193 := by exact prefixLift 1566193
  have htrace : WordTrace (prefixWord ++ tailWord_1566193) baseStart_1566193 baseEnd_1566193 := by
    simpa [prefixWord, tailWord_1566193, baseEnd_1566193] using wordTrace_append hprefix tailTrace_1566193
  have hstable : (prefixWord ++ tailWord_1566193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566193).length < 2 ^ (prefixWord ++ tailWord_1566193).sum := by decide
  have hdescent : baseEnd_1566193 < baseStart_1566193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566300 : List Nat := [2, 2, 4, 1, 2, 2, 8]
def baseStart_1566300 : Nat := 118140960795 + 1566300 * 2 ^ 59
def prefixEnd_1566300 : Nat := 4983230072969 + 3 ^ 40 * 1566300 * 2
def baseEnd_1566300 : Nat := 39716777735176645814653

theorem tailTrace_1566300 : CollatzResearch.WordTrace tailWord_1566300 prefixEnd_1566300 39716777735176645814653 := by
  unfold tailWord_1566300
  simp only [CollatzResearch.WordTrace]
  refine ⟨28563827112785038794064177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38085102817046718392085569 28563827112785038794064177)
  ·
    refine ⟨21422870334588779095548133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28563827112785038794064177 21422870334588779095548133)
    ·
      refine ⟨4016788187735396080415275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21422870334588779095548133 4016788187735396080415275)
      ·
        refine ⟨6025182281603094120622913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4016788187735396080415275 6025182281603094120622913)
        ·
          refine ⟨4518886711202320590467185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6025182281603094120622913 4518886711202320590467185)
          ·
            refine ⟨3389165033401740442850389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4518886711202320590467185 3389165033401740442850389)
            ·
              refine ⟨39716777735176645814653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3389165033401740442850389 39716777735176645814653)
              ·
                rfl

theorem cell21_1566300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 8].length) (baseStart_1566300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566300 prefixEnd_1566300 := by exact prefixLift 1566300
  have htrace : WordTrace (prefixWord ++ tailWord_1566300) baseStart_1566300 baseEnd_1566300 := by
    simpa [prefixWord, tailWord_1566300, baseEnd_1566300] using wordTrace_append hprefix tailTrace_1566300
  have hstable : (prefixWord ++ tailWord_1566300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566300).length < 2 ^ (prefixWord ++ tailWord_1566300).sum := by decide
  have hdescent : baseEnd_1566300 < baseStart_1566300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566328 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_1566328 : Nat := 118140960795 + 1566328 * 2 ^ 59
def prefixEnd_1566328 : Nat := 4983230072969 + 3 ^ 40 * 1566328 * 2
def baseEnd_1566328 : Nat := 357457389598067985865153

theorem tailTrace_1566328 : CollatzResearch.WordTrace tailWord_1566328 prefixEnd_1566328 357457389598067985865153 := by
  unfold tailWord_1566328
  simp only [CollatzResearch.WordTrace]
  refine ⟨28564337734734319185073819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38085783646312425580098425 28564337734734319185073819)
  ·
    refine ⟨42846506602101478777610729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28564337734734319185073819 42846506602101478777610729)
    ·
      refine ⟨32134879951576109083208047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42846506602101478777610729 32134879951576109083208047)
      ·
        refine ⟨48202319927364163624812071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32134879951576109083208047 48202319927364163624812071)
        ·
          refine ⟨72303479891046245437218107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48202319927364163624812071 72303479891046245437218107)
          ·
            refine ⟨108455219836569368155827161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72303479891046245437218107 108455219836569368155827161)
            ·
              refine ⟨81341414877427026116870371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108455219836569368155827161 81341414877427026116870371)
              ·
                refine ⟨122012122316140539175305557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81341414877427026116870371 122012122316140539175305557)
                ·
                  refine ⟨357457389598067985865153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122012122316140539175305557 357457389598067985865153)
                  ·
                    rfl

theorem cell21_1566328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_1566328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566328 prefixEnd_1566328 := by exact prefixLift 1566328
  have htrace : WordTrace (prefixWord ++ tailWord_1566328) baseStart_1566328 baseEnd_1566328 := by
    simpa [prefixWord, tailWord_1566328, baseEnd_1566328] using wordTrace_append hprefix tailTrace_1566328
  have hstable : (prefixWord ++ tailWord_1566328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566328).length < 2 ^ (prefixWord ++ tailWord_1566328).sum := by decide
  have hdescent : baseEnd_1566328 < baseStart_1566328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566359 : List Nat := [1, 1, 3, 3, 2, 2, 9]
def baseStart_1566359 : Nat := 118140960795 + 1566359 * 2 ^ 59
def prefixEnd_1566359 : Nat := 4983230072969 + 3 ^ 40 * 1566359 * 2
def baseEnd_1566359 : Nat := 39718273802268757872047

theorem tailTrace_1566359 : CollatzResearch.WordTrace tailWord_1566359 prefixEnd_1566359 39718273802268757872047 := by
  unfold tailWord_1566359
  simp only [CollatzResearch.WordTrace]
  refine ⟨57129806132356330664526131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38086537421570887109684087 57129806132356330664526131)
  ·
    refine ⟨85694709198534495996789197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57129806132356330664526131 85694709198534495996789197)
    ·
      refine ⟨32135515949450435998795949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85694709198534495996789197 32135515949450435998795949)
      ·
        refine ⟨12050818481043913499548481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32135515949450435998795949 12050818481043913499548481)
        ·
          refine ⟨9038113860782935124661361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12050818481043913499548481 9038113860782935124661361)
          ·
            refine ⟨6778585395587201343496021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9038113860782935124661361 6778585395587201343496021)
            ·
              refine ⟨39718273802268757872047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6778585395587201343496021 39718273802268757872047)
              ·
                rfl

theorem cell21_1566359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 9].length) (baseStart_1566359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566359 prefixEnd_1566359 := by exact prefixLift 1566359
  have htrace : WordTrace (prefixWord ++ tailWord_1566359) baseStart_1566359 baseEnd_1566359 := by
    simpa [prefixWord, tailWord_1566359, baseEnd_1566359] using wordTrace_append hprefix tailTrace_1566359
  have hstable : (prefixWord ++ tailWord_1566359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566359).length < 2 ^ (prefixWord ++ tailWord_1566359).sum := by decide
  have hdescent : baseEnd_1566359 < baseStart_1566359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566407 : List Nat := [1, 1, 4, 1, 1, 1, 4, 5, 3]
def baseStart_1566407 : Nat := 118140960795 + 1566407 * 2 ^ 59
def prefixEnd_1566407 : Nat := 4983230072969 + 3 ^ 40 * 1566407 * 2
def baseEnd_1566407 : Nat := 357475418474381404048325

theorem tailTrace_1566407 : CollatzResearch.WordTrace tailWord_1566407 prefixEnd_1566407 357475418474381404048325 := by
  unfold tailWord_1566407
  simp only [CollatzResearch.WordTrace]
  refine ⟨57131556836182434862273475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38087704557454956574848983 57131556836182434862273475)
  ·
    refine ⟨85697335254273652293410213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57131556836182434862273475 85697335254273652293410213)
    ·
      refine ⟨16068250360176309805014415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85697335254273652293410213 16068250360176309805014415)
      ·
        refine ⟨24102375540264464707521623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16068250360176309805014415 24102375540264464707521623)
        ·
          refine ⟨36153563310396697061282435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24102375540264464707521623 36153563310396697061282435)
          ·
            refine ⟨54230344965595045591923653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36153563310396697061282435 54230344965595045591923653)
            ·
              refine ⟨10168189681049071048485685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54230344965595045591923653 10168189681049071048485685)
              ·
                refine ⟨953267782598350410795533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10168189681049071048485685 953267782598350410795533)
                ·
                  refine ⟨357475418474381404048325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 953267782598350410795533 357475418474381404048325)
                  ·
                    rfl

theorem cell21_1566407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 3].length) (baseStart_1566407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566407 prefixEnd_1566407 := by exact prefixLift 1566407
  have htrace : WordTrace (prefixWord ++ tailWord_1566407) baseStart_1566407 baseEnd_1566407 := by
    simpa [prefixWord, tailWord_1566407, baseEnd_1566407] using wordTrace_append hprefix tailTrace_1566407
  have hstable : (prefixWord ++ tailWord_1566407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566407).length < 2 ^ (prefixWord ++ tailWord_1566407).sum := by decide
  have hdescent : baseEnd_1566407 < baseStart_1566407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566517 : List Nat := [1, 3, 3, 1, 4, 2, 1, 3, 3]
def baseStart_1566517 : Nat := 118140960795 + 1566517 * 2 ^ 59
def prefixEnd_1566517 : Nat := 4983230072969 + 3 ^ 40 * 1566517 * 2
def baseEnd_1566517 : Nat := 357500521973045657214767

theorem tailTrace_1566517 : CollatzResearch.WordTrace tailWord_1566517 prefixEnd_1566517 357500521973045657214767 := by
  unfold tailWord_1566517
  simp only [CollatzResearch.WordTrace]
  refine ⟨57135568865783923648777805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38090379243855949099185203 57135568865783923648777805)
  ·
    refine ⟨21425838324668971368291677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57135568865783923648777805 21425838324668971368291677)
    ·
      refine ⟨8034689371750864263109379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21425838324668971368291677 8034689371750864263109379)
      ·
        refine ⟨12052034057626296394664069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8034689371750864263109379 12052034057626296394664069)
        ·
          refine ⟨2259756385804930573999513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12052034057626296394664069 2259756385804930573999513)
          ·
            refine ⟨1694817289353697930499635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2259756385804930573999513 1694817289353697930499635)
            ·
              refine ⟨2542225934030546895749453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694817289353697930499635 2542225934030546895749453)
              ·
                refine ⟨953334725261455085906045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2542225934030546895749453 953334725261455085906045)
                ·
                  refine ⟨357500521973045657214767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 953334725261455085906045 357500521973045657214767)
                  ·
                    rfl

theorem cell21_1566517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_1566517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566517 prefixEnd_1566517 := by exact prefixLift 1566517
  have htrace : WordTrace (prefixWord ++ tailWord_1566517) baseStart_1566517 baseEnd_1566517 := by
    simpa [prefixWord, tailWord_1566517, baseEnd_1566517] using wordTrace_append hprefix tailTrace_1566517
  have hstable : (prefixWord ++ tailWord_1566517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566517).length < 2 ^ (prefixWord ++ tailWord_1566517).sum := by decide
  have hdescent : baseEnd_1566517 < baseStart_1566517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566593 : List Nat := [1, 2, 4, 4, 1, 1, 1, 4, 3]
def baseStart_1566593 : Nat := 118140960795 + 1566593 * 2 ^ 59
def prefixEnd_1566593 : Nat := 4983230072969 + 3 ^ 40 * 1566593 * 2
def baseEnd_1566593 : Nat := 357517866208486413947945

theorem tailTrace_1566593 : CollatzResearch.WordTrace tailWord_1566593 prefixEnd_1566593 357517866208486413947945 := by
  unfold tailWord_1566593
  simp only [CollatzResearch.WordTrace]
  refine ⟨57138340813508588628544433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38092227209005725752362955 57138340813508588628544433)
  ·
    refine ⟨42853755610131441471408325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57138340813508588628544433 42853755610131441471408325)
    ·
      refine ⟨8035079176899645275889061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42853755610131441471408325 8035079176899645275889061)
      ·
        refine ⟨1506577345668683489229199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8035079176899645275889061 1506577345668683489229199)
        ·
          refine ⟨2259866018503025233843799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506577345668683489229199 2259866018503025233843799)
          ·
            refine ⟨3389799027754537850765699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259866018503025233843799 3389799027754537850765699)
            ·
              refine ⟨5084698541631806776148549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3389799027754537850765699 5084698541631806776148549)
              ·
                refine ⟨953380976555963770527853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5084698541631806776148549 953380976555963770527853)
                ·
                  refine ⟨357517866208486413947945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 953380976555963770527853 357517866208486413947945)
                  ·
                    rfl

theorem cell21_1566593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_1566593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566593 prefixEnd_1566593 := by exact prefixLift 1566593
  have htrace : WordTrace (prefixWord ++ tailWord_1566593) baseStart_1566593 baseEnd_1566593 := by
    simpa [prefixWord, tailWord_1566593, baseEnd_1566593] using wordTrace_append hprefix tailTrace_1566593
  have hstable : (prefixWord ++ tailWord_1566593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566593).length < 2 ^ (prefixWord ++ tailWord_1566593).sum := by decide
  have hdescent : baseEnd_1566593 < baseStart_1566593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566618 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_1566618 : Nat := 118140960795 + 1566618 * 2 ^ 59
def prefixEnd_1566618 : Nat := 4983230072969 + 3 ^ 40 * 1566618 * 2
def baseEnd_1566618 : Nat := 357523571549091926031227

theorem tailTrace_1566618 : CollatzResearch.WordTrace tailWord_1566618 prefixEnd_1566618 357523571549091926031227 := by
  unfold tailWord_1566618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14284813159604504474551127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38092835092278678598803005 14284813159604504474551127)
  ·
    refine ⟨21427219739406756711826691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14284813159604504474551127 21427219739406756711826691)
    ·
      refine ⟨32140829609110135067740037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21427219739406756711826691 32140829609110135067740037)
      ·
        refine ⟨6026405551708150325201257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32140829609110135067740037 6026405551708150325201257)
        ·
          refine ⟨4519804163781112743900943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6026405551708150325201257 4519804163781112743900943)
          ·
            refine ⟨6779706245671669115851415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4519804163781112743900943 6779706245671669115851415)
            ·
              refine ⟨10169559368507503673777123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779706245671669115851415 10169559368507503673777123)
              ·
                refine ⟨15254339052761255510665685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10169559368507503673777123 15254339052761255510665685)
                ·
                  refine ⟨357523571549091926031227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15254339052761255510665685 357523571549091926031227)
                  ·
                    rfl

theorem cell21_1566618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_1566618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566618 prefixEnd_1566618 := by exact prefixLift 1566618
  have htrace : WordTrace (prefixWord ++ tailWord_1566618) baseStart_1566618 baseEnd_1566618 := by
    simpa [prefixWord, tailWord_1566618, baseEnd_1566618] using wordTrace_append hprefix tailTrace_1566618
  have hstable : (prefixWord ++ tailWord_1566618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566618).length < 2 ^ (prefixWord ++ tailWord_1566618).sum := by decide
  have hdescent : baseEnd_1566618 < baseStart_1566618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566638 : List Nat := [4, 1, 5, 1, 1, 1, 8]
def baseStart_1566638 : Nat := 118140960795 + 1566638 * 2 ^ 59
def prefixEnd_1566638 : Nat := 4983230072969 + 3 ^ 40 * 1566638 * 2
def baseEnd_1566638 : Nat := 39725348424619592855317

theorem tailTrace_1566638 : CollatzResearch.WordTrace tailWord_1566638 prefixEnd_1566638 39725348424619592855317 := by
  unfold tailWord_1566638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142497762293195164241571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38093321398897040875955045 7142497762293195164241571)
  ·
    refine ⟨10713746643439792746362357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7142497762293195164241571 10713746643439792746362357)
    ·
      refine ⟨1004413747822480569971471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10713746643439792746362357 1004413747822480569971471)
      ·
        refine ⟨1506620621733720854957207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004413747822480569971471 1506620621733720854957207)
        ·
          refine ⟨2259930932600581282435811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506620621733720854957207 2259930932600581282435811)
          ·
            refine ⟨3389896398900871923653717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259930932600581282435811 3389896398900871923653717)
            ·
              refine ⟨39725348424619592855317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3389896398900871923653717 39725348424619592855317)
              ·
                rfl

theorem cell21_1566638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 8].length) (baseStart_1566638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566638 prefixEnd_1566638 := by exact prefixLift 1566638
  have htrace : WordTrace (prefixWord ++ tailWord_1566638) baseStart_1566638 baseEnd_1566638 := by
    simpa [prefixWord, tailWord_1566638, baseEnd_1566638] using wordTrace_append hprefix tailTrace_1566638
  have hstable : (prefixWord ++ tailWord_1566638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566638).length < 2 ^ (prefixWord ++ tailWord_1566638).sum := by decide
  have hdescent : baseEnd_1566638 < baseStart_1566638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566652 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_1566652 : Nat := 118140960795 + 1566652 * 2 ^ 59
def prefixEnd_1566652 : Nat := 4983230072969 + 3 ^ 40 * 1566652 * 2
def baseEnd_1566652 : Nat := 357531330812315422464491

theorem tailTrace_1566652 : CollatzResearch.WordTrace tailWord_1566652 prefixEnd_1566652 357531330812315422464491 := by
  unfold tailWord_1566652
  simp only [CollatzResearch.WordTrace]
  refine ⟨28570246360147420852471105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38093661813529894469961473 28570246360147420852471105)
  ·
    refine ⟨21427684770110565639353329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28570246360147420852471105 21427684770110565639353329)
    ·
      refine ⟨16070763577582924229514997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21427684770110565639353329 16070763577582924229514997)
      ·
        refine ⟨1506634085398399146517031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16070763577582924229514997 1506634085398399146517031)
        ·
          refine ⟨2259951128097598719775547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506634085398399146517031 2259951128097598719775547)
          ·
            refine ⟨3389926692146398079663321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259951128097598719775547 3389926692146398079663321)
            ·
              refine ⟨2542445019109798559747491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389926692146398079663321 2542445019109798559747491)
              ·
                refine ⟨3813667528664697839621237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542445019109798559747491 3813667528664697839621237)
                ·
                  refine ⟨357531330812315422464491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3813667528664697839621237 357531330812315422464491)
                  ·
                    rfl

theorem cell21_1566652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_1566652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566652 prefixEnd_1566652 := by exact prefixLift 1566652
  have htrace : WordTrace (prefixWord ++ tailWord_1566652) baseStart_1566652 baseEnd_1566652 := by
    simpa [prefixWord, tailWord_1566652, baseEnd_1566652] using wordTrace_append hprefix tailTrace_1566652
  have hstable : (prefixWord ++ tailWord_1566652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566652).length < 2 ^ (prefixWord ++ tailWord_1566652).sum := by decide
  have hdescent : baseEnd_1566652 < baseStart_1566652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566725 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 4]
def baseStart_1566725 : Nat := 118140960795 + 1566725 * 2 ^ 59
def prefixEnd_1566725 : Nat := 4983230072969 + 3 ^ 40 * 1566725 * 2
def baseEnd_1566725 : Nat := 357547990406883517747675

theorem tailTrace_1566725 : CollatzResearch.WordTrace tailWord_1566725 prefixEnd_1566725 357547990406883517747675 := by
  unfold tailWord_1566725
  simp only [CollatzResearch.WordTrace]
  refine ⟨57143155249030375172349629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38095436832686916781566419 57143155249030375172349629)
  ·
    refine ⟨21428683218386390689631111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57143155249030375172349629 21428683218386390689631111)
    ·
      refine ⟨32143024827579586034446667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21428683218386390689631111 32143024827579586034446667)
      ·
        refine ⟨48214537241369379051670001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32143024827579586034446667 48214537241369379051670001)
        ·
          refine ⟨36160902931027034288752501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48214537241369379051670001 36160902931027034288752501)
          ·
            refine ⟨3390084649783784464570547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36160902931027034288752501 3390084649783784464570547)
            ·
              refine ⟨5085126974675676696855821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390084649783784464570547 5085126974675676696855821)
              ·
                refine ⟨1906922615503378761320933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5085126974675676696855821 1906922615503378761320933)
                ·
                  refine ⟨357547990406883517747675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1906922615503378761320933 357547990406883517747675)
                  ·
                    rfl

theorem cell21_1566725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_1566725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566725 prefixEnd_1566725 := by exact prefixLift 1566725
  have htrace : WordTrace (prefixWord ++ tailWord_1566725) baseStart_1566725 baseEnd_1566725 := by
    simpa [prefixWord, tailWord_1566725, baseEnd_1566725] using wordTrace_append hprefix tailTrace_1566725
  have hstable : (prefixWord ++ tailWord_1566725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566725).length < 2 ^ (prefixWord ++ tailWord_1566725).sum := by decide
  have hdescent : baseEnd_1566725 < baseStart_1566725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566756 : List Nat := [2, 3, 1, 4, 3, 8]
def baseStart_1566756 : Nat := 118140960795 + 1566756 * 2 ^ 59
def prefixEnd_1566756 : Nat := 4983230072969 + 3 ^ 40 * 1566756 * 2
def baseEnd_1566756 : Nat := 13242780186267938990035

theorem tailTrace_1566756 : CollatzResearch.WordTrace tailWord_1566756 prefixEnd_1566756 13242780186267938990035 := by
  unfold tailWord_1566756
  simp only [CollatzResearch.WordTrace]
  refine ⟨28572142955959033733364061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38096190607945378311152081 28572142955959033733364061)
  ·
    refine ⟨10714553608484637650011523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28572142955959033733364061 10714553608484637650011523)
    ·
      refine ⟨16071830412726956475017285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10714553608484637650011523 16071830412726956475017285)
      ·
        refine ⟨3013468202386304339065741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16071830412726956475017285 3013468202386304339065741)
        ·
          refine ⟨1130050575894864127149653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3013468202386304339065741 1130050575894864127149653)
          ·
            refine ⟨13242780186267938990035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1130050575894864127149653 13242780186267938990035)
            ·
              rfl

theorem cell21_1566756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 8].length) (baseStart_1566756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566756 prefixEnd_1566756 := by exact prefixLift 1566756
  have htrace : WordTrace (prefixWord ++ tailWord_1566756) baseStart_1566756 baseEnd_1566756 := by
    simpa [prefixWord, tailWord_1566756, baseEnd_1566756] using wordTrace_append hprefix tailTrace_1566756
  have hstable : (prefixWord ++ tailWord_1566756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566756).length < 2 ^ (prefixWord ++ tailWord_1566756).sum := by decide
  have hdescent : baseEnd_1566756 < baseStart_1566756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566759 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 4]
def baseStart_1566759 : Nat := 118140960795 + 1566759 * 2 ^ 59
def prefixEnd_1566759 : Nat := 4983230072969 + 3 ^ 40 * 1566759 * 2
def baseEnd_1566759 : Nat := 357555749670107014180939

theorem tailTrace_1566759 : CollatzResearch.WordTrace tailWord_1566759 prefixEnd_1566759 357555749670107014180939 := by
  unfold tailWord_1566759
  simp only [CollatzResearch.WordTrace]
  refine ⟨57144395330907198979087331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38096263553938132652724887 57144395330907198979087331)
  ·
    refine ⟨85716592996360798468630997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57144395330907198979087331 85716592996360798468630997)
    ·
      refine ⟨2008982648352206214108539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 85716592996360798468630997 2008982648352206214108539)
      ·
        refine ⟨3013473972528309321162809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008982648352206214108539 3013473972528309321162809)
        ·
          refine ⟨2260105479396231990872107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3013473972528309321162809 2260105479396231990872107)
          ·
            refine ⟨3390158219094347986308161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260105479396231990872107 3390158219094347986308161)
            ·
              refine ⟨2542618664320760989731121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390158219094347986308161 2542618664320760989731121)
              ·
                refine ⟨1906963998240570742298341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2542618664320760989731121 1906963998240570742298341)
                ·
                  refine ⟨357555749670107014180939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1906963998240570742298341 357555749670107014180939)
                  ·
                    rfl

theorem cell21_1566759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 4].length) (baseStart_1566759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566759 prefixEnd_1566759 := by exact prefixLift 1566759
  have htrace : WordTrace (prefixWord ++ tailWord_1566759) baseStart_1566759 baseEnd_1566759 := by
    simpa [prefixWord, tailWord_1566759, baseEnd_1566759] using wordTrace_append hprefix tailTrace_1566759
  have hstable : (prefixWord ++ tailWord_1566759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566759).length < 2 ^ (prefixWord ++ tailWord_1566759).sum := by decide
  have hdescent : baseEnd_1566759 < baseStart_1566759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566818 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1566818 : Nat := 118140960795 + 1566818 * 2 ^ 59
def prefixEnd_1566818 : Nat := 4983230072969 + 3 ^ 40 * 1566818 * 2
def baseEnd_1566818 : Nat := 357569214273936022697485

theorem tailTrace_1566818 : CollatzResearch.WordTrace tailWord_1566818 prefixEnd_1566818 357569214273936022697485 := by
  unfold tailWord_1566818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14286636809423363013871277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38097698158462301370323405 14286636809423363013871277)
  ·
    refine ⟨5357488803533761130201729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14286636809423363013871277 5357488803533761130201729)
    ·
      refine ⟨4018116602650320847651297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5357488803533761130201729 4018116602650320847651297)
      ·
        refine ⟨3013587451987740635738473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4018116602650320847651297 3013587451987740635738473)
        ·
          refine ⟨2260190588990805476803855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3013587451987740635738473 2260190588990805476803855)
          ·
            refine ⟨3390285883486208215205783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260190588990805476803855 3390285883486208215205783)
            ·
              refine ⟨5085428825229312322808675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390285883486208215205783 5085428825229312322808675)
              ·
                refine ⟨7628143237843968484213013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085428825229312322808675 7628143237843968484213013)
                ·
                  refine ⟨357569214273936022697485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7628143237843968484213013 357569214273936022697485)
                  ·
                    rfl

theorem cell21_1566818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1566818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566818 prefixEnd_1566818 := by exact prefixLift 1566818
  have htrace : WordTrace (prefixWord ++ tailWord_1566818) baseStart_1566818 baseEnd_1566818 := by
    simpa [prefixWord, tailWord_1566818, baseEnd_1566818] using wordTrace_append hprefix tailTrace_1566818
  have hstable : (prefixWord ++ tailWord_1566818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566818).length < 2 ^ (prefixWord ++ tailWord_1566818).sum := by decide
  have hdescent : baseEnd_1566818 < baseStart_1566818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566849 : List Nat := [1, 2, 4, 2, 3, 2, 2, 5]
def baseStart_1566849 : Nat := 118140960795 + 1566849 * 2 ^ 59
def prefixEnd_1566849 : Nat := 4983230072969 + 3 ^ 40 * 1566849 * 2
def baseEnd_1566849 : Nat := 119192096298762285893585

theorem tailTrace_1566849 : CollatzResearch.WordTrace tailWord_1566849 prefixEnd_1566849 119192096298762285893585 := by
  unfold tailWord_1566849
  simp only [CollatzResearch.WordTrace]
  refine ⟨57147677900581144349863601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38098451933720762899909067 57147677900581144349863601)
  ·
    refine ⟨42860758425435858262397701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57147677900581144349863601 42860758425435858262397701)
    ·
      refine ⟨8036392204769223424199569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42860758425435858262397701 8036392204769223424199569)
      ·
        refine ⟨6027294153576917568149677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8036392204769223424199569 6027294153576917568149677)
        ·
          refine ⟨2260235307591344088056129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6027294153576917568149677 2260235307591344088056129)
          ·
            refine ⟨1695176480693508066042097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2260235307591344088056129 1695176480693508066042097)
            ·
              refine ⟨1271382360520131049531573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695176480693508066042097 1271382360520131049531573)
              ·
                refine ⟨119192096298762285893585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1271382360520131049531573 119192096298762285893585)
                ·
                  rfl

theorem cell21_1566849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 5].length) (baseStart_1566849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566849 prefixEnd_1566849 := by exact prefixLift 1566849
  have htrace : WordTrace (prefixWord ++ tailWord_1566849) baseStart_1566849 baseEnd_1566849 := by
    simpa [prefixWord, tailWord_1566849, baseEnd_1566849] using wordTrace_append hprefix tailTrace_1566849
  have hstable : (prefixWord ++ tailWord_1566849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566849).length < 2 ^ (prefixWord ++ tailWord_1566849).sum := by decide
  have hdescent : baseEnd_1566849 < baseStart_1566849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566880 : List Nat := [2, 1, 1, 4, 2, 3, 3, 2, 3]
def baseStart_1566880 : Nat := 118140960795 + 1566880 * 2 ^ 59
def prefixEnd_1566880 : Nat := 4983230072969 + 3 ^ 40 * 1566880 * 2
def baseEnd_1566880 : Nat := 357583363518637692664025

theorem tailTrace_1566880 : CollatzResearch.WordTrace tailWord_1566880 prefixEnd_1566880 357583363518637692664025 := by
  unfold tailWord_1566880
  simp only [CollatzResearch.WordTrace]
  refine ⟨28574404281734418322121047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38099205708979224429494729 28574404281734418322121047)
  ·
    refine ⟨42861606422601627483181571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28574404281734418322121047 42861606422601627483181571)
    ·
      refine ⟨64292409633902441224772357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42861606422601627483181571 64292409633902441224772357)
      ·
        refine ⟨12054826806356707729644817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64292409633902441224772357 12054826806356707729644817)
        ·
          refine ⟨9041120104767530797233613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12054826806356707729644817 9041120104767530797233613)
          ·
            refine ⟨3390420039287824048962605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9041120104767530797233613 3390420039287824048962605)
            ·
              refine ⟨1271407514732934018360977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3390420039287824048962605 1271407514732934018360977)
              ·
                refine ⟨953555636049700513770733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1271407514732934018360977 953555636049700513770733)
                ·
                  refine ⟨357583363518637692664025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 953555636049700513770733 357583363518637692664025)
                  ·
                    rfl

theorem cell21_1566880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_1566880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566880 prefixEnd_1566880 := by exact prefixLift 1566880
  have htrace : WordTrace (prefixWord ++ tailWord_1566880) baseStart_1566880 baseEnd_1566880 := by
    simpa [prefixWord, tailWord_1566880, baseEnd_1566880] using wordTrace_append hprefix tailTrace_1566880
  have hstable : (prefixWord ++ tailWord_1566880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566880).length < 2 ^ (prefixWord ++ tailWord_1566880).sum := by decide
  have hdescent : baseEnd_1566880 < baseStart_1566880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1566905 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 7]
def baseStart_1566905 : Nat := 118140960795 + 1566905 * 2 ^ 59
def prefixEnd_1566905 : Nat := 4983230072969 + 3 ^ 40 * 1566905 * 2
def baseEnd_1566905 : Nat := 357589068859243204747307

theorem tailTrace_1566905 : CollatzResearch.WordTrace tailWord_1566905 prefixEnd_1566905 357589068859243204747307 := by
  unfold tailWord_1566905
  simp only [CollatzResearch.WordTrace]
  refine ⟨57149720388378265913902169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38099813592252177275934779 57149720388378265913902169)
  ·
    refine ⟨42862290291283699435426627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57149720388378265913902169 42862290291283699435426627)
    ·
      refine ⟨64293435436925549153139941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42862290291283699435426627 64293435436925549153139941)
      ·
        refine ⟨12055019144423540466213739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64293435436925549153139941 12055019144423540466213739)
        ·
          refine ⟨18082528716635310699320609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12055019144423540466213739 18082528716635310699320609)
          ·
            refine ⟨13561896537476483024490457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18082528716635310699320609 13561896537476483024490457)
            ·
              refine ⟨10171422403107362268367843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13561896537476483024490457 10171422403107362268367843)
              ·
                refine ⟨15257133604661043402551765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10171422403107362268367843 15257133604661043402551765)
                ·
                  refine ⟨357589068859243204747307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15257133604661043402551765 357589068859243204747307)
                  ·
                    rfl

theorem cell21_1566905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_1566905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1566905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1566905 prefixEnd_1566905 := by exact prefixLift 1566905
  have htrace : WordTrace (prefixWord ++ tailWord_1566905) baseStart_1566905 baseEnd_1566905 := by
    simpa [prefixWord, tailWord_1566905, baseEnd_1566905] using wordTrace_append hprefix tailTrace_1566905
  have hstable : (prefixWord ++ tailWord_1566905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1566905).length < 2 ^ (prefixWord ++ tailWord_1566905).sum := by decide
  have hdescent : baseEnd_1566905 < baseStart_1566905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1566905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567018 : List Nat := [3, 1, 4, 2, 3, 1, 2, 5]
def baseStart_1567018 : Nat := 118140960795 + 1567018 * 2 ^ 59
def prefixEnd_1567018 : Nat := 4983230072969 + 3 ^ 40 * 1567018 * 2
def baseEnd_1567018 : Nat := 119204952332926706454581

theorem tailTrace_1567018 : CollatzResearch.WordTrace tailWord_1567018 prefixEnd_1567018 119204952332926706454581 := by
  unfold tailWord_1567018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14288460459242221553191427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38102561224645924141843805 14288460459242221553191427)
  ·
    refine ⟨21432690688863332329787141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14288460459242221553191427 21432690688863332329787141)
    ·
      refine ⟨4018629504161874811835089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21432690688863332329787141 4018629504161874811835089)
      ·
        refine ⟨3013972128121406108876317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4018629504161874811835089 3013972128121406108876317)
        ·
          refine ⟨1130239548045527290828619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3013972128121406108876317 1130239548045527290828619)
          ·
            refine ⟨1695359322068290936242929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130239548045527290828619 1695359322068290936242929)
            ·
              refine ⟨1271519491551218202182197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695359322068290936242929 1271519491551218202182197)
              ·
                refine ⟨119204952332926706454581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1271519491551218202182197 119204952332926706454581)
                ·
                  rfl

theorem cell21_1567018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_1567018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567018 prefixEnd_1567018 := by exact prefixLift 1567018
  have htrace : WordTrace (prefixWord ++ tailWord_1567018) baseStart_1567018 baseEnd_1567018 := by
    simpa [prefixWord, tailWord_1567018, baseEnd_1567018] using wordTrace_append hprefix tailTrace_1567018
  have hstable : (prefixWord ++ tailWord_1567018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567018).length < 2 ^ (prefixWord ++ tailWord_1567018).sum := by decide
  have hdescent : baseEnd_1567018 < baseStart_1567018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567105 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 4]
def baseStart_1567105 : Nat := 118140960795 + 1567105 * 2 ^ 59
def prefixEnd_1567105 : Nat := 4983230072969 + 3 ^ 40 * 1567105 * 2
def baseEnd_1567105 : Nat := 357634711584087301413565

theorem tailTrace_1567105 : CollatzResearch.WordTrace tailWord_1567105 prefixEnd_1567105 357634711584087301413565 := by
  unfold tailWord_1567105
  simp only [CollatzResearch.WordTrace]
  refine ⟨57157014987653700071182769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38104676658435800047455179 57157014987653700071182769)
  ·
    refine ⟨42867761240740275053387077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57157014987653700071182769 42867761240740275053387077)
    ·
      refine ⟨8037705232638801572510077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42867761240740275053387077 8037705232638801572510077)
      ·
        refine ⟨3014139462239550589691279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8037705232638801572510077 3014139462239550589691279)
        ·
          refine ⟨4521209193359325884536919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014139462239550589691279 4521209193359325884536919)
          ·
            refine ⟨6781813790038988826805379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521209193359325884536919 6781813790038988826805379)
            ·
              refine ⟨10172720685058483240208069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781813790038988826805379 10172720685058483240208069)
              ·
                refine ⟨1907385128448465607539013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10172720685058483240208069 1907385128448465607539013)
                ·
                  refine ⟨357634711584087301413565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1907385128448465607539013 357634711584087301413565)
                  ·
                    rfl

theorem cell21_1567105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_1567105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567105 prefixEnd_1567105 := by exact prefixLift 1567105
  have htrace : WordTrace (prefixWord ++ tailWord_1567105) baseStart_1567105 baseEnd_1567105 := by
    simpa [prefixWord, tailWord_1567105, baseEnd_1567105] using wordTrace_append hprefix tailTrace_1567105
  have hstable : (prefixWord ++ tailWord_1567105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567105).length < 2 ^ (prefixWord ++ tailWord_1567105).sum := by decide
  have hdescent : baseEnd_1567105 < baseStart_1567105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567156 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1567156 : Nat := 118140960795 + 1567156 * 2 ^ 59
def prefixEnd_1567156 : Nat := 4983230072969 + 3 ^ 40 * 1567156 * 2
def baseEnd_1567156 : Nat := 357646350478922546063461

theorem tailTrace_1567156 : CollatzResearch.WordTrace tailWord_1567156 prefixEnd_1567156 357646350478922546063461 := by
  unfold tailWord_1567156
  simp only [CollatzResearch.WordTrace]
  refine ⟨28579437555234467890644661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38105916740312623854192881 28579437555234467890644661)
  ·
    refine ⟨2679322270803231364747937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28579437555234467890644661 2679322270803231364747937)
    ·
      refine ⟨2009491703102423523560953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2679322270803231364747937 2009491703102423523560953)
      ·
        refine ⟨1507118777326817642670715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2009491703102423523560953 1507118777326817642670715)
        ·
          refine ⟨2260678165990226464006073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507118777326817642670715 2260678165990226464006073)
          ·
            refine ⟨1695508624492669848004555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2260678165990226464006073 1695508624492669848004555)
            ·
              refine ⟨2543262936739004772006833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695508624492669848004555 2543262936739004772006833)
              ·
                refine ⟨1907447202554253579005125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2543262936739004772006833 1907447202554253579005125)
                ·
                  refine ⟨357646350478922546063461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1907447202554253579005125 357646350478922546063461)
                  ·
                    rfl

theorem cell21_1567156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1567156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567156 prefixEnd_1567156 := by exact prefixLift 1567156
  have htrace : WordTrace (prefixWord ++ tailWord_1567156) baseStart_1567156 baseEnd_1567156 := by
    simpa [prefixWord, tailWord_1567156, baseEnd_1567156] using wordTrace_append hprefix tailTrace_1567156
  have hstable : (prefixWord ++ tailWord_1567156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567156).length < 2 ^ (prefixWord ++ tailWord_1567156).sum := by decide
  have hdescent : baseEnd_1567156 < baseStart_1567156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567178 : List Nat := [3, 1, 2, 1, 2, 2, 2, 8]
def baseStart_1567178 : Nat := 118140960795 + 1567178 * 2 ^ 59
def prefixEnd_1567178 : Nat := 4983230072969 + 3 ^ 40 * 1567178 * 2
def baseEnd_1567178 : Nat := 119217123726218465565583

theorem tailTrace_1567178 : CollatzResearch.WordTrace tailWord_1567178 prefixEnd_1567178 119217123726218465565583 := by
  unfold tailWord_1567178
  simp only [CollatzResearch.WordTrace]
  refine ⟨14289919379097308384647547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38106451677592822359060125 14289919379097308384647547)
  ·
    refine ⟨21434879068645962576971321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14289919379097308384647547 21434879068645962576971321)
    ·
      refine ⟨16076159301484471932728491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21434879068645962576971321 16076159301484471932728491)
      ·
        refine ⟨24114238952226707899092737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16076159301484471932728491 24114238952226707899092737)
        ·
          refine ⟨18085679214170030924319553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24114238952226707899092737 18085679214170030924319553)
          ·
            refine ⟨13564259410627523193239665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18085679214170030924319553 13564259410627523193239665)
            ·
              refine ⟨10173194557970642394929749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13564259410627523193239665 10173194557970642394929749)
              ·
                refine ⟨119217123726218465565583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10173194557970642394929749 119217123726218465565583)
                ·
                  rfl

theorem cell21_1567178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_1567178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567178 prefixEnd_1567178 := by exact prefixLift 1567178
  have htrace : WordTrace (prefixWord ++ tailWord_1567178) baseStart_1567178 baseEnd_1567178 := by
    simpa [prefixWord, tailWord_1567178, baseEnd_1567178] using wordTrace_append hprefix tailTrace_1567178
  have hstable : (prefixWord ++ tailWord_1567178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567178).length < 2 ^ (prefixWord ++ tailWord_1567178).sum := by decide
  have hdescent : baseEnd_1567178 < baseStart_1567178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567271 : List Nat := [1, 1, 7, 2, 10]
def baseStart_1567271 : Nat := 118140960795 + 1567271 * 2 ^ 59
def prefixEnd_1567271 : Nat := 4983230072969 + 3 ^ 40 * 1567271 * 2
def baseEnd_1567271 : Nat := 4415711049947011131439

theorem tailTrace_1567271 : CollatzResearch.WordTrace tailWord_1567271 prefixEnd_1567271 4415711049947011131439 := by
  unfold tailWord_1567271
  simp only [CollatzResearch.WordTrace]
  refine ⟨57163069505052310421725667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38108713003368206947817111 57163069505052310421725667)
  ·
    refine ⟨85744604257578465632588501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57163069505052310421725667 85744604257578465632588501)
    ·
      refine ⟨2009639162286995288263793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 85744604257578465632588501 2009639162286995288263793)
      ·
        refine ⟨1507229371715246466197845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2009639162286995288263793 1507229371715246466197845)
        ·
          refine ⟨4415711049947011131439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1507229371715246466197845 4415711049947011131439)
          ·
            rfl

theorem cell21_1567271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 10].length) (baseStart_1567271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567271 prefixEnd_1567271 := by exact prefixLift 1567271
  have htrace : WordTrace (prefixWord ++ tailWord_1567271) baseStart_1567271 baseEnd_1567271 := by
    simpa [prefixWord, tailWord_1567271, baseEnd_1567271] using wordTrace_append hprefix tailTrace_1567271
  have hstable : (prefixWord ++ tailWord_1567271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567271).length < 2 ^ (prefixWord ++ tailWord_1567271).sum := by decide
  have hdescent : baseEnd_1567271 < baseStart_1567271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567285 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 5]
def baseStart_1567285 : Nat := 118140960795 + 1567285 * 2 ^ 59
def prefixEnd_1567285 : Nat := 4983230072969 + 3 ^ 40 * 1567285 * 2
def baseEnd_1567285 : Nat := 357675790036446988413197

theorem tailTrace_1567285 : CollatzResearch.WordTrace tailWord_1567285 prefixEnd_1567285 357675790036446988413197 := by
  unfold tailWord_1567285
  simp only [CollatzResearch.WordTrace]
  refine ⟨57163580127001590812735309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38109053418001060541823539 57163580127001590812735309)
  ·
    refine ⟨21436342547625596554775741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57163580127001590812735309 21436342547625596554775741)
    ·
      refine ⟨8038628455359598708040903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21436342547625596554775741 8038628455359598708040903)
      ·
        refine ⟨12057942683039398062061355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8038628455359598708040903 12057942683039398062061355)
        ·
          refine ⟨18086914024559097093092033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12057942683039398062061355 18086914024559097093092033)
          ·
            refine ⟨13565185518419322819819025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18086914024559097093092033 13565185518419322819819025)
            ·
              refine ⟨10173889138814492114864269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13565185518419322819819025 10173889138814492114864269)
              ·
                refine ⟨3815208427055434543074101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10173889138814492114864269 3815208427055434543074101)
                ·
                  refine ⟨357675790036446988413197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3815208427055434543074101 357675790036446988413197)
                  ·
                    rfl

theorem cell21_1567285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_1567285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567285 prefixEnd_1567285 := by exact prefixLift 1567285
  have htrace : WordTrace (prefixWord ++ tailWord_1567285) baseStart_1567285 baseEnd_1567285 := by
    simpa [prefixWord, tailWord_1567285, baseEnd_1567285] using wordTrace_append hprefix tailTrace_1567285
  have hstable : (prefixWord ++ tailWord_1567285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567285).length < 2 ^ (prefixWord ++ tailWord_1567285).sum := by decide
  have hdescent : baseEnd_1567285 < baseStart_1567285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567361 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 5]
def baseStart_1567361 : Nat := 118140960795 + 1567361 * 2 ^ 59
def prefixEnd_1567361 : Nat := 4983230072969 + 3 ^ 40 * 1567361 * 2
def baseEnd_1567361 : Nat := 357693134271887745146375

theorem tailTrace_1567361 : CollatzResearch.WordTrace tailWord_1567361 prefixEnd_1567361 357693134271887745146375 := by
  unfold tailWord_1567361
  simp only [CollatzResearch.WordTrace]
  refine ⟨57166352074726255792501937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38110901383150837195001291 57166352074726255792501937)
  ·
    refine ⟨42874764056044691844376453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57166352074726255792501937 42874764056044691844376453)
    ·
      refine ⟨8039018260508379720820585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42874764056044691844376453 8039018260508379720820585)
      ·
        refine ⟨6029263695381284790615439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8039018260508379720820585 6029263695381284790615439)
        ·
          refine ⟨9043895543071927185923159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029263695381284790615439 9043895543071927185923159)
          ·
            refine ⟨13565843314607890778884739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9043895543071927185923159 13565843314607890778884739)
            ·
              refine ⟨20348764971911836168327109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13565843314607890778884739 20348764971911836168327109)
              ·
                refine ⟨3815393432233469281561333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20348764971911836168327109 3815393432233469281561333)
                ·
                  refine ⟨357693134271887745146375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3815393432233469281561333 357693134271887745146375)
                  ·
                    rfl

theorem cell21_1567361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_1567361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567361 prefixEnd_1567361 := by exact prefixLift 1567361
  have htrace : WordTrace (prefixWord ++ tailWord_1567361) baseStart_1567361 baseEnd_1567361 := by
    simpa [prefixWord, tailWord_1567361, baseEnd_1567361] using wordTrace_append hprefix tailTrace_1567361
  have hstable : (prefixWord ++ tailWord_1567361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567361).length < 2 ^ (prefixWord ++ tailWord_1567361).sum := by decide
  have hdescent : baseEnd_1567361 < baseStart_1567361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567364 : List Nat := [2, 3, 2, 1, 3, 3, 2, 5]
def baseStart_1567364 : Nat := 118140960795 + 1567364 * 2 ^ 59
def prefixEnd_1567364 : Nat := 4983230072969 + 3 ^ 40 * 1567364 * 2
def baseEnd_1567364 : Nat := 119231272970920135532123

theorem tailTrace_1567364 : CollatzResearch.WordTrace tailWord_1567364 prefixEnd_1567364 119231272970920135532123 := by
  unfold tailWord_1567364
  simp only [CollatzResearch.WordTrace]
  refine ⟨28583230746857693652430573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38110974329143591536574097 28583230746857693652430573)
  ·
    refine ⟨10718711530071635119661465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28583230746857693652430573 10718711530071635119661465)
    ·
      refine ⟨8039033647553726339746099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10718711530071635119661465 8039033647553726339746099)
      ·
        refine ⟨12058550471330589509619149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8039033647553726339746099 12058550471330589509619149)
        ·
          refine ⟨4521956426748971066107181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12058550471330589509619149 4521956426748971066107181)
          ·
            refine ⟨1695733660030864149790193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4521956426748971066107181 1695733660030864149790193)
            ·
              refine ⟨1271800245023148112342645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695733660030864149790193 1271800245023148112342645)
              ·
                refine ⟨119231272970920135532123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1271800245023148112342645 119231272970920135532123)
                ·
                  rfl

theorem cell21_1567364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_1567364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567364 prefixEnd_1567364 := by exact prefixLift 1567364
  have htrace : WordTrace (prefixWord ++ tailWord_1567364) baseStart_1567364 baseEnd_1567364 := by
    simpa [prefixWord, tailWord_1567364, baseEnd_1567364] using wordTrace_append hprefix tailTrace_1567364
  have hstable : (prefixWord ++ tailWord_1567364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567364).length < 2 ^ (prefixWord ++ tailWord_1567364).sum := by decide
  have hdescent : baseEnd_1567364 < baseStart_1567364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567617 : List Nat := [1, 2, 4, 14]
def baseStart_1567617 : Nat := 118140960795 + 1567617 * 2 ^ 59
def prefixEnd_1567617 : Nat := 4983230072969 + 3 ^ 40 * 1567617 * 2
def baseEnd_1567617 : Nat := 1472228629463737402795

theorem tailTrace_1567617 : CollatzResearch.WordTrace tailWord_1567617 prefixEnd_1567617 1472228629463737402795 := by
  unfold tailWord_1567617
  simp only [CollatzResearch.WordTrace]
  refine ⟨57175689161798811513821105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38117126107865874342547403 57175689161798811513821105)
  ·
    refine ⟨42881766871349108635365829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57175689161798811513821105 42881766871349108635365829)
    ·
      refine ⟨8040331288377957869131093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42881766871349108635365829 8040331288377957869131093)
      ·
        refine ⟨1472228629463737402795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8040331288377957869131093 1472228629463737402795)
        ·
          rfl

theorem cell21_1567617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 14].length) (baseStart_1567617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567617 prefixEnd_1567617 := by exact prefixLift 1567617
  have htrace : WordTrace (prefixWord ++ tailWord_1567617) baseStart_1567617 baseEnd_1567617 := by
    simpa [prefixWord, tailWord_1567617, baseEnd_1567617] using wordTrace_append hprefix tailTrace_1567617
  have hstable : (prefixWord ++ tailWord_1567617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567617).length < 2 ^ (prefixWord ++ tailWord_1567617).sum := by decide
  have hdescent : baseEnd_1567617 < baseStart_1567617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567623 : List Nat := [1, 1, 4, 2, 3, 1, 4, 2, 3]
def baseStart_1567623 : Nat := 118140960795 + 1567623 * 2 ^ 59
def prefixEnd_1567623 : Nat := 4983230072969 + 3 ^ 40 * 1567623 * 2
def baseEnd_1567623 : Nat := 357752926241433511779173

theorem tailTrace_1567623 : CollatzResearch.WordTrace tailWord_1567623 prefixEnd_1567623 357752926241433511779173 := by
  unfold tailWord_1567623
  simp only [CollatzResearch.WordTrace]
  refine ⟨57175907999777074538539523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38117271999851383025693015 57175907999777074538539523)
  ·
    refine ⟨85763861999665611807809285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57175907999777074538539523 85763861999665611807809285)
    ·
      refine ⟨16080724124937302213964241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85763861999665611807809285 16080724124937302213964241)
      ·
        refine ⟨12060543093702976660473181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16080724124937302213964241 12060543093702976660473181)
        ·
          refine ⟨4522703660138616247677443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12060543093702976660473181 4522703660138616247677443)
          ·
            refine ⟨6784055490207924371516165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522703660138616247677443 6784055490207924371516165)
            ·
              refine ⟨1272010404413985819659281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6784055490207924371516165 1272010404413985819659281)
              ·
                refine ⟨954007803310489364744461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1272010404413985819659281 954007803310489364744461)
                ·
                  refine ⟨357752926241433511779173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954007803310489364744461 357752926241433511779173)
                  ·
                    rfl

theorem cell21_1567623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 3].length) (baseStart_1567623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567623 prefixEnd_1567623 := by exact prefixLift 1567623
  have htrace : WordTrace (prefixWord ++ tailWord_1567623) baseStart_1567623 baseEnd_1567623 := by
    simpa [prefixWord, tailWord_1567623, baseEnd_1567623] using wordTrace_append hprefix tailTrace_1567623
  have hstable : (prefixWord ++ tailWord_1567623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567623).length < 2 ^ (prefixWord ++ tailWord_1567623).sum := by decide
  have hdescent : baseEnd_1567623 < baseStart_1567623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567648 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_1567648 : Nat := 118140960795 + 1567648 * 2 ^ 59
def prefixEnd_1567648 : Nat := 4983230072969 + 3 ^ 40 * 1567648 * 2
def baseEnd_1567648 : Nat := 357758631582039023862455

theorem tailTrace_1567648 : CollatzResearch.WordTrace tailWord_1567648 prefixEnd_1567648 357758631582039023862455 := by
  unfold tailWord_1567648
  simp only [CollatzResearch.WordTrace]
  refine ⟨28588409912343251904099799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38117879883124335872133065 28588409912343251904099799)
  ·
    refine ⟨42882614868514877856149699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28588409912343251904099799 42882614868514877856149699)
    ·
      refine ⟨64323922302772316784224549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42882614868514877856149699 64323922302772316784224549)
      ·
        refine ⟨12060735431769809397042103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64323922302772316784224549 12060735431769809397042103)
        ·
          refine ⟨18091103147654714095563155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12060735431769809397042103 18091103147654714095563155)
          ·
            refine ⟨27136654721482071143344733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18091103147654714095563155 27136654721482071143344733)
            ·
              refine ⟨10176245520555776678754275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27136654721482071143344733 10176245520555776678754275)
              ·
                refine ⟨15264368280833665018131413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10176245520555776678754275 15264368280833665018131413)
                ·
                  refine ⟨357758631582039023862455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15264368280833665018131413 357758631582039023862455)
                  ·
                    rfl

theorem cell21_1567648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_1567648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567648 prefixEnd_1567648 := by exact prefixLift 1567648
  have htrace : WordTrace (prefixWord ++ tailWord_1567648) baseStart_1567648 baseEnd_1567648 := by
    simpa [prefixWord, tailWord_1567648, baseEnd_1567648] using wordTrace_append hprefix tailTrace_1567648
  have hstable : (prefixWord ++ tailWord_1567648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567648).length < 2 ^ (prefixWord ++ tailWord_1567648).sum := by decide
  have hdescent : baseEnd_1567648 < baseStart_1567648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567679 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 4]
def baseStart_1567679 : Nat := 118140960795 + 1567679 * 2 ^ 59
def prefixEnd_1567679 : Nat := 4983230072969 + 3 ^ 40 * 1567679 * 2
def baseEnd_1567679 : Nat := 357765706204389858845725

theorem tailTrace_1567679 : CollatzResearch.WordTrace tailWord_1567679 prefixEnd_1567679 357765706204389858845725 := by
  unfold tailWord_1567679
  simp only [CollatzResearch.WordTrace]
  refine ⟨57177950487574196102578091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38118633658382797401718727 57177950487574196102578091)
  ·
    refine ⟨85766925731361294153867137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57177950487574196102578091 85766925731361294153867137)
    ·
      refine ⟨64325194298520970615400353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85766925731361294153867137 64325194298520970615400353)
      ·
        refine ⟨48243895723890727961550265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64325194298520970615400353 48243895723890727961550265)
        ·
          refine ⟨36182921792918045971162699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48243895723890727961550265 36182921792918045971162699)
          ·
            refine ⟨54274382689377068956744049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36182921792918045971162699 54274382689377068956744049)
            ·
              refine ⟨40705787017032801717558037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54274382689377068956744049 40705787017032801717558037)
              ·
                refine ⟨1908083766423412580510533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40705787017032801717558037 1908083766423412580510533)
                ·
                  refine ⟨357765706204389858845725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908083766423412580510533 357765706204389858845725)
                  ·
                    rfl

theorem cell21_1567679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 4].length) (baseStart_1567679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567679 prefixEnd_1567679 := by exact prefixLift 1567679
  have htrace : WordTrace (prefixWord ++ tailWord_1567679) baseStart_1567679 baseEnd_1567679 := by
    simpa [prefixWord, tailWord_1567679, baseEnd_1567679] using wordTrace_append hprefix tailTrace_1567679
  have hstable : (prefixWord ++ tailWord_1567679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567679).length < 2 ^ (prefixWord ++ tailWord_1567679).sum := by decide
  have hdescent : baseEnd_1567679 < baseStart_1567679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567733 : List Nat := [1, 3, 5, 2, 1, 1, 3, 2, 3]
def baseStart_1567733 : Nat := 118140960795 + 1567733 * 2 ^ 59
def prefixEnd_1567733 : Nat := 4983230072969 + 3 ^ 40 * 1567733 * 2
def baseEnd_1567733 : Nat := 357778029740097764945615

theorem tailTrace_1567733 : CollatzResearch.WordTrace tailWord_1567733 prefixEnd_1567733 357778029740097764945615 := by
  unfold tailWord_1567733
  simp only [CollatzResearch.WordTrace]
  refine ⟨57179920029378563325043853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38119946686252375550029235 57179920029378563325043853)
  ·
    refine ⟨21442470011016961246891445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57179920029378563325043853 21442470011016961246891445)
    ·
      refine ⟨2010231563532840116896073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21442470011016961246891445 2010231563532840116896073)
      ·
        refine ⟨1507673672649630087672055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2010231563532840116896073 1507673672649630087672055)
        ·
          refine ⟨2261510508974445131508083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507673672649630087672055 2261510508974445131508083)
          ·
            refine ⟨3392265763461667697262125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261510508974445131508083 3392265763461667697262125)
            ·
              refine ⟨1272099661298125386473297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3392265763461667697262125 1272099661298125386473297)
              ·
                refine ⟨954074745973594039854973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1272099661298125386473297 954074745973594039854973)
                ·
                  refine ⟨357778029740097764945615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954074745973594039854973 357778029740097764945615)
                  ·
                    rfl

theorem cell21_1567733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_1567733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567733 prefixEnd_1567733 := by exact prefixLift 1567733
  have htrace : WordTrace (prefixWord ++ tailWord_1567733) baseStart_1567733 baseEnd_1567733 := by
    simpa [prefixWord, tailWord_1567733, baseEnd_1567733] using wordTrace_append hprefix tailTrace_1567733
  have hstable : (prefixWord ++ tailWord_1567733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567733).length < 2 ^ (prefixWord ++ tailWord_1567733).sum := by decide
  have hdescent : baseEnd_1567733 < baseStart_1567733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567769 : List Nat := [1, 2, 1, 2, 1, 1, 6, 7]
def baseStart_1567769 : Nat := 118140960795 + 1567769 * 2 ^ 59
def prefixEnd_1567769 : Nat := 4983230072969 + 3 ^ 40 * 1567769 * 2
def baseEnd_1567769 : Nat := 119262081810189900781847

theorem tailTrace_1567769 : CollatzResearch.WordTrace tailWord_1567769 prefixEnd_1567769 119262081810189900781847 := by
  unfold tailWord_1567769
  simp only [CollatzResearch.WordTrace]
  refine ⟨57181233057248141473354361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38120822038165427648902907 57181233057248141473354361)
  ·
    refine ⟨42885924792936106105015771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57181233057248141473354361 42885924792936106105015771)
    ·
      refine ⟨64328887189404159157523657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42885924792936106105015771 64328887189404159157523657)
      ·
        refine ⟨48246665392053119368142743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64328887189404159157523657 48246665392053119368142743)
        ·
          refine ⟨72369998088079679052214115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48246665392053119368142743 72369998088079679052214115)
          ·
            refine ⟨108554997132119518578321173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72369998088079679052214115 108554997132119518578321173)
            ·
              refine ⟨5088515490568102433358805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108554997132119518578321173 5088515490568102433358805)
              ·
                refine ⟨119262081810189900781847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5088515490568102433358805 119262081810189900781847)
                ·
                  rfl

theorem cell21_1567769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 7].length) (baseStart_1567769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567769 prefixEnd_1567769 := by exact prefixLift 1567769
  have htrace : WordTrace (prefixWord ++ tailWord_1567769) baseStart_1567769 baseEnd_1567769 := by
    simpa [prefixWord, tailWord_1567769, baseEnd_1567769] using wordTrace_append hprefix tailTrace_1567769
  have hstable : (prefixWord ++ tailWord_1567769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567769).length < 2 ^ (prefixWord ++ tailWord_1567769).sum := by decide
  have hdescent : baseEnd_1567769 < baseStart_1567769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567786 : List Nat := [3, 1, 4, 1, 3, 9]
def baseStart_1567786 : Nat := 118140960795 + 1567786 * 2 ^ 59
def prefixEnd_1567786 : Nat := 4983230072969 + 3 ^ 40 * 1567786 * 2
def baseEnd_1567786 : Nat := 13251486113414127798599

theorem tailTrace_1567786 : CollatzResearch.WordTrace tailWord_1567786 prefixEnd_1567786 13251486113414127798599 := by
  unfold tailWord_1567786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14295463274546638344180803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38121235398791035584482141 14295463274546638344180803)
  ·
    refine ⟨21443194911819957516271205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14295463274546638344180803 21443194911819957516271205)
    ·
      refine ⟨4020599045966242034300851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21443194911819957516271205 4020599045966242034300851)
      ·
        refine ⟨6030898568949363051451277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020599045966242034300851 6030898568949363051451277)
        ·
          refine ⟨2261586963356011144294229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6030898568949363051451277 2261586963356011144294229)
          ·
            refine ⟨13251486113414127798599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2261586963356011144294229 13251486113414127798599)
            ·
              rfl

theorem cell21_1567786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 9].length) (baseStart_1567786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567786 prefixEnd_1567786 := by exact prefixLift 1567786
  have htrace : WordTrace (prefixWord ++ tailWord_1567786) baseStart_1567786 baseEnd_1567786 := by
    simpa [prefixWord, tailWord_1567786, baseEnd_1567786] using wordTrace_append hprefix tailTrace_1567786
  have hstable : (prefixWord ++ tailWord_1567786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567786).length < 2 ^ (prefixWord ++ tailWord_1567786).sum := by decide
  have hdescent : baseEnd_1567786 < baseStart_1567786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567845 : List Nat := [1, 3, 1, 3, 2, 1, 10]
def baseStart_1567845 : Nat := 118140960795 + 1567845 * 2 ^ 59
def prefixEnd_1567845 : Nat := 4983230072969 + 3 ^ 40 * 1567845 * 2
def baseEnd_1567845 : Nat := 39755954407334495453191

theorem tailTrace_1567845 : CollatzResearch.WordTrace tailWord_1567845 prefixEnd_1567845 39755954407334495453191 := by
  unfold tailWord_1567845
  simp only [CollatzResearch.WordTrace]
  refine ⟨57184005004972806453120989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38122670003315204302080659 57184005004972806453120989)
  ·
    refine ⟨21444001876864802419920371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57184005004972806453120989 21444001876864802419920371)
    ·
      refine ⟨32166002815297203629880557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21444001876864802419920371 32166002815297203629880557)
      ·
        refine ⟨12062251055736451361205209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32166002815297203629880557 12062251055736451361205209)
        ·
          refine ⟨9046688291802338520903907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12062251055736451361205209 9046688291802338520903907)
          ·
            refine ⟨13570032437703507781355861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9046688291802338520903907 13570032437703507781355861)
            ·
              refine ⟨39755954407334495453191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13570032437703507781355861 39755954407334495453191)
              ·
                rfl

theorem cell21_1567845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 10].length) (baseStart_1567845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567845 prefixEnd_1567845 := by exact prefixLift 1567845
  have htrace : WordTrace (prefixWord ++ tailWord_1567845) baseStart_1567845 baseEnd_1567845 := by
    simpa [prefixWord, tailWord_1567845, baseEnd_1567845] using wordTrace_append hprefix tailTrace_1567845
  have hstable : (prefixWord ++ tailWord_1567845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567845).length < 2 ^ (prefixWord ++ tailWord_1567845).sum := by decide
  have hdescent : baseEnd_1567845 < baseStart_1567845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567862 : List Nat := [5, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1567862 : Nat := 118140960795 + 1567862 * 2 ^ 59
def prefixEnd_1567862 : Nat := 4983230072969 + 3 ^ 40 * 1567862 * 2
def baseEnd_1567862 : Nat := 119269156432540735765117

theorem tailTrace_1567862 : CollatzResearch.WordTrace tailWord_1567862 prefixEnd_1567862 119269156432540735765117 := by
  unfold tailWord_1567862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574039065369451147280615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38123083363940812237659893 3574039065369451147280615)
  ·
    refine ⟨5361058598054176720920923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3574039065369451147280615 5361058598054176720920923)
    ·
      refine ⟨8041587897081265081381385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5361058598054176720920923 8041587897081265081381385)
      ·
        refine ⟨6031190922810948811036039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8041587897081265081381385 6031190922810948811036039)
        ·
          refine ⟨9046786384216423216554059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031190922810948811036039 9046786384216423216554059)
          ·
            refine ⟨13570179576324634824831089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9046786384216423216554059 13570179576324634824831089)
            ·
              refine ⟨10177634682243476118623317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13570179576324634824831089 10177634682243476118623317)
              ·
                refine ⟨119269156432540735765117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10177634682243476118623317 119269156432540735765117)
                ·
                  rfl

theorem cell21_1567862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1567862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567862 prefixEnd_1567862 := by exact prefixLift 1567862
  have htrace : WordTrace (prefixWord ++ tailWord_1567862) baseStart_1567862 baseEnd_1567862 := by
    simpa [prefixWord, tailWord_1567862, baseEnd_1567862] using wordTrace_append hprefix tailTrace_1567862
  have hstable : (prefixWord ++ tailWord_1567862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567862).length < 2 ^ (prefixWord ++ tailWord_1567862).sum := by decide
  have hdescent : baseEnd_1567862 < baseStart_1567862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567865 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 4]
def baseStart_1567865 : Nat := 118140960795 + 1567865 * 2 ^ 59
def prefixEnd_1567865 : Nat := 4983230072969 + 3 ^ 40 * 1567865 * 2
def baseEnd_1567865 : Nat := 357808153938494868745345

theorem tailTrace_1567865 : CollatzResearch.WordTrace tailWord_1567865 prefixEnd_1567865 357808153938494868745345 := by
  unfold tailWord_1567865
  simp only [CollatzResearch.WordTrace]
  refine ⟨57184734464900349868849049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38123156309933566579232699 57184734464900349868849049)
  ·
    refine ⟨42888550848675262401636787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57184734464900349868849049 42888550848675262401636787)
    ·
      refine ⟨64332826273012893602455181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42888550848675262401636787 64332826273012893602455181)
      ·
        refine ⟨24124809852379835100920693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64332826273012893602455181 24124809852379835100920693)
        ·
          refine ⟨2261700923660609540711315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24124809852379835100920693 2261700923660609540711315)
          ·
            refine ⟨3392551385490914311066973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261700923660609540711315 3392551385490914311066973)
            ·
              refine ⟨1272206769559092866650115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3392551385490914311066973 1272206769559092866650115)
              ·
                refine ⟨1908310154338639299975173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272206769559092866650115 1908310154338639299975173)
                ·
                  refine ⟨357808153938494868745345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908310154338639299975173 357808153938494868745345)
                  ·
                    rfl

theorem cell21_1567865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_1567865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567865 prefixEnd_1567865 := by exact prefixLift 1567865
  have htrace : WordTrace (prefixWord ++ tailWord_1567865) baseStart_1567865 baseEnd_1567865 := by
    simpa [prefixWord, tailWord_1567865, baseEnd_1567865] using wordTrace_append hprefix tailTrace_1567865
  have hstable : (prefixWord ++ tailWord_1567865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567865).length < 2 ^ (prefixWord ++ tailWord_1567865).sum := by decide
  have hdescent : baseEnd_1567865 < baseStart_1567865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567893 : List Nat := [1, 3, 2, 1, 1, 1, 2, 7, 3]
def baseStart_1567893 : Nat := 118140960795 + 1567893 * 2 ^ 59
def prefixEnd_1567893 : Nat := 4983230072969 + 3 ^ 40 * 1567893 * 2
def baseEnd_1567893 : Nat := 357814543919973042278621

theorem tailTrace_1567893 : CollatzResearch.WordTrace tailWord_1567893 prefixEnd_1567893 357814543919973042278621 := by
  unfold tailWord_1567893
  simp only [CollatzResearch.WordTrace]
  refine ⟨57185755708798910650868333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38123837139199273767245555 57185755708798910650868333)
  ·
    refine ⟨21444658390799591494075625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57185755708798910650868333 21444658390799591494075625)
    ·
      refine ⟨16083493793099693620556719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21444658390799591494075625 16083493793099693620556719)
      ·
        refine ⟨24125240689649540430835079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16083493793099693620556719 24125240689649540430835079)
        ·
          refine ⟨36187861034474310646252619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24125240689649540430835079 36187861034474310646252619)
          ·
            refine ⟨54281791551711465969378929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36187861034474310646252619 54281791551711465969378929)
            ·
              refine ⟨40711343663783599477034197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54281791551711465969378929 40711343663783599477034197)
              ·
                refine ⟨954172117119928112742989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40711343663783599477034197 954172117119928112742989)
                ·
                  refine ⟨357814543919973042278621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954172117119928112742989 357814543919973042278621)
                  ·
                    rfl

theorem cell21_1567893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_1567893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567893 prefixEnd_1567893 := by exact prefixLift 1567893
  have htrace : WordTrace (prefixWord ++ tailWord_1567893) baseStart_1567893 baseEnd_1567893 := by
    simpa [prefixWord, tailWord_1567893, baseEnd_1567893] using wordTrace_append hprefix tailTrace_1567893
  have hstable : (prefixWord ++ tailWord_1567893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567893).length < 2 ^ (prefixWord ++ tailWord_1567893).sum := by decide
  have hdescent : baseEnd_1567893 < baseStart_1567893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1567958 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1567958 : Nat := 118140960795 + 1567958 * 2 ^ 59
def prefixEnd_1567958 : Nat := 4983230072969 + 3 ^ 40 * 1567958 * 2
def baseEnd_1567958 : Nat := 357829377805547373695155

theorem tailTrace_1567958 : CollatzResearch.WordTrace tailWord_1567958 prefixEnd_1567958 357829377805547373695155 := by
  unfold tailWord_1567958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574257903347714171999033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38125417635708951167989685 3574257903347714171999033)
  ·
    refine ⟨2680693427510785628999275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3574257903347714171999033 2680693427510785628999275)
    ·
      refine ⟨4021040141266178443498913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2680693427510785628999275 4021040141266178443498913)
      ·
        refine ⟨3015780105949633832624185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4021040141266178443498913 3015780105949633832624185)
        ·
          refine ⟨2261835079462225374468139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3015780105949633832624185 2261835079462225374468139)
          ·
            refine ⟨3392752619193338061702209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261835079462225374468139 3392752619193338061702209)
            ·
              refine ⟨2544564464395003546276657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3392752619193338061702209 2544564464395003546276657)
              ·
                refine ⟨1908423348296252659707493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2544564464395003546276657 1908423348296252659707493)
                ·
                  refine ⟨357829377805547373695155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908423348296252659707493 357829377805547373695155)
                  ·
                    rfl

theorem cell21_1567958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1567958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1567958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1567958 prefixEnd_1567958 := by exact prefixLift 1567958
  have htrace : WordTrace (prefixWord ++ tailWord_1567958) baseStart_1567958 baseEnd_1567958 := by
    simpa [prefixWord, tailWord_1567958, baseEnd_1567958] using wordTrace_append hprefix tailTrace_1567958
  have hstable : (prefixWord ++ tailWord_1567958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1567958).length < 2 ^ (prefixWord ++ tailWord_1567958).sum := by decide
  have hdescent : baseEnd_1567958 < baseStart_1567958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1567958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568028 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_1568028 : Nat := 118140960795 + 1568028 * 2 ^ 59
def prefixEnd_1568028 : Nat := 4983230072969 + 3 ^ 40 * 1568028 * 2
def baseEnd_1568028 : Nat := 357845352759242807528345

theorem tailTrace_1568028 : CollatzResearch.WordTrace tailWord_1568028 prefixEnd_1568028 357845352759242807528345 := by
  unfold tailWord_1568028
  simp only [CollatzResearch.WordTrace]
  refine ⟨28595339781654914353516369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38127119708873219138021825 28595339781654914353516369)
  ·
    refine ⟨21446504836241185765137277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28595339781654914353516369 21446504836241185765137277)
    ·
      refine ⟨8042439313590444661926479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21446504836241185765137277 8042439313590444661926479)
      ·
        refine ⟨12063658970385666992889719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8042439313590444661926479 12063658970385666992889719)
        ·
          refine ⟨18095488455578500489334579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12063658970385666992889719 18095488455578500489334579)
          ·
            refine ⟨27143232683367750734001869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18095488455578500489334579 27143232683367750734001869)
            ·
              refine ⟨10178712256262906525250701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27143232683367750734001869 10178712256262906525250701)
              ·
                refine ⟨3817017096098589946969013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10178712256262906525250701 3817017096098589946969013)
                ·
                  refine ⟨357845352759242807528345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3817017096098589946969013 357845352759242807528345)
                  ·
                    rfl

theorem cell21_1568028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_1568028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568028 prefixEnd_1568028 := by exact prefixLift 1568028
  have htrace : WordTrace (prefixWord ++ tailWord_1568028) baseStart_1568028 baseEnd_1568028 := by
    simpa [prefixWord, tailWord_1568028, baseEnd_1568028] using wordTrace_append hprefix tailTrace_1568028
  have hstable : (prefixWord ++ tailWord_1568028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568028).length < 2 ^ (prefixWord ++ tailWord_1568028).sum := by decide
  have hdescent : baseEnd_1568028 < baseStart_1568028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568135 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 4]
def baseStart_1568135 : Nat := 118140960795 + 1568135 * 2 ^ 59
def prefixEnd_1568135 : Nat := 4983230072969 + 3 ^ 40 * 1568135 * 2
def baseEnd_1568135 : Nat := 357869771617034399244793

theorem tailTrace_1568135 : CollatzResearch.WordTrace tailWord_1568135 prefixEnd_1568135 357869771617034399244793 := by
  unfold tailWord_1568135
  simp only [CollatzResearch.WordTrace]
  refine ⟨57194582173922185981177859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38129721449281457320785239 57194582173922185981177859)
  ·
    refine ⟨85791873260883278971766789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57194582173922185981177859 85791873260883278971766789)
    ·
      refine ⟨16085976236415614807206273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85791873260883278971766789 16085976236415614807206273)
      ·
        refine ⟨12064482177311711105404705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16085976236415614807206273 12064482177311711105404705)
        ·
          refine ⟨9048361632983783329053529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12064482177311711105404705 9048361632983783329053529)
          ·
            refine ⟨6786271224737837496790147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9048361632983783329053529 6786271224737837496790147)
            ·
              refine ⟨10179406837106756245185221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786271224737837496790147 10179406837106756245185221)
              ·
                refine ⟨1908638781957516795972229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10179406837106756245185221 1908638781957516795972229)
                ·
                  refine ⟨357869771617034399244793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1908638781957516795972229 357869771617034399244793)
                  ·
                    rfl

theorem cell21_1568135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 4].length) (baseStart_1568135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568135 prefixEnd_1568135 := by exact prefixLift 1568135
  have htrace : WordTrace (prefixWord ++ tailWord_1568135) baseStart_1568135 baseEnd_1568135 := by
    simpa [prefixWord, tailWord_1568135, baseEnd_1568135] using wordTrace_append hprefix tailTrace_1568135
  have hstable : (prefixWord ++ tailWord_1568135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568135).length < 2 ^ (prefixWord ++ tailWord_1568135).sum := by decide
  have hdescent : baseEnd_1568135 < baseStart_1568135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568149 : List Nat := [1, 3, 2, 1, 1, 2, 5, 6]
def baseStart_1568149 : Nat := 118140960795 + 1568149 * 2 ^ 59
def prefixEnd_1568149 : Nat := 4983230072969 + 3 ^ 40 * 1568149 * 2
def baseEnd_1568149 : Nat := 119290988869257828670477

theorem tailTrace_1568149 : CollatzResearch.WordTrace tailWord_1568149 prefixEnd_1568149 119290988869257828670477 := by
  unfold tailWord_1568149
  simp only [CollatzResearch.WordTrace]
  refine ⟨57195092795871466372187501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38130061863914310914791667 57195092795871466372187501)
  ·
    refine ⟨21448159798451799889570313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57195092795871466372187501 21448159798451799889570313)
    ·
      refine ⟨16086119848838849917177735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21448159798451799889570313 16086119848838849917177735)
      ·
        refine ⟨24129179773258274875766603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16086119848838849917177735 24129179773258274875766603)
        ·
          refine ⟨36193769659887412313649905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24129179773258274875766603 36193769659887412313649905)
          ·
            refine ⟨27145327244915559235237429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36193769659887412313649905 27145327244915559235237429)
            ·
              refine ⟨2544874429210833678303509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27145327244915559235237429 2544874429210833678303509)
              ·
                refine ⟨119290988869257828670477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2544874429210833678303509 119290988869257828670477)
                ·
                  rfl

theorem cell21_1568149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 6].length) (baseStart_1568149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568149 prefixEnd_1568149 := by exact prefixLift 1568149
  have htrace : WordTrace (prefixWord ++ tailWord_1568149) baseStart_1568149 baseEnd_1568149 := by
    simpa [prefixWord, tailWord_1568149, baseEnd_1568149] using wordTrace_append hprefix tailTrace_1568149
  have hstable : (prefixWord ++ tailWord_1568149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568149).length < 2 ^ (prefixWord ++ tailWord_1568149).sum := by decide
  have hdescent : baseEnd_1568149 < baseStart_1568149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568225 : List Nat := [1, 2, 3, 1, 2, 4, 1, 7]
def baseStart_1568225 : Nat := 118140960795 + 1568225 * 2 ^ 59
def prefixEnd_1568225 : Nat := 4983230072969 + 3 ^ 40 * 1568225 * 2
def baseEnd_1568225 : Nat := 119296770281071414248203

theorem tailTrace_1568225 : CollatzResearch.WordTrace tailWord_1568225 prefixEnd_1568225 119296770281071414248203 := by
  unfold tailWord_1568225
  simp only [CollatzResearch.WordTrace]
  refine ⟨57197864743596131351954129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38131909829064087567969419 57197864743596131351954129)
  ·
    refine ⟨42898398557697098513965597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57197864743596131351954129 42898398557697098513965597)
    ·
      refine ⟨16086899459136411942737099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42898398557697098513965597 16086899459136411942737099)
      ·
        refine ⟨24130349188704617914105649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16086899459136411942737099 24130349188704617914105649)
        ·
          refine ⟨18097761891528463435579237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24130349188704617914105649 18097761891528463435579237)
          ·
            refine ⟨3393330354661586894171107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18097761891528463435579237 3393330354661586894171107)
            ·
              refine ⟨5089995531992380341256661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393330354661586894171107 5089995531992380341256661)
              ·
                refine ⟨119296770281071414248203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5089995531992380341256661 119296770281071414248203)
                ·
                  rfl

theorem cell21_1568225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 7].length) (baseStart_1568225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568225 prefixEnd_1568225 := by exact prefixLift 1568225
  have htrace : WordTrace (prefixWord ++ tailWord_1568225) baseStart_1568225 baseEnd_1568225 := by
    simpa [prefixWord, tailWord_1568225, baseEnd_1568225] using wordTrace_append hprefix tailTrace_1568225
  have hstable : (prefixWord ++ tailWord_1568225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568225).length < 2 ^ (prefixWord ++ tailWord_1568225).sum := by decide
  have hdescent : baseEnd_1568225 < baseStart_1568225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568239 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 7]
def baseStart_1568239 : Nat := 118140960795 + 1568239 * 2 ^ 59
def prefixEnd_1568239 : Nat := 4983230072969 + 3 ^ 40 * 1568239 * 2
def baseEnd_1568239 : Nat := 357893505833953329511247

theorem tailTrace_1568239 : CollatzResearch.WordTrace tailWord_1568239 prefixEnd_1568239 357893505833953329511247 := by
  unfold tailWord_1568239
  simp only [CollatzResearch.WordTrace]
  refine ⟨57198375365545411742963771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38132250243696941161975847 57198375365545411742963771)
  ·
    refine ⟨85797563048318117614445657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57198375365545411742963771 85797563048318117614445657)
    ·
      refine ⟨64348172286238588210834243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85797563048318117614445657 64348172286238588210834243)
      ·
        refine ⟨96522258429357882316251365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64348172286238588210834243 96522258429357882316251365)
        ·
          refine ⟨18097923455504602934297131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96522258429357882316251365 18097923455504602934297131)
          ·
            refine ⟨27146885183256904401445697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18097923455504602934297131 27146885183256904401445697)
            ·
              refine ⟨20360163887442678301084273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27146885183256904401445697 20360163887442678301084273)
              ·
                refine ⟨15270122915582008725813205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20360163887442678301084273 15270122915582008725813205)
                ·
                  refine ⟨357893505833953329511247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15270122915582008725813205 357893505833953329511247)
                  ·
                    rfl

theorem cell21_1568239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_1568239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568239 prefixEnd_1568239 := by exact prefixLift 1568239
  have htrace : WordTrace (prefixWord ++ tailWord_1568239) baseStart_1568239 baseEnd_1568239 := by
    simpa [prefixWord, tailWord_1568239, baseEnd_1568239] using wordTrace_append hprefix tailTrace_1568239
  have hstable : (prefixWord ++ tailWord_1568239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568239).length < 2 ^ (prefixWord ++ tailWord_1568239).sum := by decide
  have hdescent : baseEnd_1568239 < baseStart_1568239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568242 : List Nat := [3, 2, 1, 4, 1, 3, 7]
def baseStart_1568242 : Nat := 118140960795 + 1568242 * 2 ^ 59
def prefixEnd_1568242 : Nat := 4983230072969 + 3 ^ 40 * 1568242 * 2
def baseEnd_1568242 : Nat := 39766021163869554551249

theorem tailTrace_1568242 : CollatzResearch.WordTrace tailWord_1568242 prefixEnd_1568242 39766021163869554551249 := by
  unfold tailWord_1568242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299621196133635813830745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38132323189689695503548653 14299621196133635813830745)
  ·
    refine ⟨10724715897100226860373059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14299621196133635813830745 10724715897100226860373059)
    ·
      refine ⟨16087073845650340290559589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10724715897100226860373059 16087073845650340290559589)
      ·
        refine ⟨3016326346059438804479923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16087073845650340290559589 3016326346059438804479923)
        ·
          refine ⟨4524489519089158206719885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3016326346059438804479923 4524489519089158206719885)
          ·
            refine ⟨1696683569658434327519957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4524489519089158206719885 1696683569658434327519957)
            ·
              refine ⟨39766021163869554551249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1696683569658434327519957 39766021163869554551249)
              ·
                rfl

theorem cell21_1568242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 7].length) (baseStart_1568242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568242 prefixEnd_1568242 := by exact prefixLift 1568242
  have htrace : WordTrace (prefixWord ++ tailWord_1568242) baseStart_1568242 baseEnd_1568242 := by
    simpa [prefixWord, tailWord_1568242, baseEnd_1568242] using wordTrace_append hprefix tailTrace_1568242
  have hstable : (prefixWord ++ tailWord_1568242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568242).length < 2 ^ (prefixWord ++ tailWord_1568242).sum := by decide
  have hdescent : baseEnd_1568242 < baseStart_1568242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568332 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_1568332 : Nat := 118140960795 + 1568332 * 2 ^ 59
def prefixEnd_1568332 : Nat := 4983230072969 + 3 ^ 40 * 1568332 * 2
def baseEnd_1568332 : Nat := 357914729701005834461057

theorem tailTrace_1568332 : CollatzResearch.WordTrace tailWord_1568332 prefixEnd_1568332 357914729701005834461057 := by
  unfold tailWord_1568332
  simp only [CollatzResearch.WordTrace]
  refine ⟨28600883677104244313049625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38134511569472325750732833 28600883677104244313049625)
  ·
    refine ⟨21450662757828183234787219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28600883677104244313049625 21450662757828183234787219)
    ·
      refine ⟨32175994136742274852180829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21450662757828183234787219 32175994136742274852180829)
      ·
        refine ⟨12065997801278353069567811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32175994136742274852180829 12065997801278353069567811)
        ·
          refine ⟨18098996701917529604351717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12065997801278353069567811 18098996701917529604351717)
          ·
            refine ⟨3393561881609536800815947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18098996701917529604351717 3393561881609536800815947)
            ·
              refine ⟨5090342822414305201223921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393561881609536800815947 5090342822414305201223921)
              ·
                refine ⟨3817757116810728900917941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5090342822414305201223921 3817757116810728900917941)
                ·
                  refine ⟨357914729701005834461057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3817757116810728900917941 357914729701005834461057)
                  ·
                    rfl

theorem cell21_1568332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_1568332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568332 prefixEnd_1568332 := by exact prefixLift 1568332
  have htrace : WordTrace (prefixWord ++ tailWord_1568332) baseStart_1568332 baseEnd_1568332 := by
    simpa [prefixWord, tailWord_1568332, baseEnd_1568332] using wordTrace_append hprefix tailTrace_1568332
  have hstable : (prefixWord ++ tailWord_1568332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568332).length < 2 ^ (prefixWord ++ tailWord_1568332).sum := by decide
  have hdescent : baseEnd_1568332 < baseStart_1568332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568394 : List Nat := [3, 1, 2, 3, 2, 1, 4, 5]
def baseStart_1568394 : Nat := 118140960795 + 1568394 * 2 ^ 59
def prefixEnd_1568394 : Nat := 4983230072969 + 3 ^ 40 * 1568394 * 2
def baseEnd_1568394 : Nat := 119309626315235834809199

theorem tailTrace_1568394 : CollatzResearch.WordTrace tailWord_1568394 prefixEnd_1568394 119309626315235834809199 := by
  unfold tailWord_1568394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14301007169995968303714059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38136019119989248809904157 14301007169995968303714059)
  ·
    refine ⟨21451510754993952455571089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14301007169995968303714059 21451510754993952455571089)
    ·
      refine ⟨16088633066245464341678317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21451510754993952455571089 16088633066245464341678317)
      ·
        refine ⟨6033237399842049128129369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16088633066245464341678317 6033237399842049128129369)
        ·
          refine ⟨4524928049881536846097027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6033237399842049128129369 4524928049881536846097027)
          ·
            refine ⟨6787392074822305269145541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524928049881536846097027 6787392074822305269145541)
            ·
              refine ⟨1272636014029182237964789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6787392074822305269145541 1272636014029182237964789)
              ·
                refine ⟨119309626315235834809199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1272636014029182237964789 119309626315235834809199)
                ·
                  rfl

theorem cell21_1568394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_1568394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568394 prefixEnd_1568394 := by exact prefixLift 1568394
  have htrace : WordTrace (prefixWord ++ tailWord_1568394) baseStart_1568394 baseEnd_1568394 := by
    simpa [prefixWord, tailWord_1568394, baseEnd_1568394] using wordTrace_append hprefix tailTrace_1568394
  have hstable : (prefixWord ++ tailWord_1568394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568394).length < 2 ^ (prefixWord ++ tailWord_1568394).sum := by decide
  have hdescent : baseEnd_1568394 < baseStart_1568394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568439 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 4]
def baseStart_1568439 : Nat := 118140960795 + 1568439 * 2 ^ 59
def prefixEnd_1568439 : Nat := 4983230072969 + 3 ^ 40 * 1568439 * 2
def baseEnd_1568439 : Nat := 357939148558797426177505

theorem tailTrace_1568439 : CollatzResearch.WordTrace tailWord_1568439 prefixEnd_1568439 357939148558797426177505 := by
  unfold tailWord_1568439
  simp only [CollatzResearch.WordTrace]
  refine ⟨57205669964820845900244371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38137113309880563933496247 57205669964820845900244371)
  ·
    refine ⟨85808504947231268850366557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57205669964820845900244371 85808504947231268850366557)
    ·
      refine ⟨32178189355211725818887459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85808504947231268850366557 32178189355211725818887459)
      ·
        refine ⟨48267284032817588728331189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32178189355211725818887459 48267284032817588728331189)
        ·
          refine ⟨4525057878076648943281049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48267284032817588728331189 4525057878076648943281049)
          ·
            refine ⟨3393793408557486707460787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4525057878076648943281049 3393793408557486707460787)
            ·
              refine ⟨5090690112836230061191181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393793408557486707460787 5090690112836230061191181)
              ·
                refine ⟨1909008792313586272946693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5090690112836230061191181 1909008792313586272946693)
                ·
                  refine ⟨357939148558797426177505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1909008792313586272946693 357939148558797426177505)
                  ·
                    rfl

theorem cell21_1568439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 4].length) (baseStart_1568439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568439 prefixEnd_1568439 := by exact prefixLift 1568439
  have htrace : WordTrace (prefixWord ++ tailWord_1568439) baseStart_1568439 baseEnd_1568439 := by
    simpa [prefixWord, tailWord_1568439, baseEnd_1568439] using wordTrace_append hprefix tailTrace_1568439
  have hstable : (prefixWord ++ tailWord_1568439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568439).length < 2 ^ (prefixWord ++ tailWord_1568439).sum := by decide
  have hdescent : baseEnd_1568439 < baseStart_1568439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568470 : List Nat := [5, 2, 1, 3, 10]
def baseStart_1568470 : Nat := 118140960795 + 1568470 * 2 ^ 59
def prefixEnd_1568470 : Nat := 4983230072969 + 3 ^ 40 * 1568470 * 2
def baseEnd_1568470 : Nat := 4419089175075904458775

theorem tailTrace_1568470 : CollatzResearch.WordTrace tailWord_1568470 prefixEnd_1568470 4419089175075904458775 := by
  unfold tailWord_1568470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575425039231783637163929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38137867085139025463081909 3575425039231783637163929)
  ·
    refine ⟨2681568779423837727872947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3575425039231783637163929 2681568779423837727872947)
    ·
      refine ⟨4022353169135756591809421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2681568779423837727872947 4022353169135756591809421)
      ·
        refine ⟨1508382438425908721928533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4022353169135756591809421 1508382438425908721928533)
        ·
          refine ⟨4419089175075904458775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1508382438425908721928533 4419089175075904458775)
          ·
            rfl

theorem cell21_1568470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 10].length) (baseStart_1568470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568470 prefixEnd_1568470 := by exact prefixLift 1568470
  have htrace : WordTrace (prefixWord ++ tailWord_1568470) baseStart_1568470 baseEnd_1568470 := by
    simpa [prefixWord, tailWord_1568470, baseEnd_1568470] using wordTrace_append hprefix tailTrace_1568470
  have hstable : (prefixWord ++ tailWord_1568470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568470).length < 2 ^ (prefixWord ++ tailWord_1568470).sum := by decide
  have hdescent : baseEnd_1568470 < baseStart_1568470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568476 : List Nat := [2, 2, 5, 1, 2, 2, 2, 2, 3]
def baseStart_1568476 : Nat := 118140960795 + 1568476 * 2 ^ 59
def prefixEnd_1568476 : Nat := 4983230072969 + 3 ^ 40 * 1568476 * 2
def baseEnd_1568476 : Nat := 357947592462893584060763

theorem tailTrace_1568476 : CollatzResearch.WordTrace tailWord_1568476 prefixEnd_1568476 357947592462893584060763 := by
  unfold tailWord_1568476
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603509732843400609670641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38138012977124534146227521 28603509732843400609670641)
  ·
    refine ⟨21452632299632550457252981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28603509732843400609670641 21452632299632550457252981)
    ·
      refine ⟨2011184278090551605367467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21452632299632550457252981 2011184278090551605367467)
      ·
        refine ⟨3016776417135827408051201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011184278090551605367467 3016776417135827408051201)
        ·
          refine ⟨2262582312851870556038401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016776417135827408051201 2262582312851870556038401)
          ·
            refine ⟨1696936734638902917028801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2262582312851870556038401 1696936734638902917028801)
            ·
              refine ⟨1272702550979177187771601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696936734638902917028801 1272702550979177187771601)
              ·
                refine ⟨954526913234382890828701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1272702550979177187771601 954526913234382890828701)
                ·
                  refine ⟨357947592462893584060763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954526913234382890828701 357947592462893584060763)
                  ·
                    rfl

theorem cell21_1568476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_1568476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568476 prefixEnd_1568476 := by exact prefixLift 1568476
  have htrace : WordTrace (prefixWord ++ tailWord_1568476) baseStart_1568476 baseEnd_1568476 := by
    simpa [prefixWord, tailWord_1568476, baseEnd_1568476] using wordTrace_append hprefix tailTrace_1568476
  have hstable : (prefixWord ++ tailWord_1568476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568476).length < 2 ^ (prefixWord ++ tailWord_1568476).sum := by decide
  have hdescent : baseEnd_1568476 < baseStart_1568476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568487 : List Nat := [1, 1, 5, 4, 1, 2, 1, 6]
def baseStart_1568487 : Nat := 118140960795 + 1568487 * 2 ^ 59
def prefixEnd_1568487 : Nat := 4983230072969 + 3 ^ 40 * 1568487 * 2
def baseEnd_1568487 : Nat := 119316700937586669792469

theorem tailTrace_1568487 : CollatzResearch.WordTrace tailWord_1568487 prefixEnd_1568487 119316700937586669792469 := by
  unfold tailWord_1568487
  simp only [CollatzResearch.WordTrace]
  refine ⟨57207420668646950097991715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38138280445764633398661143 57207420668646950097991715)
  ·
    refine ⟨85811131002970425146987573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57207420668646950097991715 85811131002970425146987573)
    ·
      refine ⟨8044793531528477357530085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85811131002970425146987573 8044793531528477357530085)
      ·
        refine ⟨1508398787161589504536891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8044793531528477357530085 1508398787161589504536891)
        ·
          refine ⟨2262598180742384256805337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508398787161589504536891 2262598180742384256805337)
          ·
            refine ⟨1696948635556788192604003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2262598180742384256805337 1696948635556788192604003)
            ·
              refine ⟨2545422953335182288906005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696948635556788192604003 2545422953335182288906005)
              ·
                refine ⟨119316700937586669792469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2545422953335182288906005 119316700937586669792469)
                ·
                  rfl

theorem cell21_1568487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 6].length) (baseStart_1568487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568487 prefixEnd_1568487 := by exact prefixLift 1568487
  have htrace : WordTrace (prefixWord ++ tailWord_1568487) baseStart_1568487 baseEnd_1568487 := by
    simpa [prefixWord, tailWord_1568487, baseEnd_1568487] using wordTrace_append hprefix tailTrace_1568487
  have hstable : (prefixWord ++ tailWord_1568487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568487).length < 2 ^ (prefixWord ++ tailWord_1568487).sum := by decide
  have hdescent : baseEnd_1568487 < baseStart_1568487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568563 : List Nat := [1, 1, 1, 2, 8, 1, 2, 5]
def baseStart_1568563 : Nat := 118140960795 + 1568563 * 2 ^ 59
def prefixEnd_1568563 : Nat := 4983230072969 + 3 ^ 40 * 1568563 * 2
def baseEnd_1568563 : Nat := 119322482349400255370195

theorem tailTrace_1568563 : CollatzResearch.WordTrace tailWord_1568563 prefixEnd_1568563 119322482349400255370195 := by
  unfold tailWord_1568563
  simp only [CollatzResearch.WordTrace]
  refine ⟨57210192616371615077758343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38140128410914410051838895 57210192616371615077758343)
  ·
    refine ⟨85815288924557422616637515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57210192616371615077758343 85815288924557422616637515)
    ·
      refine ⟨128722933386836133924956273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85815288924557422616637515 128722933386836133924956273)
      ·
        refine ⟨96542200040127100443717205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128722933386836133924956273 96542200040127100443717205)
        ·
          refine ⟨1131353906720239458324811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 96542200040127100443717205 1131353906720239458324811)
          ·
            refine ⟨1697030860080359187487217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131353906720239458324811 1697030860080359187487217)
            ·
              refine ⟨1272773145060269390615413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697030860080359187487217 1272773145060269390615413)
              ·
                refine ⟨119322482349400255370195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1272773145060269390615413 119322482349400255370195)
                ·
                  rfl

theorem cell21_1568563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 5].length) (baseStart_1568563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568563 prefixEnd_1568563 := by exact prefixLift 1568563
  have htrace : WordTrace (prefixWord ++ tailWord_1568563) baseStart_1568563 baseEnd_1568563 := by
    simpa [prefixWord, tailWord_1568563, baseEnd_1568563] using wordTrace_append hprefix tailTrace_1568563
  have hstable : (prefixWord ++ tailWord_1568563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568563).length < 2 ^ (prefixWord ++ tailWord_1568563).sum := by decide
  have hdescent : baseEnd_1568563 < baseStart_1568563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568594 : List Nat := [3, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_1568594 : Nat := 118140960795 + 1568594 * 2 ^ 59
def prefixEnd_1568594 : Nat := 4983230072969 + 3 ^ 40 * 1568594 * 2
def baseEnd_1568594 : Nat := 357974521670551601093855

theorem tailTrace_1568594 : CollatzResearch.WordTrace tailWord_1568594 prefixEnd_1568594 357974521670551601093855 := by
  unfold tailWord_1568594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14302830819814826843034209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38140882186172871581424557 14302830819814826843034209)
  ·
    refine ⟨10727123114861120132275657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14302830819814826843034209 10727123114861120132275657)
    ·
      refine ⟨8045342336145840099206743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10727123114861120132275657 8045342336145840099206743)
      ·
        refine ⟨12068013504218760148810115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8045342336145840099206743 12068013504218760148810115)
        ·
          refine ⟨18102020256328140223215173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12068013504218760148810115 18102020256328140223215173)
          ·
            refine ⟨3394128798061526291852845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18102020256328140223215173 3394128798061526291852845)
            ·
              refine ⟨1272798299273072359444817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3394128798061526291852845 1272798299273072359444817)
              ·
                refine ⟨954598724454804269583613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1272798299273072359444817 954598724454804269583613)
                ·
                  refine ⟨357974521670551601093855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954598724454804269583613 357974521670551601093855)
                  ·
                    rfl

theorem cell21_1568594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_1568594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568594 prefixEnd_1568594 := by exact prefixLift 1568594
  have htrace : WordTrace (prefixWord ++ tailWord_1568594) baseStart_1568594 baseEnd_1568594 := by
    simpa [prefixWord, tailWord_1568594, baseEnd_1568594] using wordTrace_append hprefix tailTrace_1568594
  have hstable : (prefixWord ++ tailWord_1568594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568594).length < 2 ^ (prefixWord ++ tailWord_1568594).sum := by decide
  have hdescent : baseEnd_1568594 < baseStart_1568594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568608 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_1568608 : Nat := 118140960795 + 1568608 * 2 ^ 59
def prefixEnd_1568608 : Nat := 4983230072969 + 3 ^ 40 * 1568608 * 2
def baseEnd_1568608 : Nat := 357977716661290687860493

theorem tailTrace_1568608 : CollatzResearch.WordTrace tailWord_1568608 prefixEnd_1568608 357977716661290687860493 := by
  unfold tailWord_1568608
  simp only [CollatzResearch.WordTrace]
  refine ⟨28605916950604293881573239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38141222600805725175430985 28605916950604293881573239)
  ·
    refine ⟨42908875425906440822359859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28605916950604293881573239 42908875425906440822359859)
    ·
      refine ⟨64363313138859661233539789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42908875425906440822359859 64363313138859661233539789)
      ·
        refine ⟨24136242427072372962577421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64363313138859661233539789 24136242427072372962577421)
        ·
          refine ⟨9051090910152139860966533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24136242427072372962577421 9051090910152139860966533)
          ·
            refine ⟨1697079545653526223931225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9051090910152139860966533 1697079545653526223931225)
            ·
              refine ⟨1272809659240144667948419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697079545653526223931225 1272809659240144667948419)
              ·
                refine ⟨1909214488860217001922629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272809659240144667948419 1909214488860217001922629)
                ·
                  refine ⟨357977716661290687860493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1909214488860217001922629 357977716661290687860493)
                  ·
                    rfl

theorem cell21_1568608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_1568608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568608 prefixEnd_1568608 := by exact prefixLift 1568608
  have htrace : WordTrace (prefixWord ++ tailWord_1568608) baseStart_1568608 baseEnd_1568608 := by
    simpa [prefixWord, tailWord_1568608, baseEnd_1568608] using wordTrace_append hprefix tailTrace_1568608
  have hstable : (prefixWord ++ tailWord_1568608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568608).length < 2 ^ (prefixWord ++ tailWord_1568608).sum := by decide
  have hdescent : baseEnd_1568608 < baseStart_1568608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568670 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1568670 : Nat := 118140960795 + 1568670 * 2 ^ 59
def prefixEnd_1568670 : Nat := 4983230072969 + 3 ^ 40 * 1568670 * 2
def baseEnd_1568670 : Nat := 357991865905992357827033

theorem tailTrace_1568670 : CollatzResearch.WordTrace tailWord_1568670 prefixEnd_1568670 357991865905992357827033 := by
  unfold tailWord_1568670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7151761903372996543987933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38142730151322648234602309 7151761903372996543987933)
  ·
    refine ⟨2681910713764873703995475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7151761903372996543987933 2681910713764873703995475)
    ·
      refine ⟨4022866070647310555993213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2681910713764873703995475 4022866070647310555993213)
      ·
        refine ⟨1508574776492741458497455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4022866070647310555993213 1508574776492741458497455)
        ·
          refine ⟨2262862164739112187746183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508574776492741458497455 2262862164739112187746183)
          ·
            refine ⟨3394293247108668281619275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262862164739112187746183 3394293247108668281619275)
            ·
              refine ⟨5091439870663002422428913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394293247108668281619275 5091439870663002422428913)
              ·
                refine ⟨3818579902997251816821685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5091439870663002422428913 3818579902997251816821685)
                ·
                  refine ⟨357991865905992357827033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3818579902997251816821685 357991865905992357827033)
                  ·
                    rfl

theorem cell21_1568670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1568670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568670 prefixEnd_1568670 := by exact prefixLift 1568670
  have htrace : WordTrace (prefixWord ++ tailWord_1568670) baseStart_1568670 baseEnd_1568670 := by
    simpa [prefixWord, tailWord_1568670, baseEnd_1568670] using wordTrace_append hprefix tailTrace_1568670
  have hstable : (prefixWord ++ tailWord_1568670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568670).length < 2 ^ (prefixWord ++ tailWord_1568670).sum := by decide
  have hdescent : baseEnd_1568670 < baseStart_1568670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568712 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_1568712 : Nat := 118140960795 + 1568712 * 2 ^ 59
def prefixEnd_1568712 : Nat := 4983230072969 + 3 ^ 40 * 1568712 * 2
def baseEnd_1568712 : Nat := 358001450878209618126947

theorem tailTrace_1568712 : CollatzResearch.WordTrace tailWord_1568712 prefixEnd_1568712 358001450878209618126947 := by
  unfold tailWord_1568712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28607813546415906762466195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38143751395221209016621593 28607813546415906762466195)
  ·
    refine ⟨42911720319623860143699293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28607813546415906762466195 42911720319623860143699293)
    ·
      refine ⟨16091895119858947553887235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42911720319623860143699293 16091895119858947553887235)
      ·
        refine ⟨24137842679788421330830853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16091895119858947553887235 24137842679788421330830853)
        ·
          refine ⟨4525845502460328999530785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24137842679788421330830853 4525845502460328999530785)
          ·
            refine ⟨3394384126845246749648089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4525845502460328999530785 3394384126845246749648089)
            ·
              refine ⟨2545788095133935062236067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3394384126845246749648089 2545788095133935062236067)
              ·
                refine ⟨3818682142700902593354101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545788095133935062236067 3818682142700902593354101)
                ·
                  refine ⟨358001450878209618126947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3818682142700902593354101 358001450878209618126947)
                  ·
                    rfl

theorem cell21_1568712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_1568712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568712 prefixEnd_1568712 := by exact prefixLift 1568712
  have htrace : WordTrace (prefixWord ++ tailWord_1568712) baseStart_1568712 baseEnd_1568712 := by
    simpa [prefixWord, tailWord_1568712, baseEnd_1568712] using wordTrace_append hprefix tailTrace_1568712
  have hstable : (prefixWord ++ tailWord_1568712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568712).length < 2 ^ (prefixWord ++ tailWord_1568712).sum := by decide
  have hdescent : baseEnd_1568712 < baseStart_1568712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568740 : List Nat := [2, 3, 1, 1, 1, 1, 5, 7]
def baseStart_1568740 : Nat := 118140960795 + 1568740 * 2 ^ 59
def prefixEnd_1568740 : Nat := 4983230072969 + 3 ^ 40 * 1568740 * 2
def baseEnd_1568740 : Nat := 119335946953229263886741

theorem tailTrace_1568740 : CollatzResearch.WordTrace tailWord_1568740 prefixEnd_1568740 119335946953229263886741 := by
  unfold tailWord_1568740
  simp only [CollatzResearch.WordTrace]
  refine ⟨28608324168365187153475837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38144432224486916204634449 28608324168365187153475837)
  ·
    refine ⟨10728121563136945182553439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28608324168365187153475837 10728121563136945182553439)
    ·
      refine ⟨16092182344705417773830159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10728121563136945182553439 16092182344705417773830159)
      ·
        refine ⟨24138273517058126660745239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16092182344705417773830159 24138273517058126660745239)
        ·
          refine ⟨36207410275587189991117859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24138273517058126660745239 36207410275587189991117859)
          ·
            refine ⟨54311115413380784986676789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36207410275587189991117859 54311115413380784986676789)
            ·
              refine ⟨5091667070004448592500949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54311115413380784986676789 5091667070004448592500949)
              ·
                refine ⟨119335946953229263886741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5091667070004448592500949 119335946953229263886741)
                ·
                  rfl

theorem cell21_1568740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_1568740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568740 prefixEnd_1568740 := by exact prefixLift 1568740
  have htrace : WordTrace (prefixWord ++ tailWord_1568740) baseStart_1568740 baseEnd_1568740 := by
    simpa [prefixWord, tailWord_1568740, baseEnd_1568740] using wordTrace_append hprefix tailTrace_1568740
  have hstable : (prefixWord ++ tailWord_1568740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568740).length < 2 ^ (prefixWord ++ tailWord_1568740).sum := by decide
  have hdescent : baseEnd_1568740 < baseStart_1568740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568833 : List Nat := [1, 2, 5, 1, 2, 1, 3, 6]
def baseStart_1568833 : Nat := 118140960795 + 1568833 * 2 ^ 59
def prefixEnd_1568833 : Nat := 4983230072969 + 3 ^ 40 * 1568833 * 2
def baseEnd_1568833 : Nat := 119343021575580098870011

theorem tailTrace_1568833 : CollatzResearch.WordTrace tailWord_1568833 prefixEnd_1568833 119343021575580098870011 := by
  unfold tailWord_1568833
  simp only [CollatzResearch.WordTrace]
  refine ⟨57220040325393451190087153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38146693550262300793391435 57220040325393451190087153)
  ·
    refine ⟨42915030244045088392565365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57220040325393451190087153 42915030244045088392565365)
    ·
      refine ⟨4023284085379227036803003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42915030244045088392565365 4023284085379227036803003)
      ·
        refine ⟨6034926128068840555204505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4023284085379227036803003 6034926128068840555204505)
        ·
          refine ⟨4526194596051630416403379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6034926128068840555204505 4526194596051630416403379)
          ·
            refine ⟨6789291894077445624605069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526194596051630416403379 6789291894077445624605069)
            ·
              refine ⟨2545984460279042109226901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6789291894077445624605069 2545984460279042109226901)
              ·
                refine ⟨119343021575580098870011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2545984460279042109226901 119343021575580098870011)
                ·
                  rfl

theorem cell21_1568833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 6].length) (baseStart_1568833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568833 prefixEnd_1568833 := by exact prefixLift 1568833
  have htrace : WordTrace (prefixWord ++ tailWord_1568833) baseStart_1568833 baseEnd_1568833 := by
    simpa [prefixWord, tailWord_1568833, baseEnd_1568833] using wordTrace_append hprefix tailTrace_1568833
  have hstable : (prefixWord ++ tailWord_1568833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568833).length < 2 ^ (prefixWord ++ tailWord_1568833).sum := by decide
  have hdescent : baseEnd_1568833 < baseStart_1568833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568850 : List Nat := [3, 2, 2, 1, 4, 1, 3, 5]
def baseStart_1568850 : Nat := 118140960795 + 1568850 * 2 ^ 59
def prefixEnd_1568850 : Nat := 4983230072969 + 3 ^ 40 * 1568850 * 2
def baseEnd_1568850 : Nat := 119344314786117348275555

theorem tailTrace_1568850 : CollatzResearch.WordTrace tailWord_1568850 prefixEnd_1568850 119344314786117348275555 := by
  unfold tailWord_1568850
  simp only [CollatzResearch.WordTrace]
  refine ⟨14305165091582965773364001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38147106910887908728970669 14305165091582965773364001)
  ·
    refine ⟨10728873818687224330023001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14305165091582965773364001 10728873818687224330023001)
    ·
      refine ⟨8046655364015418247517251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10728873818687224330023001 8046655364015418247517251)
      ·
        refine ⟨12069983046023127371275877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8046655364015418247517251 12069983046023127371275877)
        ·
          refine ⟨2263121821129336382114227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12069983046023127371275877 2263121821129336382114227)
          ·
            refine ⟨3394682731694004573171341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263121821129336382114227 3394682731694004573171341)
            ·
              refine ⟨1273006024385251714939253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3394682731694004573171341 1273006024385251714939253)
              ·
                refine ⟨119344314786117348275555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1273006024385251714939253 119344314786117348275555)
                ·
                  rfl

theorem cell21_1568850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_1568850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568850 prefixEnd_1568850 := by exact prefixLift 1568850
  have htrace : WordTrace (prefixWord ++ tailWord_1568850) baseStart_1568850 baseEnd_1568850 := by
    simpa [prefixWord, tailWord_1568850, baseEnd_1568850] using wordTrace_append hprefix tailTrace_1568850
  have hstable : (prefixWord ++ tailWord_1568850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568850).length < 2 ^ (prefixWord ++ tailWord_1568850).sum := by decide
  have hdescent : baseEnd_1568850 < baseStart_1568850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568864 : List Nat := [2, 1, 1, 3, 2, 3, 1, 5, 3]
def baseStart_1568864 : Nat := 118140960795 + 1568864 * 2 ^ 59
def prefixEnd_1568864 : Nat := 4983230072969 + 3 ^ 40 * 1568864 * 2
def baseEnd_1568864 : Nat := 358036139349091131593303

theorem tailTrace_1568864 : CollatzResearch.WordTrace tailWord_1568864 prefixEnd_1568864 358036139349091131593303 := by
  unfold tailWord_1568864
  simp only [CollatzResearch.WordTrace]
  refine ⟨28610585494140571742232823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38147447325520762322977097 28610585494140571742232823)
  ·
    refine ⟨42915878241210857613349235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28610585494140571742232823 42915878241210857613349235)
    ·
      refine ⟨64373817361816286420023853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42915878241210857613349235 64373817361816286420023853)
      ·
        refine ⟨24140181510681107407508945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64373817361816286420023853 24140181510681107407508945)
        ·
          refine ⟨18105136133010830555631709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24140181510681107407508945 18105136133010830555631709)
          ·
            refine ⟨6789426049879061458361891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18105136133010830555631709 6789426049879061458361891)
            ·
              refine ⟨10184139074818592187542837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6789426049879061458361891 10184139074818592187542837)
              ·
                refine ⟨954763038264243017582141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10184139074818592187542837 954763038264243017582141)
                ·
                  refine ⟨358036139349091131593303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 954763038264243017582141 358036139349091131593303)
                  ·
                    rfl

theorem cell21_1568864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_1568864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568864 prefixEnd_1568864 := by exact prefixLift 1568864
  have htrace : WordTrace (prefixWord ++ tailWord_1568864) baseStart_1568864 baseEnd_1568864 := by
    simpa [prefixWord, tailWord_1568864, baseEnd_1568864] using wordTrace_append hprefix tailTrace_1568864
  have hstable : (prefixWord ++ tailWord_1568864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568864).length < 2 ^ (prefixWord ++ tailWord_1568864).sum := by decide
  have hdescent : baseEnd_1568864 < baseStart_1568864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568878 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1568878 : Nat := 118140960795 + 1568878 * 2 ^ 59
def prefixEnd_1568878 : Nat := 4983230072969 + 3 ^ 40 * 1568878 * 2
def baseEnd_1568878 : Nat := 358039334339830218359941

theorem tailTrace_1568878 : CollatzResearch.WordTrace tailWord_1568878 prefixEnd_1568878 358039334339830218359941 := by
  unfold tailWord_1568878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152710201278802984434411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38147787740153615916983525 7152710201278802984434411)
  ·
    refine ⟨10729065301918204476651617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7152710201278802984434411 10729065301918204476651617)
    ·
      refine ⟨8046798976438653357488713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10729065301918204476651617 8046798976438653357488713)
      ·
        refine ⟨6035099232328990018116535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8046798976438653357488713 6035099232328990018116535)
        ·
          refine ⟨9052648848493485027174803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035099232328990018116535 9052648848493485027174803)
          ·
            refine ⟨13578973272740227540762205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052648848493485027174803 13578973272740227540762205)
            ·
              refine ⟨5092114977277585327785827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13578973272740227540762205 5092114977277585327785827)
              ·
                refine ⟨7638172465916377991678741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092114977277585327785827 7638172465916377991678741)
                ·
                  refine ⟨358039334339830218359941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7638172465916377991678741 358039334339830218359941)
                  ·
                    rfl

theorem cell21_1568878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1568878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568878 prefixEnd_1568878 := by exact prefixLift 1568878
  have htrace : WordTrace (prefixWord ++ tailWord_1568878) baseStart_1568878 baseEnd_1568878 := by
    simpa [prefixWord, tailWord_1568878, baseEnd_1568878] using wordTrace_append hprefix tailTrace_1568878
  have hstable : (prefixWord ++ tailWord_1568878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568878).length < 2 ^ (prefixWord ++ tailWord_1568878).sum := by decide
  have hdescent : baseEnd_1568878 < baseStart_1568878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568926 : List Nat := [4, 3, 1, 1, 3, 2, 7]
def baseStart_1568926 : Nat := 118140960795 + 1568926 * 2 ^ 59
def prefixEnd_1568926 : Nat := 4983230072969 + 3 ^ 40 * 1568926 * 2
def baseEnd_1568926 : Nat := 39783365399310311284427

theorem tailTrace_1568926 : CollatzResearch.WordTrace tailWord_1568926 prefixEnd_1568926 39783365399310311284427 := by
  unfold tailWord_1568926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152929039257066009152829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38148954876037685382148421 7152929039257066009152829)
  ·
    refine ⟨2682348389721399753432311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7152929039257066009152829 2682348389721399753432311)
    ·
      refine ⟨4023522584582099630148467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2682348389721399753432311 4023522584582099630148467)
      ·
        refine ⟨6035283876873149445222701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4023522584582099630148467 6035283876873149445222701)
        ·
          refine ⟨2263231453827431041958513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6035283876873149445222701 2263231453827431041958513)
          ·
            refine ⟨1697423590370573281468885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263231453827431041958513 1697423590370573281468885)
            ·
              refine ⟨39783365399310311284427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1697423590370573281468885 39783365399310311284427)
              ·
                rfl

theorem cell21_1568926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 7].length) (baseStart_1568926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1568926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1568926 prefixEnd_1568926 := by exact prefixLift 1568926
  have htrace : WordTrace (prefixWord ++ tailWord_1568926) baseStart_1568926 baseEnd_1568926 := by
    simpa [prefixWord, tailWord_1568926, baseEnd_1568926] using wordTrace_append hprefix tailTrace_1568926
  have hstable : (prefixWord ++ tailWord_1568926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568926).length < 2 ^ (prefixWord ++ tailWord_1568926).sum := by decide
  have hdescent : baseEnd_1568926 < baseStart_1568926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569047 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 4]
def baseStart_1569047 : Nat := 118140960795 + 1569047 * 2 ^ 59
def prefixEnd_1569047 : Nat := 4983230072969 + 3 ^ 40 * 1569047 * 2
def baseEnd_1569047 : Nat := 358077902442323480042929

theorem tailTrace_1569047 : CollatzResearch.WordTrace tailWord_1569047 prefixEnd_1569047 358077902442323480042929 := by
  unfold tailWord_1569047
  simp only [CollatzResearch.WordTrace]
  refine ⟨57227845546618165738377395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38151897031078777158918263 57227845546618165738377395)
  ·
    refine ⟨85841768319927248607566093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57227845546618165738377395 85841768319927248607566093)
    ·
      refine ⟨32190663119972718227837285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85841768319927248607566093 32190663119972718227837285)
      ·
        refine ⟨6035749334994884667719491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32190663119972718227837285 6035749334994884667719491)
        ·
          refine ⟨9053624002492327001579237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035749334994884667719491 9053624002492327001579237)
          ·
            refine ⟨1697554500467311312796107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9053624002492327001579237 1697554500467311312796107)
            ·
              refine ⟨2546331750700966969194161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697554500467311312796107 2546331750700966969194161)
              ·
                refine ⟨1909748813025725226895621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2546331750700966969194161 1909748813025725226895621)
                ·
                  refine ⟨358077902442323480042929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1909748813025725226895621 358077902442323480042929)
                  ·
                    rfl

theorem cell21_1569047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 4].length) (baseStart_1569047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569047 prefixEnd_1569047 := by exact prefixLift 1569047
  have htrace : WordTrace (prefixWord ++ tailWord_1569047) baseStart_1569047 baseEnd_1569047 := by
    simpa [prefixWord, tailWord_1569047, baseEnd_1569047] using wordTrace_append hprefix tailTrace_1569047
  have hstable : (prefixWord ++ tailWord_1569047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569047).length < 2 ^ (prefixWord ++ tailWord_1569047).sum := by decide
  have hdescent : baseEnd_1569047 < baseStart_1569047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569064 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_1569064 : Nat := 118140960795 + 1569064 * 2 ^ 59
def prefixEnd_1569064 : Nat := 4983230072969 + 3 ^ 40 * 1569064 * 2
def baseEnd_1569064 : Nat := 358081782073935228259561

theorem tailTrace_1569064 : CollatzResearch.WordTrace tailWord_1569064 prefixEnd_1569064 358081782073935228259561 := by
  unfold tailWord_1569064
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614232793778288820873123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38152310391704385094497497 28614232793778288820873123)
  ·
    refine ⟨42921349190667433231309685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28614232793778288820873123 42921349190667433231309685)
    ·
      refine ⟨4023876486625071865435283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42921349190667433231309685 4023876486625071865435283)
      ·
        refine ⟨6035814729937607798152925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4023876486625071865435283 6035814729937607798152925)
        ·
          refine ⟨2263430523726602924307347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6035814729937607798152925 2263430523726602924307347)
          ·
            refine ⟨3395145785589904386461021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263430523726602924307347 3395145785589904386461021)
            ·
              refine ⟨1273179669596214144922883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3395145785589904386461021 1273179669596214144922883)
              ·
                refine ⟨1909769504394321217384325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273179669596214144922883 1909769504394321217384325)
                ·
                  refine ⟨358081782073935228259561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1909769504394321217384325 358081782073935228259561)
                  ·
                    rfl

theorem cell21_1569064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_1569064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569064 prefixEnd_1569064 := by exact prefixLift 1569064
  have htrace : WordTrace (prefixWord ++ tailWord_1569064) baseStart_1569064 baseEnd_1569064 := by
    simpa [prefixWord, tailWord_1569064, baseEnd_1569064] using wordTrace_append hprefix tailTrace_1569064
  have hstable : (prefixWord ++ tailWord_1569064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569064).length < 2 ^ (prefixWord ++ tailWord_1569064).sum := by decide
  have hdescent : baseEnd_1569064 < baseStart_1569064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569109 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 5]
def baseStart_1569109 : Nat := 118140960795 + 1569109 * 2 ^ 59
def prefixEnd_1569109 : Nat := 4983230072969 + 3 ^ 40 * 1569109 * 2
def baseEnd_1569109 : Nat := 358092051687025150009469

theorem tailTrace_1569109 : CollatzResearch.WordTrace tailWord_1569109 prefixEnd_1569109 358092051687025150009469 := by
  unfold tailWord_1569109
  simp only [CollatzResearch.WordTrace]
  refine ⟨57230106872393550327134381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38153404581595700218089587 57230106872393550327134381)
  ·
    refine ⟨21461290077147581372675393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57230106872393550327134381 21461290077147581372675393)
    ·
      refine ⟨16095967557860686029506545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21461290077147581372675393 16095967557860686029506545)
      ·
        refine ⟨12071975668395514522129909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16095967557860686029506545 12071975668395514522129909)
        ·
          refine ⟨1131747718912079486449679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12071975668395514522129909 1131747718912079486449679)
          ·
            refine ⟨1697621578368119229674519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131747718912079486449679 1697621578368119229674519)
            ·
              refine ⟨2546432367552178844511779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697621578368119229674519 2546432367552178844511779)
              ·
                refine ⟨3819648551328268266767669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546432367552178844511779 3819648551328268266767669)
                ·
                  refine ⟨358092051687025150009469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3819648551328268266767669 358092051687025150009469)
                  ·
                    rfl

theorem cell21_1569109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_1569109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569109 prefixEnd_1569109 := by exact prefixLift 1569109
  have htrace : WordTrace (prefixWord ++ tailWord_1569109) baseStart_1569109 baseEnd_1569109 := by
    simpa [prefixWord, tailWord_1569109, baseEnd_1569109] using wordTrace_append hprefix tailTrace_1569109
  have hstable : (prefixWord ++ tailWord_1569109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569109).length < 2 ^ (prefixWord ++ tailWord_1569109).sum := by decide
  have hdescent : baseEnd_1569109 < baseStart_1569109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569154 : List Nat := [3, 4, 2, 1, 3, 8]
def baseStart_1569154 : Nat := 118140960795 + 1569154 * 2 ^ 59
def prefixEnd_1569154 : Nat := 4983230072969 + 3 ^ 40 * 1569154 * 2
def baseEnd_1569154 : Nat := 13263048937041298954051

theorem tailTrace_1569154 : CollatzResearch.WordTrace tailWord_1569154 prefixEnd_1569154 13263048937041298954051 := by
  unfold tailWord_1569154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14307937039307630753130629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38154498771487015341681677 14307937039307630753130629)
  ·
    refine ⟨2682738194870180766211993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14307937039307630753130629 2682738194870180766211993)
    ·
      refine ⟨2012053646152635574658995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2682738194870180766211993 2012053646152635574658995)
      ·
        refine ⟨3018080469228953361988493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012053646152635574658995 3018080469228953361988493)
        ·
          refine ⟨1131780175960857510745685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3018080469228953361988493 1131780175960857510745685)
          ·
            refine ⟨13263048937041298954051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1131780175960857510745685 13263048937041298954051)
            ·
              rfl

theorem cell21_1569154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 8].length) (baseStart_1569154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569154 prefixEnd_1569154 := by exact prefixLift 1569154
  have htrace : WordTrace (prefixWord ++ tailWord_1569154) baseStart_1569154 baseEnd_1569154 := by
    simpa [prefixWord, tailWord_1569154, baseEnd_1569154] using wordTrace_append hprefix tailTrace_1569154
  have hstable : (prefixWord ++ tailWord_1569154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569154).length < 2 ^ (prefixWord ++ tailWord_1569154).sum := by decide
  have hdescent : baseEnd_1569154 < baseStart_1569154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569261 : List Nat := [1, 5, 1, 3, 1, 1, 3, 3, 3]
def baseStart_1569261 : Nat := 118140960795 + 1569261 * 2 ^ 59
def prefixEnd_1569261 : Nat := 4983230072969 + 3 ^ 40 * 1569261 * 2
def baseEnd_1569261 : Nat := 358126740157906663475825

theorem tailTrace_1569261 : CollatzResearch.WordTrace tailWord_1569261 prefixEnd_1569261 358126740157906663475825 := by
  unfold tailWord_1569261
  simp only [CollatzResearch.WordTrace]
  refine ⟨57235650767842880286667637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38157100511895253524445091 57235650767842880286667637)
  ·
    refine ⟨5365842259485270026875091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57235650767842880286667637 5365842259485270026875091)
    ·
      refine ⟨8048763389227905040312637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5365842259485270026875091 8048763389227905040312637)
      ·
        refine ⟨3018286270960464390117239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8048763389227905040312637 3018286270960464390117239)
        ·
          refine ⟨4527429406440696585175859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3018286270960464390117239 4527429406440696585175859)
          ·
            refine ⟨6791144109661044877763789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4527429406440696585175859 6791144109661044877763789)
            ·
              refine ⟨2546679041122891829161421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6791144109661044877763789 2546679041122891829161421)
              ·
                refine ⟨955004640421084435935533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2546679041122891829161421 955004640421084435935533)
                ·
                  refine ⟨358126740157906663475825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955004640421084435935533 358126740157906663475825)
                  ·
                    rfl

theorem cell21_1569261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_1569261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569261 prefixEnd_1569261 := by exact prefixLift 1569261
  have htrace : WordTrace (prefixWord ++ tailWord_1569261) baseStart_1569261 baseEnd_1569261 := by
    simpa [prefixWord, tailWord_1569261, baseEnd_1569261] using wordTrace_append hprefix tailTrace_1569261
  have hstable : (prefixWord ++ tailWord_1569261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569261).length < 2 ^ (prefixWord ++ tailWord_1569261).sum := by decide
  have hdescent : baseEnd_1569261 < baseStart_1569261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569441 : List Nat := [1, 2, 3, 3, 4, 1, 7]
def baseStart_1569441 : Nat := 118140960795 + 1569441 * 2 ^ 59
def prefixEnd_1569441 : Nat := 4983230072969 + 3 ^ 40 * 1569441 * 2
def baseEnd_1569441 : Nat := 39796424290029594497273

theorem tailTrace_1569441 : CollatzResearch.WordTrace tailWord_1569441 prefixEnd_1569441 39796424290029594497273 := by
  unfold tailWord_1569441
  simp only [CollatzResearch.WordTrace]
  refine ⟨57242215907190771028220177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38161477271460514018813451 57242215907190771028220177)
  ·
    refine ⟨42931661930393078271165133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57242215907190771028220177 42931661930393078271165133)
    ·
      refine ⟨16099373223897404351686925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42931661930393078271165133 16099373223897404351686925)
      ·
        refine ⟨6037264958961526631882597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16099373223897404351686925 6037264958961526631882597)
        ·
          refine ⟨1131987179805286243477987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6037264958961526631882597 1131987179805286243477987)
          ·
            refine ⟨1697980769707929365216981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131987179805286243477987 1697980769707929365216981)
            ·
              refine ⟨39796424290029594497273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1697980769707929365216981 39796424290029594497273)
              ·
                rfl

theorem cell21_1569441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 7].length) (baseStart_1569441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569441 prefixEnd_1569441 := by exact prefixLift 1569441
  have htrace : WordTrace (prefixWord ++ tailWord_1569441) baseStart_1569441 baseEnd_1569441 := by
    simpa [prefixWord, tailWord_1569441, baseEnd_1569441] using wordTrace_append hprefix tailTrace_1569441
  have hstable : (prefixWord ++ tailWord_1569441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569441).length < 2 ^ (prefixWord ++ tailWord_1569441).sum := by decide
  have hdescent : baseEnd_1569441 < baseStart_1569441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569455 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 5]
def baseStart_1569455 : Nat := 118140960795 + 1569455 * 2 ^ 59
def prefixEnd_1569455 : Nat := 4983230072969 + 3 ^ 40 * 1569455 * 2
def baseEnd_1569455 : Nat := 358171013601005437242095

theorem tailTrace_1569455 : CollatzResearch.WordTrace tailWord_1569455 prefixEnd_1569455 358171013601005437242095 := by
  unfold tailWord_1569455
  simp only [CollatzResearch.WordTrace]
  refine ⟨57242726529140051419229819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38161817686093367612819879 57242726529140051419229819)
  ·
    refine ⟨85864089793710077128844729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57242726529140051419229819 85864089793710077128844729)
    ·
      refine ⟨64398067345282557846633547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85864089793710077128844729 64398067345282557846633547)
      ·
        refine ⟨96597101017923836769950321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64398067345282557846633547 96597101017923836769950321)
        ·
          refine ⟨72447825763442877577462741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96597101017923836769950321 72447825763442877577462741)
          ·
            refine ⟨1697995916330692443221783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 72447825763442877577462741 1697995916330692443221783)
            ·
              refine ⟨2546993874496038664832675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697995916330692443221783 2546993874496038664832675)
              ·
                refine ⟨3820490811744057997249013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546993874496038664832675 3820490811744057997249013)
                ·
                  refine ⟨358171013601005437242095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3820490811744057997249013 358171013601005437242095)
                  ·
                    rfl

theorem cell21_1569455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 5].length) (baseStart_1569455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569455 prefixEnd_1569455 := by exact prefixLift 1569455
  have htrace : WordTrace (prefixWord ++ tailWord_1569455) baseStart_1569455 baseEnd_1569455 := by
    simpa [prefixWord, tailWord_1569455, baseEnd_1569455] using wordTrace_append hprefix tailTrace_1569455
  have hstable : (prefixWord ++ tailWord_1569455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569455).length < 2 ^ (prefixWord ++ tailWord_1569455).sum := by decide
  have hdescent : baseEnd_1569455 < baseStart_1569455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569500 : List Nat := [2, 2, 5, 1, 1, 10]
def baseStart_1569500 : Nat := 118140960795 + 1569500 * 2 ^ 59
def prefixEnd_1569500 : Nat := 4983230072969 + 3 ^ 40 * 1569500 * 2
def baseEnd_1569500 : Nat := 13265973452373902184889

theorem tailTrace_1569500 : CollatzResearch.WordTrace tailWord_1569500 prefixEnd_1569500 13265973452373902184889 := by
  unfold tailWord_1569500
  simp only [CollatzResearch.WordTrace]
  refine ⟨28622183906988512052308977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38162911875984682736411969 28622183906988512052308977)
  ·
    refine ⟨21466637930241384039231733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28622183906988512052308977 21466637930241384039231733)
    ·
      refine ⟨2012497305960129753677975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21466637930241384039231733 2012497305960129753677975)
      ·
        refine ⟨3018745958940194630516963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012497305960129753677975 3018745958940194630516963)
        ·
          refine ⟨4528118938410291945775445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3018745958940194630516963 4528118938410291945775445)
          ·
            refine ⟨13265973452373902184889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4528118938410291945775445 13265973452373902184889)
            ·
              rfl

theorem cell21_1569500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 10].length) (baseStart_1569500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569500 prefixEnd_1569500 := by exact prefixLift 1569500
  have htrace : WordTrace (prefixWord ++ tailWord_1569500) baseStart_1569500 baseEnd_1569500 := by
    simpa [prefixWord, tailWord_1569500, baseEnd_1569500] using wordTrace_append hprefix tailTrace_1569500
  have hstable : (prefixWord ++ tailWord_1569500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569500).length < 2 ^ (prefixWord ++ tailWord_1569500).sum := by decide
  have hdescent : baseEnd_1569500 < baseStart_1569500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569514 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1569514 : Nat := 118140960795 + 1569514 * 2 ^ 59
def prefixEnd_1569514 : Nat := 4983230072969 + 3 ^ 40 * 1569514 * 2
def baseEnd_1569514 : Nat := 358184478204834445758641

theorem tailTrace_1569514 : CollatzResearch.WordTrace tailWord_1569514 prefixEnd_1569514 358184478204834445758641 := by
  unfold tailWord_1569514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14311219608981576123906899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38163252290617536330418397 14311219608981576123906899)
  ·
    refine ⟨21466829413472364185860349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14311219608981576123906899 21466829413472364185860349)
    ·
      refine ⟨8050061030052136569697631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21466829413472364185860349 8050061030052136569697631)
      ·
        refine ⟨12075091545078204854546447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050061030052136569697631 12075091545078204854546447)
        ·
          refine ⟨18112637317617307281819671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12075091545078204854546447 18112637317617307281819671)
          ·
            refine ⟨27168955976425960922729507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18112637317617307281819671 27168955976425960922729507)
            ·
              refine ⟨40753433964638941384094261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27168955976425960922729507 40753433964638941384094261)
              ·
                refine ⟨3820634434184900754758837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40753433964638941384094261 3820634434184900754758837)
                ·
                  refine ⟨358184478204834445758641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3820634434184900754758837 358184478204834445758641)
                  ·
                    rfl

theorem cell21_1569514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1569514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569514 prefixEnd_1569514 := by exact prefixLift 1569514
  have htrace : WordTrace (prefixWord ++ tailWord_1569514) baseStart_1569514 baseEnd_1569514 := by
    simpa [prefixWord, tailWord_1569514, baseEnd_1569514] using wordTrace_append hprefix tailTrace_1569514
  have hstable : (prefixWord ++ tailWord_1569514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569514).length < 2 ^ (prefixWord ++ tailWord_1569514).sum := by decide
  have hdescent : baseEnd_1569514 < baseStart_1569514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569621 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 4]
def baseStart_1569621 : Nat := 118140960795 + 1569621 * 2 ^ 59
def prefixEnd_1569621 : Nat := 4983230072969 + 3 ^ 40 * 1569621 * 2
def baseEnd_1569621 : Nat := 358208897062626037475089

theorem tailTrace_1569621 : CollatzResearch.WordTrace tailWord_1569621 prefixEnd_1569621 358208897062626037475089 := by
  unfold tailWord_1569621
  simp only [CollatzResearch.WordTrace]
  refine ⟨57248781046538661769772717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38165854031025774513181811 57248781046538661769772717)
  ·
    refine ⟨21468292892451998163664769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57248781046538661769772717 21468292892451998163664769)
    ·
      refine ⟨16101219669338998622748577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21468292892451998163664769 16101219669338998622748577)
      ·
        refine ⟨12075914752004248967061433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16101219669338998622748577 12075914752004248967061433)
        ·
          refine ⟨9056936064003186725296075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12075914752004248967061433 9056936064003186725296075)
          ·
            refine ⟨13585404096004780087944113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9056936064003186725296075 13585404096004780087944113)
            ·
              refine ⟨10189053072003585065958085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13585404096004780087944113 10189053072003585065958085)
              ·
                refine ⟨1910447451000672199867141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10189053072003585065958085 1910447451000672199867141)
                ·
                  refine ⟨358208897062626037475089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1910447451000672199867141 358208897062626037475089)
                  ·
                    rfl

theorem cell21_1569621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_1569621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569621 prefixEnd_1569621 := by exact prefixLift 1569621
  have htrace : WordTrace (prefixWord ++ tailWord_1569621) baseStart_1569621 baseEnd_1569621 := by
    simpa [prefixWord, tailWord_1569621, baseEnd_1569621] using wordTrace_append hprefix tailTrace_1569621
  have hstable : (prefixWord ++ tailWord_1569621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569621).length < 2 ^ (prefixWord ++ tailWord_1569621).sum := by decide
  have hdescent : baseEnd_1569621 < baseStart_1569621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569635 : List Nat := [1, 1, 1, 5, 3, 1, 1, 8]
def baseStart_1569635 : Nat := 118140960795 + 1569635 * 2 ^ 59
def prefixEnd_1569635 : Nat := 4983230072969 + 3 ^ 40 * 1569635 * 2
def baseEnd_1569635 : Nat := 119404030684455041413909

theorem tailTrace_1569635 : CollatzResearch.WordTrace tailWord_1569635 prefixEnd_1569635 119404030684455041413909 := by
  unfold tailWord_1569635
  simp only [CollatzResearch.WordTrace]
  refine ⟨57249291668487942160782359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38166194445658628107188239 57249291668487942160782359)
  ·
    refine ⟨85873937502731913241173539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57249291668487942160782359 85873937502731913241173539)
    ·
      refine ⟨128810906254097869861760309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85873937502731913241173539 128810906254097869861760309)
      ·
        refine ⟨12076022461321675299540029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128810906254097869861760309 12076022461321675299540029)
        ·
          refine ⟨4528508422995628237327511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12076022461321675299540029 4528508422995628237327511)
          ·
            refine ⟨6792762634493442355991267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528508422995628237327511 6792762634493442355991267)
            ·
              refine ⟨10189143951740163533986901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792762634493442355991267 10189143951740163533986901)
              ·
                refine ⟨119404030684455041413909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10189143951740163533986901 119404030684455041413909)
                ·
                  rfl

theorem cell21_1569635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 8].length) (baseStart_1569635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569635 prefixEnd_1569635 := by exact prefixLift 1569635
  have htrace : WordTrace (prefixWord ++ tailWord_1569635) baseStart_1569635 baseEnd_1569635 := by
    simpa [prefixWord, tailWord_1569635, baseEnd_1569635] using wordTrace_append hprefix tailTrace_1569635
  have hstable : (prefixWord ++ tailWord_1569635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569635).length < 2 ^ (prefixWord ++ tailWord_1569635).sum := by decide
  have hdescent : baseEnd_1569635 < baseStart_1569635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569686 : List Nat := [5, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1569686 : Nat := 118140960795 + 1569686 * 2 ^ 59
def prefixEnd_1569686 : Nat := 4983230072969 + 3 ^ 40 * 1569686 * 2
def baseEnd_1569686 : Nat := 119407910316066789630541

theorem tailTrace_1569686 : CollatzResearch.WordTrace tailWord_1569686 prefixEnd_1569686 119407910316066789630541 := by
  unfold tailWord_1569686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578196986956448616930557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38167434527535451913925941 3578196986956448616930557)
  ·
    refine ⟨1341823870108668231348959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3578196986956448616930557 1341823870108668231348959)
    ·
      refine ⟨2012735805163002347023439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341823870108668231348959 2012735805163002347023439)
      ·
        refine ⟨3019103707744503520535159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012735805163002347023439 3019103707744503520535159)
        ·
          refine ⟨4528655561616755280802739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019103707744503520535159 4528655561616755280802739)
          ·
            refine ⟨6792983342425132921204109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528655561616755280802739 6792983342425132921204109)
            ·
              refine ⟨2547368753409424845451541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6792983342425132921204109 2547368753409424845451541)
              ·
                refine ⟨119407910316066789630541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2547368753409424845451541 119407910316066789630541)
                ·
                  rfl

theorem cell21_1569686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1569686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569686 prefixEnd_1569686 := by exact prefixLift 1569686
  have htrace : WordTrace (prefixWord ++ tailWord_1569686) baseStart_1569686 baseEnd_1569686 := by
    simpa [prefixWord, tailWord_1569686, baseEnd_1569686] using wordTrace_append hprefix tailTrace_1569686
  have hstable : (prefixWord ++ tailWord_1569686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569686).length < 2 ^ (prefixWord ++ tailWord_1569686).sum := by decide
  have hdescent : baseEnd_1569686 < baseStart_1569686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569742 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1569742 : Nat := 118140960795 + 1569742 * 2 ^ 59
def prefixEnd_1569742 : Nat := 4983230072969 + 3 ^ 40 * 1569742 * 2
def baseEnd_1569742 : Nat := 358236510911156715958175

theorem tailTrace_1569742 : CollatzResearch.WordTrace tailWord_1569742 prefixEnd_1569742 358236510911156715958175 := by
  unfold tailWord_1569742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7156649284887537429365935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38168796186066866289951653 7156649284887537429365935)
  ·
    refine ⟨10734973927331306144048903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7156649284887537429365935 10734973927331306144048903)
    ·
      refine ⟨16102460890996959216073355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10734973927331306144048903 16102460890996959216073355)
      ·
        refine ⟨24153691336495438824110033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16102460890996959216073355 24153691336495438824110033)
        ·
          refine ⟨18115268502371579118082525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24153691336495438824110033 18115268502371579118082525)
          ·
            refine ⟨6793225688389342169280947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18115268502371579118082525 6793225688389342169280947)
            ·
              refine ⟨10189838532584013253921421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793225688389342169280947 10189838532584013253921421)
              ·
                refine ⟨3821189449719004970220533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10189838532584013253921421 3821189449719004970220533)
                ·
                  refine ⟨358236510911156715958175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3821189449719004970220533 358236510911156715958175)
                  ·
                    rfl

theorem cell21_1569742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1569742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569742 prefixEnd_1569742 := by exact prefixLift 1569742
  have htrace : WordTrace (prefixWord ++ tailWord_1569742) baseStart_1569742 baseEnd_1569742 := by
    simpa [prefixWord, tailWord_1569742, baseEnd_1569742] using wordTrace_append hprefix tailTrace_1569742
  have hstable : (prefixWord ++ tailWord_1569742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569742).length < 2 ^ (prefixWord ++ tailWord_1569742).sum := by decide
  have hdescent : baseEnd_1569742 < baseStart_1569742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569762 : List Nat := [3, 3, 3, 1, 1, 3, 2, 5]
def baseStart_1569762 : Nat := 118140960795 + 1569762 * 2 ^ 59
def prefixEnd_1569762 : Nat := 4983230072969 + 3 ^ 40 * 1569762 * 2
def baseEnd_1569762 : Nat := 119413691727880375208267

theorem tailTrace_1569762 : CollatzResearch.WordTrace tailWord_1569762 prefixEnd_1569762 119413691727880375208267 := by
  unfold tailWord_1569762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14313480934756960712663885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38169282492685228567103693 14313480934756960712663885)
  ·
    refine ⟨5367555350533860267248957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14313480934756960712663885 5367555350533860267248957)
    ·
      refine ⟨2012833256450197600218359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5367555350533860267248957 2012833256450197600218359)
      ·
        refine ⟨3019249884675296400327539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012833256450197600218359 3019249884675296400327539)
        ·
          refine ⟨4528874827012944600491309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019249884675296400327539 4528874827012944600491309)
          ·
            refine ⟨1698328060129854225184241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4528874827012944600491309 1698328060129854225184241)
            ·
              refine ⟨1273746045097390668888181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698328060129854225184241 1273746045097390668888181)
              ·
                refine ⟨119413691727880375208267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1273746045097390668888181 119413691727880375208267)
                ·
                  rfl

theorem cell21_1569762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_1569762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569762 prefixEnd_1569762 := by exact prefixLift 1569762
  have htrace : WordTrace (prefixWord ++ tailWord_1569762) baseStart_1569762 baseEnd_1569762 := by
    simpa [prefixWord, tailWord_1569762, baseEnd_1569762] using wordTrace_append hprefix tailTrace_1569762
  have hstable : (prefixWord ++ tailWord_1569762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569762).length < 2 ^ (prefixWord ++ tailWord_1569762).sum := by decide
  have hdescent : baseEnd_1569762 < baseStart_1569762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569849 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 4]
def baseStart_1569849 : Nat := 118140960795 + 1569849 * 2 ^ 59
def prefixEnd_1569849 : Nat := 4983230072969 + 3 ^ 40 * 1569849 * 2
def baseEnd_1569849 : Nat := 358260929768948307674623

theorem tailTrace_1569849 : CollatzResearch.WordTrace tailWord_1569849 prefixEnd_1569849 358260929768948307674623 := by
  unfold tailWord_1569849
  simp only [CollatzResearch.WordTrace]
  refine ⟨57257096889712656709072601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38171397926475104472715067 57257096889712656709072601)
  ·
    refine ⟨42942822667284492531804451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57257096889712656709072601 42942822667284492531804451)
    ·
      refine ⟨64414234000926738797706677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42942822667284492531804451 64414234000926738797706677)
      ·
        refine ⟨6038834437586881762285001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64414234000926738797706677 6038834437586881762285001)
        ·
          refine ⟨4529125828190161321713751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6038834437586881762285001 4529125828190161321713751)
          ·
            refine ⟨6793688742285241982570627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529125828190161321713751 6793688742285241982570627)
            ·
              refine ⟨10190533113427862973855941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793688742285241982570627 10190533113427862973855941)
              ·
                refine ⟨1910724958767724307597989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10190533113427862973855941 1910724958767724307597989)
                ·
                  refine ⟨358260929768948307674623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1910724958767724307597989 358260929768948307674623)
                  ·
                    rfl

theorem cell21_1569849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_1569849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569849 prefixEnd_1569849 := by exact prefixLift 1569849
  have htrace : WordTrace (prefixWord ++ tailWord_1569849) baseStart_1569849 baseEnd_1569849 := by
    simpa [prefixWord, tailWord_1569849, baseEnd_1569849] using wordTrace_append hprefix tailTrace_1569849
  have hstable : (prefixWord ++ tailWord_1569849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569849).length < 2 ^ (prefixWord ++ tailWord_1569849).sum := by decide
  have hdescent : baseEnd_1569849 < baseStart_1569849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569852 : List Nat := [2, 2, 2, 2, 2, 2, 4, 2, 3]
def baseStart_1569852 : Nat := 118140960795 + 1569852 * 2 ^ 59
def prefixEnd_1569852 : Nat := 4983230072969 + 3 ^ 40 * 1569852 * 2
def baseEnd_1569852 : Nat := 358261614409820969124617

theorem tailTrace_1569852 : CollatzResearch.WordTrace tailWord_1569852 prefixEnd_1569852 358261614409820969124617 := by
  unfold tailWord_1569852
  simp only [CollatzResearch.WordTrace]
  refine ⟨28628603154350894110715905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38171470872467858814287873 28628603154350894110715905)
  ·
    refine ⟨21471452365763170583036929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28628603154350894110715905 21471452365763170583036929)
    ·
      refine ⟨16103589274322377937277697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21471452365763170583036929 16103589274322377937277697)
      ·
        refine ⟨12077691955741783452958273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16103589274322377937277697 12077691955741783452958273)
        ·
          refine ⟨9058268966806337589718705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12077691955741783452958273 9058268966806337589718705)
          ·
            refine ⟨6793701725104753192289029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058268966806337589718705 6793701725104753192289029)
            ·
              refine ⟨1273819073457141223554193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6793701725104753192289029 1273819073457141223554193)
              ·
                refine ⟨955364305092855917665645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273819073457141223554193 955364305092855917665645)
                ·
                  refine ⟨358261614409820969124617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955364305092855917665645 358261614409820969124617)
                  ·
                    rfl

theorem cell21_1569852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_1569852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569852 prefixEnd_1569852 := by exact prefixLift 1569852
  have htrace : WordTrace (prefixWord ++ tailWord_1569852) baseStart_1569852 baseEnd_1569852 := by
    simpa [prefixWord, tailWord_1569852, baseEnd_1569852] using wordTrace_append hprefix tailTrace_1569852
  have hstable : (prefixWord ++ tailWord_1569852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569852).length < 2 ^ (prefixWord ++ tailWord_1569852).sum := by decide
  have hdescent : baseEnd_1569852 < baseStart_1569852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569863 : List Nat := [1, 1, 4, 1, 3, 2, 3, 6]
def baseStart_1569863 : Nat := 118140960795 + 1569863 * 2 ^ 59
def prefixEnd_1569863 : Nat := 4983230072969 + 3 ^ 40 * 1569863 * 2
def baseEnd_1569863 : Nat := 119421374919895798147087

theorem tailTrace_1569863 : CollatzResearch.WordTrace tailWord_1569863 prefixEnd_1569863 119421374919895798147087 := by
  unfold tailWord_1569863
  simp only [CollatzResearch.WordTrace]
  refine ⟨57257607511661937100082243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38171738341107958066721495 57257607511661937100082243)
  ·
    refine ⟨85886411267492905650123365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57257607511661937100082243 85886411267492905650123365)
    ·
      refine ⟨16103702112654919809398131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85886411267492905650123365 16103702112654919809398131)
      ·
        refine ⟨24155553168982379714097197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16103702112654919809398131 24155553168982379714097197)
        ·
          refine ⟨9058332438368392392786449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24155553168982379714097197 9058332438368392392786449)
          ·
            refine ⟨6793749328776294294589837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058332438368392392786449 6793749328776294294589837)
            ·
              refine ⟨2547655998291110360471189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6793749328776294294589837 2547655998291110360471189)
              ·
                refine ⟨119421374919895798147087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2547655998291110360471189 119421374919895798147087)
                ·
                  rfl

theorem cell21_1569863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 6].length) (baseStart_1569863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569863 prefixEnd_1569863 := by exact prefixLift 1569863
  have htrace : WordTrace (prefixWord ++ tailWord_1569863) baseStart_1569863 baseEnd_1569863 := by
    simpa [prefixWord, tailWord_1569863, baseEnd_1569863] using wordTrace_append hprefix tailTrace_1569863
  have hstable : (prefixWord ++ tailWord_1569863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569863).length < 2 ^ (prefixWord ++ tailWord_1569863).sum := by decide
  have hdescent : baseEnd_1569863 < baseStart_1569863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569886 : List Nat := [4, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1569886 : Nat := 118140960795 + 1569886 * 2 ^ 59
def prefixEnd_1569886 : Nat := 4983230072969 + 3 ^ 40 * 1569886 * 2
def baseEnd_1569886 : Nat := 358269373673044465557881

theorem tailTrace_1569886 : CollatzResearch.WordTrace tailWord_1569886 prefixEnd_1569886 358269373673044465557881 := by
  unfold tailWord_1569886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157305798822326503521189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38172297593719074685446341 7157305798822326503521189)
  ·
    refine ⟨1341994837279186219410223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7157305798822326503521189 1341994837279186219410223)
    ·
      refine ⟨2012992255918779329115335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341994837279186219410223 2012992255918779329115335)
      ·
        refine ⟨3019488383878168993673003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012992255918779329115335 3019488383878168993673003)
        ·
          refine ⟨4529232575817253490509505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019488383878168993673003 4529232575817253490509505)
          ·
            refine ⟨3396924431862940117882129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4529232575817253490509505 3396924431862940117882129)
            ·
              refine ⟨2547693323897205088411597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396924431862940117882129 2547693323897205088411597)
              ·
                refine ⟨955384996461451908154349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2547693323897205088411597 955384996461451908154349)
                ·
                  refine ⟨358269373673044465557881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955384996461451908154349 358269373673044465557881)
                  ·
                    rfl

theorem cell21_1569886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1569886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569886 prefixEnd_1569886 := by exact prefixLift 1569886
  have htrace : WordTrace (prefixWord ++ tailWord_1569886) baseStart_1569886 baseEnd_1569886 := by
    simpa [prefixWord, tailWord_1569886, baseEnd_1569886] using wordTrace_append hprefix tailTrace_1569886
  have hstable : (prefixWord ++ tailWord_1569886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569886).length < 2 ^ (prefixWord ++ tailWord_1569886).sum := by decide
  have hdescent : baseEnd_1569886 < baseStart_1569886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569939 : List Nat := [1, 1, 1, 2, 1, 2, 8, 5]
def baseStart_1569939 : Nat := 118140960795 + 1569939 * 2 ^ 59
def prefixEnd_1569939 : Nat := 4983230072969 + 3 ^ 40 * 1569939 * 2
def baseEnd_1569939 : Nat := 119427156331709383724813

theorem tailTrace_1569939 : CollatzResearch.WordTrace tailWord_1569939 prefixEnd_1569939 119427156331709383724813 := by
  unfold tailWord_1569939
  simp only [CollatzResearch.WordTrace]
  refine ⟨57260379459386602079848871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38173586306257734719899247 57260379459386602079848871)
  ·
    refine ⟨85890569189079903119773307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57260379459386602079848871 85890569189079903119773307)
    ·
      refine ⟨128835853783619854679659961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85890569189079903119773307 128835853783619854679659961)
      ·
        refine ⟨96626890337714891009744971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128835853783619854679659961 96626890337714891009744971)
        ·
          refine ⟨144940335506572336514617457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96626890337714891009744971 144940335506572336514617457)
          ·
            refine ⟨108705251629929252385963093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144940335506572336514617457 108705251629929252385963093)
            ·
              refine ⟨1273889667538233426398005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 108705251629929252385963093 1273889667538233426398005)
              ·
                refine ⟨119427156331709383724813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1273889667538233426398005 119427156331709383724813)
                ·
                  rfl

theorem cell21_1569939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 5].length) (baseStart_1569939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569939 prefixEnd_1569939 := by exact prefixLift 1569939
  have htrace : WordTrace (prefixWord ++ tailWord_1569939) baseStart_1569939 baseEnd_1569939 := by
    simpa [prefixWord, tailWord_1569939, baseEnd_1569939] using wordTrace_append hprefix tailTrace_1569939
  have hstable : (prefixWord ++ tailWord_1569939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569939).length < 2 ^ (prefixWord ++ tailWord_1569939).sum := by decide
  have hdescent : baseEnd_1569939 < baseStart_1569939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569970 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1569970 : Nat := 118140960795 + 1569970 * 2 ^ 59
def prefixEnd_1569970 : Nat := 4983230072969 + 3 ^ 40 * 1569970 * 2
def baseEnd_1569970 : Nat := 358288543617478986157709

theorem tailTrace_1569970 : CollatzResearch.WordTrace tailWord_1569970 prefixEnd_1569970 358288543617478986157709 := by
  unfold tailWord_1569970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14315377530568573593556841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38174340081516196249484909 14315377530568573593556841)
  ·
    refine ⟨10736533147926430195167631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14315377530568573593556841 10736533147926430195167631)
    ·
      refine ⟨16104799721889645292751447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10736533147926430195167631 16104799721889645292751447)
      ·
        refine ⟨24157199582834467939127171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16104799721889645292751447 24157199582834467939127171)
        ·
          refine ⟨36235799374251701908690757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24157199582834467939127171 36235799374251701908690757)
          ·
            refine ⟨6794212382672194107879517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36235799374251701908690757 6794212382672194107879517)
            ·
              refine ⟨2547829643502072790454819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6794212382672194107879517 2547829643502072790454819)
              ·
                refine ⟨3821744465253109185682229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547829643502072790454819 3821744465253109185682229)
                ·
                  refine ⟨358288543617478986157709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3821744465253109185682229 358288543617478986157709)
                  ·
                    rfl

theorem cell21_1569970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1569970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1569970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1569970 prefixEnd_1569970 := by exact prefixLift 1569970
  have htrace : WordTrace (prefixWord ++ tailWord_1569970) baseStart_1569970 baseEnd_1569970 := by
    simpa [prefixWord, tailWord_1569970, baseEnd_1569970] using wordTrace_append hprefix tailTrace_1569970
  have hstable : (prefixWord ++ tailWord_1569970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569970).length < 2 ^ (prefixWord ++ tailWord_1569970).sum := by decide
  have hdescent : baseEnd_1569970 < baseStart_1569970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570021 : List Nat := [1, 3, 1, 4, 3, 2, 2, 2, 3]
def baseStart_1570021 : Nat := 118140960795 + 1570021 * 2 ^ 59
def prefixEnd_1570021 : Nat := 4983230072969 + 3 ^ 40 * 1570021 * 2
def baseEnd_1570021 : Nat := 358300182512314230807605

theorem tailTrace_1570021 : CollatzResearch.WordTrace tailWord_1570021 prefixEnd_1570021 358300182512314230807605 := by
  unfold tailWord_1570021
  simp only [CollatzResearch.WordTrace]
  refine ⟨57263370245089530084333917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38175580163393020056222611 57263370245089530084333917)
  ·
    refine ⟨21473763841908573781625219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57263370245089530084333917 21473763841908573781625219)
    ·
      refine ⟨32210645762862860672437829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21473763841908573781625219 32210645762862860672437829)
      ·
        refine ⟨6039496080536786376082093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32210645762862860672437829 6039496080536786376082093)
        ·
          refine ⟨2264811030201294891030785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6039496080536786376082093 2264811030201294891030785)
          ·
            refine ⟨1698608272650971168273089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2264811030201294891030785 1698608272650971168273089)
            ·
              refine ⟨1273956204488228376204817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698608272650971168273089 1273956204488228376204817)
              ·
                refine ⟨955467153366171282153613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273956204488228376204817 955467153366171282153613)
                ·
                  refine ⟨358300182512314230807605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955467153366171282153613 358300182512314230807605)
                  ·
                    rfl

theorem cell21_1570021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_1570021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570021 prefixEnd_1570021 := by exact prefixLift 1570021
  have htrace : WordTrace (prefixWord ++ tailWord_1570021) baseStart_1570021 baseEnd_1570021 := by
    simpa [prefixWord, tailWord_1570021, baseEnd_1570021] using wordTrace_append hprefix tailTrace_1570021
  have hstable : (prefixWord ++ tailWord_1570021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570021).length < 2 ^ (prefixWord ++ tailWord_1570021).sum := by decide
  have hdescent : baseEnd_1570021 < baseStart_1570021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570046 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_1570046 : Nat := 118140960795 + 1570046 * 2 ^ 59
def prefixEnd_1570046 : Nat := 4983230072969 + 3 ^ 40 * 1570046 * 2
def baseEnd_1570046 : Nat := 358305887852919742890887

theorem tailTrace_1570046 : CollatzResearch.WordTrace tailWord_1570046 prefixEnd_1570046 358305887852919742890887 := by
  unfold tailWord_1570046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7158035258749869919249249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38176188046665972902662661 7158035258749869919249249)
  ·
    refine ⟨5368526444062402439436937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7158035258749869919249249 5368526444062402439436937)
    ·
      refine ⟨4026394833046801829577703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5368526444062402439436937 4026394833046801829577703)
      ·
        refine ⟨6039592249570202744366555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4026394833046801829577703 6039592249570202744366555)
        ·
          refine ⟨9059388374355304116549833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6039592249570202744366555 9059388374355304116549833)
          ·
            refine ⟨6794541280766478087412375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9059388374355304116549833 6794541280766478087412375)
            ·
              refine ⟨10191811921149717131118563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794541280766478087412375 10191811921149717131118563)
              ·
                refine ⟨15287717881724575696677845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10191811921149717131118563 15287717881724575696677845)
                ·
                  refine ⟨358305887852919742890887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15287717881724575696677845 358305887852919742890887)
                  ·
                    rfl

theorem cell21_1570046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_1570046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570046 prefixEnd_1570046 := by exact prefixLift 1570046
  have htrace : WordTrace (prefixWord ++ tailWord_1570046) baseStart_1570046 baseEnd_1570046 := by
    simpa [prefixWord, tailWord_1570046, baseEnd_1570046] using wordTrace_append hprefix tailTrace_1570046
  have hstable : (prefixWord ++ tailWord_1570046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570046).length < 2 ^ (prefixWord ++ tailWord_1570046).sum := by decide
  have hdescent : baseEnd_1570046 < baseStart_1570046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570077 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1570077 : Nat := 118140960795 + 1570077 * 2 ^ 59
def prefixEnd_1570077 : Nat := 4983230072969 + 3 ^ 40 * 1570077 * 2
def baseEnd_1570077 : Nat := 358312962475270577874157

theorem tailTrace_1570077 : CollatzResearch.WordTrace tailWord_1570077 prefixEnd_1570077 358312962475270577874157 := by
  unfold tailWord_1570077
  simp only [CollatzResearch.WordTrace]
  refine ⟨57265412732886651648372485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38176941821924434432248323 57265412732886651648372485)
  ·
    refine ⟨10737264887416247184069841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57265412732886651648372485 10737264887416247184069841)
    ·
      refine ⟨8052948665562185388052381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10737264887416247184069841 8052948665562185388052381)
      ·
        refine ⟨3019855749585819520519643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8052948665562185388052381 3019855749585819520519643)
        ·
          refine ⟨4529783624378729280779465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019855749585819520519643 4529783624378729280779465)
          ·
            refine ⟨3397337718284046960584599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4529783624378729280779465 3397337718284046960584599)
            ·
              refine ⟨5096006577426070440876899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397337718284046960584599 5096006577426070440876899)
              ·
                refine ⟨7644009866139105661315349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096006577426070440876899 7644009866139105661315349)
                ·
                  refine ⟨358312962475270577874157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7644009866139105661315349 358312962475270577874157)
                  ·
                    rfl

theorem cell21_1570077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1570077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570077 prefixEnd_1570077 := by exact prefixLift 1570077
  have htrace : WordTrace (prefixWord ++ tailWord_1570077) baseStart_1570077 baseEnd_1570077 := by
    simpa [prefixWord, tailWord_1570077, baseEnd_1570077] using wordTrace_append hprefix tailTrace_1570077
  have hstable : (prefixWord ++ tailWord_1570077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570077).length < 2 ^ (prefixWord ++ tailWord_1570077).sum := by decide
  have hdescent : baseEnd_1570077 < baseStart_1570077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570108 : List Nat := [2, 2, 2, 2, 1, 5, 2, 5]
def baseStart_1570108 : Nat := 118140960795 + 1570108 * 2 ^ 59
def prefixEnd_1570108 : Nat := 4983230072969 + 3 ^ 40 * 1570108 * 2
def baseEnd_1570108 : Nat := 119440012365873804285809

theorem tailTrace_1570108 : CollatzResearch.WordTrace tailWord_1570108 prefixEnd_1570108 119440012365873804285809 := by
  unfold tailWord_1570108
  simp only [CollatzResearch.WordTrace]
  refine ⟨28633271697887171971375489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38177695597182895961833985 28633271697887171971375489)
  ·
    refine ⟨21474953773415378978531617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28633271697887171971375489 21474953773415378978531617)
    ·
      refine ⟨16106215330061534233898713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21474953773415378978531617 16106215330061534233898713)
      ·
        refine ⟨12079661497546150675424035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16106215330061534233898713 12079661497546150675424035)
        ·
          refine ⟨18119492246319226013136053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12079661497546150675424035 18119492246319226013136053)
          ·
            refine ⟨1698702398092427438731505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18119492246319226013136053 1698702398092427438731505)
            ·
              refine ⟨1274026798569320579048629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698702398092427438731505 1274026798569320579048629)
              ·
                refine ⟨119440012365873804285809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1274026798569320579048629 119440012365873804285809)
                ·
                  rfl

theorem cell21_1570108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_1570108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570108 prefixEnd_1570108 := by exact prefixLift 1570108
  have htrace : WordTrace (prefixWord ++ tailWord_1570108) baseStart_1570108 baseEnd_1570108 := by
    simpa [prefixWord, tailWord_1570108, baseEnd_1570108] using wordTrace_append hprefix tailTrace_1570108
  have hstable : (prefixWord ++ tailWord_1570108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570108).length < 2 ^ (prefixWord ++ tailWord_1570108).sum := by decide
  have hdescent : baseEnd_1570108 < baseStart_1570108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570125 : List Nat := [1, 6, 1, 3, 1, 2, 7]
def baseStart_1570125 : Nat := 118140960795 + 1570125 * 2 ^ 59
def prefixEnd_1570125 : Nat := 4983230072969 + 3 ^ 40 * 1570125 * 2
def baseEnd_1570125 : Nat := 39813768525470351230451

theorem tailTrace_1570125 : CollatzResearch.WordTrace tailWord_1570125 prefixEnd_1570125 39813768525470351230451 := by
  unfold tailWord_1570125
  simp only [CollatzResearch.WordTrace]
  refine ⟨57267163436712755846119829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38178108957808503897413219 57267163436712755846119829)
  ·
    refine ⟨2684398286095910430286867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57267163436712755846119829 2684398286095910430286867)
    ·
      refine ⟨4026597429143865645430301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2684398286095910430286867 4026597429143865645430301)
      ·
        refine ⟨1509974035928949617036363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4026597429143865645430301 1509974035928949617036363)
        ·
          refine ⟨2264961053893424425554545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509974035928949617036363 2264961053893424425554545)
          ·
            refine ⟨1698720790420068319165909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2264961053893424425554545 1698720790420068319165909)
            ·
              refine ⟨39813768525470351230451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1698720790420068319165909 39813768525470351230451)
              ·
                rfl

theorem cell21_1570125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 7].length) (baseStart_1570125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570125 prefixEnd_1570125 := by exact prefixLift 1570125
  have htrace : WordTrace (prefixWord ++ tailWord_1570125) baseStart_1570125 baseEnd_1570125 := by
    simpa [prefixWord, tailWord_1570125, baseEnd_1570125] using wordTrace_append hprefix tailTrace_1570125
  have hstable : (prefixWord ++ tailWord_1570125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570125).length < 2 ^ (prefixWord ++ tailWord_1570125).sum := by decide
  have hdescent : baseEnd_1570125 < baseStart_1570125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570136 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_1570136 : Nat := 118140960795 + 1570136 * 2 ^ 59
def prefixEnd_1570136 : Nat := 4983230072969 + 3 ^ 40 * 1570136 * 2
def baseEnd_1570136 : Nat := 358326427079099586390703

theorem tailTrace_1570136 : CollatzResearch.WordTrace tailWord_1570136 prefixEnd_1570136 358326427079099586390703 := by
  unfold tailWord_1570136
  simp only [CollatzResearch.WordTrace]
  refine ⟨28633782319836452362385131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38178376426448603149846841 28633782319836452362385131)
  ·
    refine ⟨42950673479754678543577697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28633782319836452362385131 42950673479754678543577697)
    ·
      refine ⟨32213005109816008907683273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42950673479754678543577697 32213005109816008907683273)
      ·
        refine ⟨24159753832362006680762455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32213005109816008907683273 24159753832362006680762455)
        ·
          refine ⟨36239630748543010021143683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24159753832362006680762455 36239630748543010021143683)
          ·
            refine ⟨54359446122814515031715525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36239630748543010021143683 54359446122814515031715525)
            ·
              refine ⟨10192396148027721568446661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54359446122814515031715525 10192396148027721568446661)
              ·
                refine ⟨1911074277755197794083749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10192396148027721568446661 1911074277755197794083749)
                ·
                  refine ⟨358326427079099586390703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911074277755197794083749 358326427079099586390703)
                  ·
                    rfl

theorem cell21_1570136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_1570136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570136 prefixEnd_1570136 := by exact prefixLift 1570136
  have htrace : WordTrace (prefixWord ++ tailWord_1570136) baseStart_1570136 baseEnd_1570136 := by
    simpa [prefixWord, tailWord_1570136, baseEnd_1570136] using wordTrace_append hprefix tailTrace_1570136
  have hstable : (prefixWord ++ tailWord_1570136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570136).length < 2 ^ (prefixWord ++ tailWord_1570136).sum := by decide
  have hdescent : baseEnd_1570136 < baseStart_1570136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570190 : List Nat := [4, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_1570190 : Nat := 118140960795 + 1570190 * 2 ^ 59
def prefixEnd_1570190 : Nat := 4983230072969 + 3 ^ 40 * 1570190 * 2
def baseEnd_1570190 : Nat := 358338750614807492490593

theorem tailTrace_1570190 : CollatzResearch.WordTrace tailWord_1570190 prefixEnd_1570190 358338750614807492490593 := by
  unfold tailWord_1570190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7158691772684658993404503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38179689454318181298157349 7158691772684658993404503)
  ·
    refine ⟨10738037659026988490106755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7158691772684658993404503 10738037659026988490106755)
    ·
      refine ⟨16107056488540482735160133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10738037659026988490106755 16107056488540482735160133)
      ·
        refine ⟨3020073091601340512842525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16107056488540482735160133 3020073091601340512842525)
        ·
          refine ⟨1132527409350502692315947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3020073091601340512842525 1132527409350502692315947)
          ·
            refine ⟨1698791114025754038473921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132527409350502692315947 1698791114025754038473921)
            ·
              refine ⟨1274093335519315528855441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698791114025754038473921 1274093335519315528855441)
              ·
                refine ⟨955570001639486646641581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274093335519315528855441 955570001639486646641581)
                ·
                  refine ⟨358338750614807492490593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955570001639486646641581 358338750614807492490593)
                  ·
                    rfl

theorem cell21_1570190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_1570190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570190 prefixEnd_1570190 := by exact prefixLift 1570190
  have htrace : WordTrace (prefixWord ++ tailWord_1570190) baseStart_1570190 baseEnd_1570190 := by
    simpa [prefixWord, tailWord_1570190, baseEnd_1570190] using wordTrace_append hprefix tailTrace_1570190
  have hstable : (prefixWord ++ tailWord_1570190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570190).length < 2 ^ (prefixWord ++ tailWord_1570190).sum := by decide
  have hdescent : baseEnd_1570190 < baseStart_1570190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570308 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 5]
def baseStart_1570308 : Nat := 118140960795 + 1570308 * 2 ^ 59
def prefixEnd_1570308 : Nat := 4983230072969 + 3 ^ 40 * 1570308 * 2
def baseEnd_1570308 : Nat := 358365679822465509523685

theorem tailTrace_1570308 : CollatzResearch.WordTrace tailWord_1570308 prefixEnd_1570308 358365679822465509523685 := by
  unfold tailWord_1570308
  simp only [CollatzResearch.WordTrace]
  refine ⟨28636918997524889050015789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38182558663366518733354385 28636918997524889050015789)
  ·
    refine ⟨10738844624071833393755921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28636918997524889050015789 10738844624071833393755921)
    ·
      refine ⟨8054133468053875045316941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10738844624071833393755921 8054133468053875045316941)
      ·
        refine ⟨3020300050520203141993853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8054133468053875045316941 3020300050520203141993853)
        ·
          refine ⟨1132612518945076178247695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3020300050520203141993853 1132612518945076178247695)
          ·
            refine ⟨1698918778417614267371543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132612518945076178247695 1698918778417614267371543)
            ·
              refine ⟨2548378167626421401057315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698918778417614267371543 2548378167626421401057315)
              ·
                refine ⟨3822567251439632101585973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2548378167626421401057315 3822567251439632101585973)
                ·
                  refine ⟨358365679822465509523685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3822567251439632101585973 358365679822465509523685)
                  ·
                    rfl

theorem cell21_1570308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_1570308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570308 prefixEnd_1570308 := by exact prefixLift 1570308
  have htrace : WordTrace (prefixWord ++ tailWord_1570308) baseStart_1570308 baseEnd_1570308 := by
    simpa [prefixWord, tailWord_1570308, baseEnd_1570308] using wordTrace_append hprefix tailTrace_1570308
  have hstable : (prefixWord ++ tailWord_1570308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570308).length < 2 ^ (prefixWord ++ tailWord_1570308).sum := by decide
  have hdescent : baseEnd_1570308 < baseStart_1570308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570333 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1570333 : Nat := 118140960795 + 1570333 * 2 ^ 59
def prefixEnd_1570333 : Nat := 4983230072969 + 3 ^ 40 * 1570333 * 2
def baseEnd_1570333 : Nat := 358371385163071021606967

theorem tailTrace_1570333 : CollatzResearch.WordTrace tailWord_1570333 prefixEnd_1570333 358371385163071021606967 := by
  unfold tailWord_1570333
  simp only [CollatzResearch.WordTrace]
  refine ⟨57274749819959207369691653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38183166546639471579794435 57274749819959207369691653)
  ·
    refine ⟨10739015591242351381817185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57274749819959207369691653 10739015591242351381817185)
    ·
      refine ⟨8054261693431763536362889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10739015591242351381817185 8054261693431763536362889)
      ·
        refine ⟨6040696270073822652272167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8054261693431763536362889 6040696270073822652272167)
        ·
          refine ⟨9061044405110733978408251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040696270073822652272167 9061044405110733978408251)
          ·
            refine ⟨13591566607666100967612377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9061044405110733978408251 13591566607666100967612377)
            ·
              refine ⟨10193674955749575725709283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13591566607666100967612377 10193674955749575725709283)
              ·
                refine ⟨15290512433624363588563925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10193674955749575725709283 15290512433624363588563925)
                ·
                  refine ⟨358371385163071021606967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15290512433624363588563925 358371385163071021606967)
                  ·
                    rfl

theorem cell21_1570333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1570333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570333 prefixEnd_1570333 := by exact prefixLift 1570333
  have htrace : WordTrace (prefixWord ++ tailWord_1570333) baseStart_1570333 baseEnd_1570333 := by
    simpa [prefixWord, tailWord_1570333, baseEnd_1570333] using wordTrace_append hprefix tailTrace_1570333
  have hstable : (prefixWord ++ tailWord_1570333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570333).length < 2 ^ (prefixWord ++ tailWord_1570333).sum := by decide
  have hdescent : baseEnd_1570333 < baseStart_1570333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570367 : List Nat := [1, 1, 2, 2, 3, 3, 4, 2, 3]
def baseStart_1570367 : Nat := 118140960795 + 1570367 * 2 ^ 59
def prefixEnd_1570367 : Nat := 4983230072969 + 3 ^ 40 * 1570367 * 2
def baseEnd_1570367 : Nat := 358379144426294518040231

theorem tailTrace_1570367 : CollatzResearch.WordTrace tailWord_1570367 prefixEnd_1570367 358379144426294518040231 := by
  unfold tailWord_1570367
  simp only [CollatzResearch.WordTrace]
  refine ⟨57275989901836031176429355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38183993267890687450952903 57275989901836031176429355)
  ·
    refine ⟨85913984852754046764644033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57275989901836031176429355 85913984852754046764644033)
    ·
      refine ⟨64435488639565535073483025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85913984852754046764644033 64435488639565535073483025)
      ·
        refine ⟨48326616479674151305112269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64435488639565535073483025 48326616479674151305112269)
        ·
          refine ⟨18122481179877806739417101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48326616479674151305112269 18122481179877806739417101)
          ·
            refine ⟨6795930442454177527281413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18122481179877806739417101 6795930442454177527281413)
            ·
              refine ⟨1274236957960158286365265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6795930442454177527281413 1274236957960158286365265)
              ·
                refine ⟨955677718470118714773949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274236957960158286365265 955677718470118714773949)
                ·
                  refine ⟨358379144426294518040231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955677718470118714773949 358379144426294518040231)
                  ·
                    rfl

theorem cell21_1570367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 3].length) (baseStart_1570367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570367 prefixEnd_1570367 := by exact prefixLift 1570367
  have htrace : WordTrace (prefixWord ++ tailWord_1570367) baseStart_1570367 baseEnd_1570367 := by
    simpa [prefixWord, tailWord_1570367, baseEnd_1570367] using wordTrace_append hprefix tailTrace_1570367
  have hstable : (prefixWord ++ tailWord_1570367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570367).length < 2 ^ (prefixWord ++ tailWord_1570367).sum := by decide
  have hdescent : baseEnd_1570367 < baseStart_1570367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570460 : List Nat := [2, 2, 3, 2, 3, 2, 1, 3, 3]
def baseStart_1570460 : Nat := 118140960795 + 1570460 * 2 ^ 59
def prefixEnd_1570460 : Nat := 4983230072969 + 3 ^ 40 * 1570460 * 2
def baseEnd_1570460 : Nat := 358400368293347022990041

theorem tailTrace_1570460 : CollatzResearch.WordTrace tailWord_1570460 prefixEnd_1570460 358400368293347022990041 := by
  unfold tailWord_1570460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28639690945249554029782417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38186254593666072039709889 28639690945249554029782417)
  ·
    refine ⟨21479768208937165522336813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28639690945249554029782417 21479768208937165522336813)
    ·
      refine ⟨8054913078351437070876305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21479768208937165522336813 8054913078351437070876305)
      ·
        refine ⟨6041184808763577803157229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8054913078351437070876305 6041184808763577803157229)
        ·
          refine ⟨2265444303286341676183961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6041184808763577803157229 2265444303286341676183961)
          ·
            refine ⟨1699083227464756257137971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2265444303286341676183961 1699083227464756257137971)
            ·
              refine ⟨2548624841197134385706957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699083227464756257137971 2548624841197134385706957)
              ·
                refine ⟨955734315448925394640109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2548624841197134385706957 955734315448925394640109)
                ·
                  refine ⟨358400368293347022990041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955734315448925394640109 358400368293347022990041)
                  ·
                    rfl

theorem cell21_1570460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_1570460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570460 prefixEnd_1570460 := by exact prefixLift 1570460
  have htrace : WordTrace (prefixWord ++ tailWord_1570460) baseStart_1570460 baseEnd_1570460 := by
    simpa [prefixWord, tailWord_1570460, baseEnd_1570460] using wordTrace_append hprefix tailTrace_1570460
  have hstable : (prefixWord ++ tailWord_1570460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570460).length < 2 ^ (prefixWord ++ tailWord_1570460).sum := by decide
  have hdescent : baseEnd_1570460 < baseStart_1570460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570536 : List Nat := [2, 1, 4, 1, 3, 3, 2, 2, 3]
def baseStart_1570536 : Nat := 118140960795 + 1570536 * 2 ^ 59
def prefixEnd_1570536 : Nat := 4983230072969 + 3 ^ 40 * 1570536 * 2
def baseEnd_1570536 : Nat := 358417712528787779723219

theorem tailTrace_1570536 : CollatzResearch.WordTrace tailWord_1570536 prefixEnd_1570536 358417712528787779723219 := by
  unfold tailWord_1570536
  simp only [CollatzResearch.WordTrace]
  refine ⟨28641076919111886519665731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38188102558815848692887641 28641076919111886519665731)
  ·
    refine ⟨42961615378667829779498597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28641076919111886519665731 42961615378667829779498597)
    ·
      refine ⟨8055302883500218083655987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42961615378667829779498597 8055302883500218083655987)
      ·
        refine ⟨12082954325250327125483981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8055302883500218083655987 12082954325250327125483981)
        ·
          refine ⟨4531107871968872672056493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12082954325250327125483981 4531107871968872672056493)
          ·
            refine ⟨1699165451988327252021185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4531107871968872672056493 1699165451988327252021185)
            ·
              refine ⟨1274374088991245439015889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1699165451988327252021185 1274374088991245439015889)
              ·
                refine ⟨955780566743434079261917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274374088991245439015889 955780566743434079261917)
                ·
                  refine ⟨358417712528787779723219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955780566743434079261917 358417712528787779723219)
                  ·
                    rfl

theorem cell21_1570536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_1570536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570536 prefixEnd_1570536 := by exact prefixLift 1570536
  have htrace : WordTrace (prefixWord ++ tailWord_1570536) baseStart_1570536 baseEnd_1570536 := by
    simpa [prefixWord, tailWord_1570536, baseEnd_1570536] using wordTrace_append hprefix tailTrace_1570536
  have hstable : (prefixWord ++ tailWord_1570536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570536).length < 2 ^ (prefixWord ++ tailWord_1570536).sum := by decide
  have hdescent : baseEnd_1570536 < baseStart_1570536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570609 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 4]
def baseStart_1570609 : Nat := 118140960795 + 1570609 * 2 ^ 59
def prefixEnd_1570609 : Nat := 4983230072969 + 3 ^ 40 * 1570609 * 2
def baseEnd_1570609 : Nat := 358434372123355875006403

theorem tailTrace_1570609 : CollatzResearch.WordTrace tailWord_1570609 prefixEnd_1570609 358434372123355875006403 := by
  unfold tailWord_1570609
  simp only [CollatzResearch.WordTrace]
  refine ⟨57284816366959306506738881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38189877577972871004492587 57284816366959306506738881)
  ·
    refine ⟨42963612275219479880054161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57284816366959306506738881 42963612275219479880054161)
    ·
      refine ⟨32222709206414609910040621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42963612275219479880054161 32222709206414609910040621)
      ·
        refine ⟨12083515952405478716265233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32222709206414609910040621 12083515952405478716265233)
        ·
          refine ⟨9062636964304109037198925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12083515952405478716265233 9062636964304109037198925)
          ·
            refine ⟨3398488861614040888949597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9062636964304109037198925 3398488861614040888949597)
            ·
              refine ⟨1274433323105265333356099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3398488861614040888949597 1274433323105265333356099)
              ·
                refine ⟨1911649984657898000034149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274433323105265333356099 1911649984657898000034149)
                ·
                  refine ⟨358434372123355875006403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911649984657898000034149 358434372123355875006403)
                  ·
                    rfl

theorem cell21_1570609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_1570609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570609 prefixEnd_1570609 := by exact prefixLift 1570609
  have htrace : WordTrace (prefixWord ++ tailWord_1570609) baseStart_1570609 baseEnd_1570609 := by
    simpa [prefixWord, tailWord_1570609, baseEnd_1570609] using wordTrace_append hprefix tailTrace_1570609
  have hstable : (prefixWord ++ tailWord_1570609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570609).length < 2 ^ (prefixWord ++ tailWord_1570609).sum := by decide
  have hdescent : baseEnd_1570609 < baseStart_1570609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570668 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_1570668 : Nat := 118140960795 + 1570668 * 2 ^ 59
def prefixEnd_1570668 : Nat := 4983230072969 + 3 ^ 40 * 1570668 * 2
def baseEnd_1570668 : Nat := 358447836727184883522949

theorem tailTrace_1570668 : CollatzResearch.WordTrace tailWord_1570668 prefixEnd_1570668 358447836727184883522949 := by
  unfold tailWord_1570668
  simp only [CollatzResearch.WordTrace]
  refine ⟨28643484136872779791568329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38191312182497039722091105 28643484136872779791568329)
  ·
    refine ⟨21482613102654584843676247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28643484136872779791568329 21482613102654584843676247)
    ·
      refine ⟨32223919653981877265514371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21482613102654584843676247 32223919653981877265514371)
      ·
        refine ⟨48335879480972815898271557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32223919653981877265514371 48335879480972815898271557)
        ·
          refine ⟨9062977402682402980925917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48335879480972815898271557 9062977402682402980925917)
          ·
            refine ⟨3398616526005901117847219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9062977402682402980925917 3398616526005901117847219)
            ·
              refine ⟨5097924789008851676770829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398616526005901117847219 5097924789008851676770829)
              ·
                refine ⟨1911721795878319378789061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5097924789008851676770829 1911721795878319378789061)
                ·
                  refine ⟨358447836727184883522949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911721795878319378789061 358447836727184883522949)
                  ·
                    rfl

theorem cell21_1570668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_1570668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570668 prefixEnd_1570668 := by exact prefixLift 1570668
  have htrace : WordTrace (prefixWord ++ tailWord_1570668) baseStart_1570668 baseEnd_1570668 := by
    simpa [prefixWord, tailWord_1570668, baseEnd_1570668] using wordTrace_append hprefix tailTrace_1570668
  have hstable : (prefixWord ++ tailWord_1570668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570668).length < 2 ^ (prefixWord ++ tailWord_1570668).sum := by decide
  have hdescent : baseEnd_1570668 < baseStart_1570668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570702 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1570702 : Nat := 118140960795 + 1570702 * 2 ^ 59
def prefixEnd_1570702 : Nat := 4983230072969 + 3 ^ 40 * 1570702 * 2
def baseEnd_1570702 : Nat := 358455595990408379956213

theorem tailTrace_1570702 : CollatzResearch.WordTrace tailWord_1570702 prefixEnd_1570702 358455595990408379956213 := by
  unfold tailWord_1570702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161026044452797923734295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38192138903748255593249573 7161026044452797923734295)
  ·
    refine ⟨10741539066679196885601443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7161026044452797923734295 10741539066679196885601443)
    ·
      refine ⟨16112308600018795328402165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10741539066679196885601443 16112308600018795328402165)
      ·
        refine ⟨1510528931251762062037703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16112308600018795328402165 1510528931251762062037703)
        ·
          refine ⟨2265793396877643093056555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510528931251762062037703 2265793396877643093056555)
          ·
            refine ⟨3398690095316464639584833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265793396877643093056555 3398690095316464639584833)
            ·
              refine ⟨2549017571487348479688625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398690095316464639584833 2549017571487348479688625)
              ·
                refine ⟨1911763178615511359766469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549017571487348479688625 1911763178615511359766469)
                ·
                  refine ⟨358455595990408379956213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911763178615511359766469 358455595990408379956213)
                  ·
                    rfl

theorem cell21_1570702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1570702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570702 prefixEnd_1570702 := by exact prefixLift 1570702
  have htrace : WordTrace (prefixWord ++ tailWord_1570702) baseStart_1570702 baseEnd_1570702 := by
    simpa [prefixWord, tailWord_1570702, baseEnd_1570702] using wordTrace_append hprefix tailTrace_1570702
  have hstable : (prefixWord ++ tailWord_1570702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570702).length < 2 ^ (prefixWord ++ tailWord_1570702).sum := by decide
  have hdescent : baseEnd_1570702 < baseStart_1570702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570823 : List Nat := [1, 1, 4, 3, 1, 3, 3, 2, 3]
def baseStart_1570823 : Nat := 118140960795 + 1570823 * 2 ^ 59
def prefixEnd_1570823 : Nat := 4983230072969 + 3 ^ 40 * 1570823 * 2
def baseEnd_1570823 : Nat := 358483209838939058439299

theorem tailTrace_1570823 : CollatzResearch.WordTrace tailWord_1570823 prefixEnd_1570823 358483209838939058439299 := by
  unfold tailWord_1570823
  simp only [CollatzResearch.WordTrace]
  refine ⟨57292621588184021055029123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38195081058789347370019415 57292621588184021055029123)
  ·
    refine ⟨85938932382276031582543685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57292621588184021055029123 85938932382276031582543685)
    ·
      refine ⟨16113549821676755921726941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85938932382276031582543685 16113549821676755921726941)
      ·
        refine ⟨6042581183128783470647603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16113549821676755921726941 6042581183128783470647603)
        ·
          refine ⟨9063871774693175205971405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042581183128783470647603 9063871774693175205971405)
          ·
            refine ⟨3398951915509940702239277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9063871774693175205971405 3398951915509940702239277)
            ·
              refine ⟨1274606968316227763339729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3398951915509940702239277 1274606968316227763339729)
              ·
                refine ⟨955955226237170822504797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274606968316227763339729 955955226237170822504797)
                ·
                  refine ⟨358483209838939058439299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955955226237170822504797 358483209838939058439299)
                  ·
                    rfl

theorem cell21_1570823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 3].length) (baseStart_1570823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570823 prefixEnd_1570823 := by exact prefixLift 1570823
  have htrace : WordTrace (prefixWord ++ tailWord_1570823) baseStart_1570823 baseEnd_1570823 := by
    simpa [prefixWord, tailWord_1570823, baseEnd_1570823] using wordTrace_append hprefix tailTrace_1570823
  have hstable : (prefixWord ++ tailWord_1570823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570823).length < 2 ^ (prefixWord ++ tailWord_1570823).sum := by decide
  have hdescent : baseEnd_1570823 < baseStart_1570823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570829 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1570829 : Nat := 118140960795 + 1570829 * 2 ^ 59
def prefixEnd_1570829 : Nat := 4983230072969 + 3 ^ 40 * 1570829 * 2
def baseEnd_1570829 : Nat := 358484579120684381339287

theorem tailTrace_1570829 : CollatzResearch.WordTrace tailWord_1570829 prefixEnd_1570829 358484579120684381339287 := by
  unfold tailWord_1570829
  simp only [CollatzResearch.WordTrace]
  refine ⟨57292840426162284079747541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38195226950774856053165027 57292840426162284079747541)
  ·
    refine ⟨1342800947488178533119083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 57292840426162284079747541 1342800947488178533119083)
    ·
      refine ⟨2014201421232267799678625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1342800947488178533119083 2014201421232267799678625)
      ·
        refine ⟨1510651065924200849758969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2014201421232267799678625 1510651065924200849758969)
        ·
          refine ⟨1132988299443150637319227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1510651065924200849758969 1132988299443150637319227)
          ·
            refine ⟨1699482449164725955978841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132988299443150637319227 1699482449164725955978841)
            ·
              refine ⟨1274611836873544466984131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1699482449164725955978841 1274611836873544466984131)
              ·
                refine ⟨1911917755310316700476197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274611836873544466984131 1911917755310316700476197)
                ·
                  refine ⟨358484579120684381339287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911917755310316700476197 358484579120684381339287)
                  ·
                    rfl

theorem cell21_1570829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1570829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570829 prefixEnd_1570829 := by exact prefixLift 1570829
  have htrace : WordTrace (prefixWord ++ tailWord_1570829) baseStart_1570829 baseEnd_1570829 := by
    simpa [prefixWord, tailWord_1570829, baseEnd_1570829] using wordTrace_append hprefix tailTrace_1570829
  have hstable : (prefixWord ++ tailWord_1570829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570829).length < 2 ^ (prefixWord ++ tailWord_1570829).sum := by decide
  have hdescent : baseEnd_1570829 < baseStart_1570829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570879 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 4]
def baseStart_1570879 : Nat := 118140960795 + 1570879 * 2 ^ 59
def prefixEnd_1570879 : Nat := 4983230072969 + 3 ^ 40 * 1570879 * 2
def baseEnd_1570879 : Nat := 358495989801895405505851

theorem tailTrace_1570879 : CollatzResearch.WordTrace tailWord_1570879 prefixEnd_1570879 358495989801895405505851 := by
  unfold tailWord_1570879
  simp only [CollatzResearch.WordTrace]
  refine ⟨57294664075981142619067691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38196442717320761746045127 57294664075981142619067691)
  ·
    refine ⟨85941996113971713928601537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57294664075981142619067691 85941996113971713928601537)
    ·
      refine ⟨64456497085478785446451153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85941996113971713928601537 64456497085478785446451153)
      ·
        refine ⟨48342372814109089084838365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64456497085478785446451153 48342372814109089084838365)
        ·
          refine ⟨18128389805290908406814387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48342372814109089084838365 18128389805290908406814387)
          ·
            refine ⟨27192584707936362610221581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18128389805290908406814387 27192584707936362610221581)
            ·
              refine ⟨10197219265476135978833093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27192584707936362610221581 10197219265476135978833093)
              ·
                refine ⟨1911978612276775496031205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10197219265476135978833093 1911978612276775496031205)
                ·
                  refine ⟨358495989801895405505851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1911978612276775496031205 358495989801895405505851)
                  ·
                    rfl

theorem cell21_1570879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 4].length) (baseStart_1570879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570879 prefixEnd_1570879 := by exact prefixLift 1570879
  have htrace : WordTrace (prefixWord ++ tailWord_1570879) baseStart_1570879 baseEnd_1570879 := by
    simpa [prefixWord, tailWord_1570879, baseEnd_1570879] using wordTrace_append hprefix tailTrace_1570879
  have hstable : (prefixWord ++ tailWord_1570879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570879).length < 2 ^ (prefixWord ++ tailWord_1570879).sum := by decide
  have hdescent : baseEnd_1570879 < baseStart_1570879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570941 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1570941 : Nat := 118140960795 + 1570941 * 2 ^ 59
def prefixEnd_1570941 : Nat := 4983230072969 + 3 ^ 40 * 1570941 * 2
def baseEnd_1570941 : Nat := 358510139046597075472391

theorem tailTrace_1570941 : CollatzResearch.WordTrace tailWord_1570941 prefixEnd_1570941 358510139046597075472391 := by
  unfold tailWord_1570941
  simp only [CollatzResearch.WordTrace]
  refine ⟨57296925401756527207824677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38197950267837684805216451 57296925401756527207824677)
  ·
    refine ⟨10743173512829348851467127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57296925401756527207824677 10743173512829348851467127)
    ·
      refine ⟨16114760269244023277200691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10743173512829348851467127 16114760269244023277200691)
      ·
        refine ⟨24172140403866034915801037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16114760269244023277200691 24172140403866034915801037)
        ·
          refine ⟨9064552651449763093425389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24172140403866034915801037 9064552651449763093425389)
          ·
            refine ⟨3399207244293661160034521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9064552651449763093425389 3399207244293661160034521)
            ·
              refine ⟨2549405433220245870025891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399207244293661160034521 2549405433220245870025891)
              ·
                refine ⟨3824108149830368805038837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549405433220245870025891 3824108149830368805038837)
                ·
                  refine ⟨358510139046597075472391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3824108149830368805038837 358510139046597075472391)
                  ·
                    rfl

theorem cell21_1570941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1570941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570941 prefixEnd_1570941 := by exact prefixLift 1570941
  have htrace : WordTrace (prefixWord ++ tailWord_1570941) baseStart_1570941 baseEnd_1570941 := by
    simpa [prefixWord, tailWord_1570941, baseEnd_1570941] using wordTrace_append hprefix tailTrace_1570941
  have hstable : (prefixWord ++ tailWord_1570941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570941).length < 2 ^ (prefixWord ++ tailWord_1570941).sum := by decide
  have hdescent : baseEnd_1570941 < baseStart_1570941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570975 : List Nat := [1, 1, 2, 6, 1, 3, 1, 3, 3]
def baseStart_1570975 : Nat := 118140960795 + 1570975 * 2 ^ 59
def prefixEnd_1570975 : Nat := 4983230072969 + 3 ^ 40 * 1570975 * 2
def baseEnd_1570975 : Nat := 358517898309820571905655

theorem tailTrace_1570975 : CollatzResearch.WordTrace tailWord_1570975 prefixEnd_1570975 358517898309820571905655 := by
  unfold tailWord_1570975
  simp only [CollatzResearch.WordTrace]
  refine ⟨57298165483633351014562379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38198776989088900676374919 57298165483633351014562379)
  ·
    refine ⟨85947248225450026521843569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57298165483633351014562379 85947248225450026521843569)
    ·
      refine ⟨64460436169087519891382677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85947248225450026521843569 64460436169087519891382677)
      ·
        refine ⟨3021582945425977494908563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64460436169087519891382677 3021582945425977494908563)
        ·
          refine ⟨4532374418138966242362845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3021582945425977494908563 4532374418138966242362845)
          ·
            refine ⟨1699640406802112340886067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4532374418138966242362845 1699640406802112340886067)
            ·
              refine ⟨2549460610203168511329101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699640406802112340886067 2549460610203168511329101)
              ·
                refine ⟨956047728826188191748413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2549460610203168511329101 956047728826188191748413)
                ·
                  refine ⟨358517898309820571905655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956047728826188191748413 358517898309820571905655)
                  ·
                    rfl

theorem cell21_1570975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 3].length) (baseStart_1570975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1570975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1570975 prefixEnd_1570975 := by exact prefixLift 1570975
  have htrace : WordTrace (prefixWord ++ tailWord_1570975) baseStart_1570975 baseEnd_1570975 := by
    simpa [prefixWord, tailWord_1570975, baseEnd_1570975] using wordTrace_append hprefix tailTrace_1570975
  have hstable : (prefixWord ++ tailWord_1570975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570975).length < 2 ^ (prefixWord ++ tailWord_1570975).sum := by decide
  have hdescent : baseEnd_1570975 < baseStart_1570975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571006 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_1571006 : Nat := 118140960795 + 1571006 * 2 ^ 59
def prefixEnd_1571006 : Nat := 4983230072969 + 3 ^ 40 * 1571006 * 2
def baseEnd_1571006 : Nat := 358524972932171406888925

theorem tailTrace_1571006 : CollatzResearch.WordTrace tailWord_1571006 prefixEnd_1571006 358524972932171406888925 := by
  unfold tailWord_1571006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7162412018315130413617609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38199530764347362205960581 7162412018315130413617609)
  ·
    refine ⟨5371809013736347810213207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7162412018315130413617609 5371809013736347810213207)
    ·
      refine ⟨8057713520604521715319811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5371809013736347810213207 8057713520604521715319811)
      ·
        refine ⟨12086570280906782572979717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8057713520604521715319811 12086570280906782572979717)
        ·
          refine ⟨2266231927670021732433697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12086570280906782572979717 2266231927670021732433697)
          ·
            refine ⟨1699673945752516299325273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2266231927670021732433697 1699673945752516299325273)
            ·
              refine ⟨1274755459314387224493955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1699673945752516299325273 1274755459314387224493955)
              ·
                refine ⟨1912133188971580836740933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274755459314387224493955 1912133188971580836740933)
                ·
                  refine ⟨358524972932171406888925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912133188971580836740933 358524972932171406888925)
                  ·
                    rfl

theorem cell21_1571006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_1571006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571006 prefixEnd_1571006 := by exact prefixLift 1571006
  have htrace : WordTrace (prefixWord ++ tailWord_1571006) baseStart_1571006 baseEnd_1571006 := by
    simpa [prefixWord, tailWord_1571006, baseEnd_1571006] using wordTrace_append hprefix tailTrace_1571006
  have hstable : (prefixWord ++ tailWord_1571006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571006).length < 2 ^ (prefixWord ++ tailWord_1571006).sum := by decide
  have hdescent : baseEnd_1571006 < baseStart_1571006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571045 : List Nat := [1, 3, 1, 4, 2, 10]
def baseStart_1571045 : Nat := 118140960795 + 1571045 * 2 ^ 59
def prefixEnd_1571045 : Nat := 4983230072969 + 3 ^ 40 * 1571045 * 2
def baseEnd_1571045 : Nat := 13279032343093185397735

theorem tailTrace_1571045 : CollatzResearch.WordTrace tailWord_1571045 prefixEnd_1571045 13279032343093185397735 := by
  unfold tailWord_1571045
  simp only [CollatzResearch.WordTrace]
  refine ⟨57300718593379752969610589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38200479062253168646407059 57300718593379752969610589)
  ·
    refine ⟨21487769472517407363603971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57300718593379752969610589 21487769472517407363603971)
    ·
      refine ⟨32231654208776111045405957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21487769472517407363603971 32231654208776111045405957)
      ·
        refine ⟨6043435164145520821013617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32231654208776111045405957 6043435164145520821013617)
        ·
          refine ⟨4532576373109140615760213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6043435164145520821013617 4532576373109140615760213)
          ·
            refine ⟨13279032343093185397735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4532576373109140615760213 13279032343093185397735)
            ·
              rfl

theorem cell21_1571045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 10].length) (baseStart_1571045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571045 prefixEnd_1571045 := by exact prefixLift 1571045
  have htrace : WordTrace (prefixWord ++ tailWord_1571045) baseStart_1571045 baseEnd_1571045 := by
    simpa [prefixWord, tailWord_1571045, baseEnd_1571045] using wordTrace_append hprefix tailTrace_1571045
  have hstable : (prefixWord ++ tailWord_1571045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571045).length < 2 ^ (prefixWord ++ tailWord_1571045).sum := by decide
  have hdescent : baseEnd_1571045 < baseStart_1571045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571048 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_1571048 : Nat := 118140960795 + 1571048 * 2 ^ 59
def prefixEnd_1571048 : Nat := 4983230072969 + 3 ^ 40 * 1571048 * 2
def baseEnd_1571048 : Nat := 358534557904388667188839

theorem tailTrace_1571048 : CollatzResearch.WordTrace tailWord_1571048 prefixEnd_1571048 358534557904388667188839 := by
  unfold tailWord_1571048
  simp only [CollatzResearch.WordTrace]
  refine ⟨28650414006184442240984899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38200552008245922987979865 28650414006184442240984899)
  ·
    refine ⟨42975621009276663361477349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28650414006184442240984899 42975621009276663361477349)
    ·
      refine ⟨8057928939239374380277003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42975621009276663361477349 8057928939239374380277003)
      ·
        refine ⟨12086893408859061570415505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8057928939239374380277003 12086893408859061570415505)
        ·
          refine ⟨9065170056644296177811629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12086893408859061570415505 9065170056644296177811629)
          ·
            refine ⟨3399438771241611066679361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9065170056644296177811629 3399438771241611066679361)
            ·
              refine ⟨2549579078431208300009521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399438771241611066679361 2549579078431208300009521)
              ·
                refine ⟨1912184308823406225007141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549579078431208300009521 1912184308823406225007141)
                ·
                  refine ⟨358534557904388667188839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912184308823406225007141 358534557904388667188839)
                  ·
                    rfl

theorem cell21_1571048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_1571048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571048 prefixEnd_1571048 := by exact prefixLift 1571048
  have htrace : WordTrace (prefixWord ++ tailWord_1571048) baseStart_1571048 baseEnd_1571048 := by
    simpa [prefixWord, tailWord_1571048, baseEnd_1571048] using wordTrace_append hprefix tailTrace_1571048
  have hstable : (prefixWord ++ tailWord_1571048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571048).length < 2 ^ (prefixWord ++ tailWord_1571048).sum := by decide
  have hdescent : baseEnd_1571048 < baseStart_1571048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571062 : List Nat := [5, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1571062 : Nat := 118140960795 + 1571062 * 2 ^ 59
def prefixEnd_1571062 : Nat := 4983230072969 + 3 ^ 40 * 1571062 * 2
def baseEnd_1571062 : Nat := 119512584298375917985159

theorem tailTrace_1571062 : CollatzResearch.WordTrace tailWord_1571062 prefixEnd_1571062 119512584298375917985159 := by
  unfold tailWord_1571062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3581333664644885304561215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38200892422878776581986293 3581333664644885304561215)
  ·
    refine ⟨5372000496967327956841823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3581333664644885304561215 5372000496967327956841823)
    ·
      refine ⟨8058000745450991935262735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5372000496967327956841823 8058000745450991935262735)
      ·
        refine ⟨12087001118176487902894103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8058000745450991935262735 12087001118176487902894103)
        ·
          refine ⟨18130501677264731854341155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12087001118176487902894103 18130501677264731854341155)
          ·
            refine ⟨27195752515897097781511733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18130501677264731854341155 27195752515897097781511733)
            ·
              refine ⟨2549601798365352917016725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27195752515897097781511733 2549601798365352917016725)
              ·
                refine ⟨119512584298375917985159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2549601798365352917016725 119512584298375917985159)
                ·
                  rfl

theorem cell21_1571062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1571062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571062 prefixEnd_1571062 := by exact prefixLift 1571062
  have htrace : WordTrace (prefixWord ++ tailWord_1571062) baseStart_1571062 baseEnd_1571062 := by
    simpa [prefixWord, tailWord_1571062, baseEnd_1571062] using wordTrace_append hprefix tailTrace_1571062
  have hstable : (prefixWord ++ tailWord_1571062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571062).length < 2 ^ (prefixWord ++ tailWord_1571062).sum := by decide
  have hdescent : baseEnd_1571062 < baseStart_1571062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571093 : List Nat := [1, 3, 2, 1, 2, 1, 3, 5, 3]
def baseStart_1571093 : Nat := 118140960795 + 1571093 * 2 ^ 59
def prefixEnd_1571093 : Nat := 4983230072969 + 3 ^ 40 * 1571093 * 2
def baseEnd_1571093 : Nat := 358544827517478588938747

theorem tailTrace_1571093 : CollatzResearch.WordTrace tailWord_1571093 prefixEnd_1571093 358544827517478588938747 := by
  unfold tailWord_1571093
  simp only [CollatzResearch.WordTrace]
  refine ⟨57302469297205857167357933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38201646198137238111571955 57302469297205857167357933)
  ·
    refine ⟨21488425986452196437759225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57302469297205857167357933 21488425986452196437759225)
    ·
      refine ⟨16116319489839147328319419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21488425986452196437759225 16116319489839147328319419)
      ·
        refine ⟨24174479234758720992479129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16116319489839147328319419 24174479234758720992479129)
        ·
          refine ⟨18130859426069040744359347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24174479234758720992479129 18130859426069040744359347)
          ·
            refine ⟨27196289139103561116539021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18130859426069040744359347 27196289139103561116539021)
            ·
              refine ⟨10198608427163835418702133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27196289139103561116539021 10198608427163835418702133)
              ·
                refine ⟨956119540046609570503325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10198608427163835418702133 956119540046609570503325)
                ·
                  refine ⟨358544827517478588938747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956119540046609570503325 358544827517478588938747)
                  ·
                    rfl

theorem cell21_1571093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_1571093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571093 prefixEnd_1571093 := by exact prefixLift 1571093
  have htrace : WordTrace (prefixWord ++ tailWord_1571093) baseStart_1571093 baseEnd_1571093 := by
    simpa [prefixWord, tailWord_1571093, baseEnd_1571093] using wordTrace_append hprefix tailTrace_1571093
  have hstable : (prefixWord ++ tailWord_1571093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571093).length < 2 ^ (prefixWord ++ tailWord_1571093).sum := by decide
  have hdescent : baseEnd_1571093 < baseStart_1571093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571197 : List Nat := [1, 4, 1, 1, 2, 3, 2, 7]
def baseStart_1571197 : Nat := 118140960795 + 1571197 * 2 ^ 59
def prefixEnd_1571197 : Nat := 4983230072969 + 3 ^ 40 * 1571197 * 2
def baseEnd_1571197 : Nat := 119522853911465839735067

theorem tailTrace_1571197 : CollatzResearch.WordTrace tailWord_1571197 prefixEnd_1571197 119522853911465839735067 := by
  unfold tailWord_1571197
  simp only [CollatzResearch.WordTrace]
  refine ⟨57306262488829082929143845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38204174992552721952762563 57306262488829082929143845)
  ·
    refine ⟨10744924216655453049214471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57306262488829082929143845 10744924216655453049214471)
    ·
      refine ⟨16117386324983179573821707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10744924216655453049214471 16117386324983179573821707)
      ·
        refine ⟨24176079487474769360732561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16117386324983179573821707 24176079487474769360732561)
        ·
          refine ⟨18132059615606077020549421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24176079487474769360732561 18132059615606077020549421)
          ·
            refine ⟨6799522355852278882706033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18132059615606077020549421 6799522355852278882706033)
            ·
              refine ⟨5099641766889209162029525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6799522355852278882706033 5099641766889209162029525)
              ·
                refine ⟨119522853911465839735067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5099641766889209162029525 119522853911465839735067)
                ·
                  rfl

theorem cell21_1571197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 7].length) (baseStart_1571197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571197 prefixEnd_1571197 := by exact prefixLift 1571197
  have htrace : WordTrace (prefixWord ++ tailWord_1571197) baseStart_1571197 baseEnd_1571197 := by
    simpa [prefixWord, tailWord_1571197, baseEnd_1571197] using wordTrace_append hprefix tailTrace_1571197
  have hstable : (prefixWord ++ tailWord_1571197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571197).length < 2 ^ (prefixWord ++ tailWord_1571197).sum := by decide
  have hdescent : baseEnd_1571197 < baseStart_1571197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571220 : List Nat := [2, 4, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1571220 : Nat := 118140960795 + 1571220 * 2 ^ 59
def prefixEnd_1571220 : Nat := 4983230072969 + 3 ^ 40 * 1571220 * 2
def baseEnd_1571220 : Nat := 358573810647754590321821

theorem tailTrace_1571220 : CollatzResearch.WordTrace tailWord_1571220 prefixEnd_1571220 358573810647754590321821 := by
  unfold tailWord_1571220
  simp only [CollatzResearch.WordTrace]
  refine ⟨28653550683872878928615557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38204734245163838571487409 28653550683872878928615557)
  ·
    refine ⟨5372540753226164799115417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28653550683872878928615557 5372540753226164799115417)
    ·
      refine ⟨4029405564919623599336563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5372540753226164799115417 4029405564919623599336563)
      ·
        refine ⟨6044108347379435399004845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029405564919623599336563 6044108347379435399004845)
        ·
          refine ⟨2266540630267288274626817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6044108347379435399004845 2266540630267288274626817)
          ·
            refine ⟨1699905472700466205970113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2266540630267288274626817 1699905472700466205970113)
            ·
              refine ⟨1274929104525349654477585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1699905472700466205970113 1274929104525349654477585)
              ·
                refine ⟨956196828394012240858189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274929104525349654477585 956196828394012240858189)
                ·
                  refine ⟨358573810647754590321821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956196828394012240858189 358573810647754590321821)
                  ·
                    rfl

theorem cell21_1571220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1571220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571220 prefixEnd_1571220 := by exact prefixLift 1571220
  have htrace : WordTrace (prefixWord ++ tailWord_1571220) baseStart_1571220 baseEnd_1571220 := by
    simpa [prefixWord, tailWord_1571220, baseEnd_1571220] using wordTrace_append hprefix tailTrace_1571220
  have hstable : (prefixWord ++ tailWord_1571220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571220).length < 2 ^ (prefixWord ++ tailWord_1571220).sum := by decide
  have hdescent : baseEnd_1571220 < baseStart_1571220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571304 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_1571304 : Nat := 118140960795 + 1571304 * 2 ^ 59
def prefixEnd_1571304 : Nat := 4983230072969 + 3 ^ 40 * 1571304 * 2
def baseEnd_1571304 : Nat := 358592980592189110921649

theorem tailTrace_1571304 : CollatzResearch.WordTrace tailWord_1571304 prefixEnd_1571304 358592980592189110921649 := by
  unfold tailWord_1571304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28655082549720720101644483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38206776732960960135525977 28655082549720720101644483)
  ·
    refine ⟨42982623824581080152466725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28655082549720720101644483 42982623824581080152466725)
    ·
      refine ⟨8059241967108952528587511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42982623824581080152466725 8059241967108952528587511)
      ·
        refine ⟨12088862950663428792881267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8059241967108952528587511 12088862950663428792881267)
        ·
          refine ⟨18133294425995143189321901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088862950663428792881267 18133294425995143189321901)
          ·
            refine ⟨6799985409748178695995713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18133294425995143189321901 6799985409748178695995713)
            ·
              refine ⟨5099989057311134021996785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6799985409748178695995713 5099989057311134021996785)
              ·
                refine ⟨3824991792983350516497589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5099989057311134021996785 3824991792983350516497589)
                ·
                  refine ⟨358592980592189110921649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3824991792983350516497589 358592980592189110921649)
                  ·
                    rfl

theorem cell21_1571304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_1571304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571304 prefixEnd_1571304 := by exact prefixLift 1571304
  have htrace : WordTrace (prefixWord ++ tailWord_1571304) baseStart_1571304 baseEnd_1571304 := by
    simpa [prefixWord, tailWord_1571304, baseEnd_1571304] using wordTrace_append hprefix tailTrace_1571304
  have hstable : (prefixWord ++ tailWord_1571304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571304).length < 2 ^ (prefixWord ++ tailWord_1571304).sum := by decide
  have hdescent : baseEnd_1571304 < baseStart_1571304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571321 : List Nat := [1, 2, 1, 3, 1, 2, 5, 3, 3]
def baseStart_1571321 : Nat := 118140960795 + 1571321 * 2 ^ 59
def prefixEnd_1571321 : Nat := 4983230072969 + 3 ^ 40 * 1571321 * 2
def baseEnd_1571321 : Nat := 358596860223800859138281

theorem tailTrace_1571321 : CollatzResearch.WordTrace tailWord_1571321 prefixEnd_1571321 358596860223800859138281 := by
  unfold tailWord_1571321
  simp only [CollatzResearch.WordTrace]
  refine ⟨57310785140379852106657817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38207190093586568071105211 57310785140379852106657817)
  ·
    refine ⟨42983088855284889079993363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57310785140379852106657817 42983088855284889079993363)
    ·
      refine ⟨64474633282927333619990045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42983088855284889079993363 64474633282927333619990045)
      ·
        refine ⟨24177987481097750107496267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64474633282927333619990045 24177987481097750107496267)
        ·
          refine ⟨36266981221646625161244401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24177987481097750107496267 36266981221646625161244401)
          ·
            refine ⟨27200235916234968870933301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36266981221646625161244401 27200235916234968870933301)
            ·
              refine ⟨2550022117147028331649997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27200235916234968870933301 2550022117147028331649997)
              ·
                refine ⟨956258293930135624368749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2550022117147028331649997 956258293930135624368749)
                ·
                  refine ⟨358596860223800859138281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956258293930135624368749 358596860223800859138281)
                  ·
                    rfl

theorem cell21_1571321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_1571321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571321 prefixEnd_1571321 := by exact prefixLift 1571321
  have htrace : WordTrace (prefixWord ++ tailWord_1571321) baseStart_1571321 baseEnd_1571321 := by
    simpa [prefixWord, tailWord_1571321, baseEnd_1571321] using wordTrace_append hprefix tailTrace_1571321
  have hstable : (prefixWord ++ tailWord_1571321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571321).length < 2 ^ (prefixWord ++ tailWord_1571321).sum := by decide
  have hdescent : baseEnd_1571321 < baseStart_1571321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571338 : List Nat := [3, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_1571338 : Nat := 118140960795 + 1571338 * 2 ^ 59
def prefixEnd_1571338 : Nat := 4983230072969 + 3 ^ 40 * 1571338 * 2
def baseEnd_1571338 : Nat := 358600739855412607354913

theorem tailTrace_1571338 : CollatzResearch.WordTrace tailWord_1571338 prefixEnd_1571338 358600739855412607354913 := by
  unfold tailWord_1571338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14327851295329566002506667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38207603454212176006684445 14327851295329566002506667)
  ·
    refine ⟨21491776942994349003760001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14327851295329566002506667 21491776942994349003760001)
    ·
      refine ⟨16118832707245761752820001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21491776942994349003760001 16118832707245761752820001)
      ·
        refine ⟨12089124530434321314615001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16118832707245761752820001 12089124530434321314615001)
        ·
          refine ⟨9066843397825740985961251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12089124530434321314615001 9066843397825740985961251)
          ·
            refine ⟨13600265096738611478941877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9066843397825740985961251 13600265096738611478941877)
            ·
              refine ⟨1275024852819244826150801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13600265096738611478941877 1275024852819244826150801)
              ·
                refine ⟨956268639614433619613101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275024852819244826150801 956268639614433619613101)
                ·
                  refine ⟨358600739855412607354913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956268639614433619613101 358600739855412607354913)
                  ·
                    rfl

theorem cell21_1571338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_1571338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571338 prefixEnd_1571338 := by exact prefixLift 1571338
  have htrace : WordTrace (prefixWord ++ tailWord_1571338) baseStart_1571338 baseEnd_1571338 := by
    simpa [prefixWord, tailWord_1571338, baseEnd_1571338] using wordTrace_append hprefix tailTrace_1571338
  have hstable : (prefixWord ++ tailWord_1571338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571338).length < 2 ^ (prefixWord ++ tailWord_1571338).sum := by decide
  have hdescent : baseEnd_1571338 < baseStart_1571338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571349 : List Nat := [1, 3, 2, 1, 3, 1, 4, 6]
def baseStart_1571349 : Nat := 118140960795 + 1571349 * 2 ^ 59
def prefixEnd_1571349 : Nat := 4983230072969 + 3 ^ 40 * 1571349 * 2
def baseEnd_1571349 : Nat := 119534416735093010890519

theorem tailTrace_1571349 : CollatzResearch.WordTrace tailWord_1571349 prefixEnd_1571349 119534416735093010890519 := by
  unfold tailWord_1571349
  simp only [CollatzResearch.WordTrace]
  refine ⟨57311806384278412888677101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38207870922852275259118067 57311806384278412888677101)
  ·
    refine ⟨21491927394104404833253913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57311806384278412888677101 21491927394104404833253913)
    ·
      refine ⟨16118945545578303624940435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21491927394104404833253913 16118945545578303624940435)
      ·
        refine ⟨24178418318367455437410653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16118945545578303624940435 24178418318367455437410653)
        ·
          refine ⟨9066906869387795789028995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24178418318367455437410653 9066906869387795789028995)
          ·
            refine ⟨13600360304081693683543493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9066906869387795789028995 13600360304081693683543493)
            ·
              refine ⟨2550067557015317565664405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13600360304081693683543493 2550067557015317565664405)
              ·
                refine ⟨119534416735093010890519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2550067557015317565664405 119534416735093010890519)
                ·
                  rfl

theorem cell21_1571349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 6].length) (baseStart_1571349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571349 prefixEnd_1571349 := by exact prefixLift 1571349
  have htrace : WordTrace (prefixWord ++ tailWord_1571349) baseStart_1571349 baseEnd_1571349 := by
    simpa [prefixWord, tailWord_1571349, baseEnd_1571349] using wordTrace_append hprefix tailTrace_1571349
  have hstable : (prefixWord ++ tailWord_1571349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571349).length < 2 ^ (prefixWord ++ tailWord_1571349).sum := by decide
  have hdescent : baseEnd_1571349 < baseStart_1571349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571352 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_1571352 : Nat := 118140960795 + 1571352 * 2 ^ 59
def prefixEnd_1571352 : Nat := 4983230072969 + 3 ^ 40 * 1571352 * 2
def baseEnd_1571352 : Nat := 358603934846151694121551

theorem tailTrace_1571352 : CollatzResearch.WordTrace tailWord_1571352 prefixEnd_1571352 358603934846151694121551 := by
  unfold tailWord_1571352
  simp only [CollatzResearch.WordTrace]
  refine ⟨28655957901633772200518155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38207943868845029600690873 28655957901633772200518155)
  ·
    refine ⟨42983936852450658300777233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28655957901633772200518155 42983936852450658300777233)
    ·
      refine ⟨32237952639337993725582925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42983936852450658300777233 32237952639337993725582925)
      ·
        refine ⟨12089232239751747647093597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32237952639337993725582925 12089232239751747647093597)
        ·
          refine ⟨4533462089906905367660099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12089232239751747647093597 4533462089906905367660099)
          ·
            refine ⟨6800193134860358051490149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533462089906905367660099 6800193134860358051490149)
            ·
              refine ⟨1275036212786317134654403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6800193134860358051490149 1275036212786317134654403)
              ·
                refine ⟨1912554319179475701981605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275036212786317134654403 1912554319179475701981605)
                ·
                  refine ⟨358603934846151694121551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912554319179475701981605 358603934846151694121551)
                  ·
                    rfl

theorem cell21_1571352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_1571352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571352 prefixEnd_1571352 := by exact prefixLift 1571352
  have htrace : WordTrace (prefixWord ++ tailWord_1571352) baseStart_1571352 baseEnd_1571352 := by
    simpa [prefixWord, tailWord_1571352, baseEnd_1571352] using wordTrace_append hprefix tailTrace_1571352
  have hstable : (prefixWord ++ tailWord_1571352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571352).length < 2 ^ (prefixWord ++ tailWord_1571352).sum := by decide
  have hdescent : baseEnd_1571352 < baseStart_1571352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571397 : List Nat := [1, 3, 1, 1, 1, 6, 1, 4, 3]
def baseStart_1571397 : Nat := 118140960795 + 1571397 * 2 ^ 59
def prefixEnd_1571397 : Nat := 4983230072969 + 3 ^ 40 * 1571397 * 2
def baseEnd_1571397 : Nat := 358614204459241615871459

theorem tailTrace_1571397 : CollatzResearch.WordTrace tailWord_1571397 prefixEnd_1571397 358614204459241615871459 := by
  unfold tailWord_1571397
  simp only [CollatzResearch.WordTrace]
  refine ⟨57313557088104517086424445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38209038058736344724282963 57313557088104517086424445)
  ·
    refine ⟨21492583908039193907409167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57313557088104517086424445 21492583908039193907409167)
    ·
      refine ⟨32238875862058790861113751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21492583908039193907409167 32238875862058790861113751)
      ·
        refine ⟨48358313793088186291670627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32238875862058790861113751 48358313793088186291670627)
        ·
          refine ⟨72537470689632279437505941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48358313793088186291670627 72537470689632279437505941)
          ·
            refine ⟨3400193938576513098633091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72537470689632279437505941 3400193938576513098633091)
            ·
              refine ⟨5100290907864769647949637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400193938576513098633091 5100290907864769647949637)
              ·
                refine ⟨956304545224644308990557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5100290907864769647949637 956304545224644308990557)
                ·
                  refine ⟨358614204459241615871459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956304545224644308990557 358614204459241615871459)
                  ·
                    rfl

theorem cell21_1571397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_1571397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571397 prefixEnd_1571397 := by exact prefixLift 1571397
  have htrace : WordTrace (prefixWord ++ tailWord_1571397) baseStart_1571397 baseEnd_1571397 := by
    simpa [prefixWord, tailWord_1571397, baseEnd_1571397] using wordTrace_append hprefix tailTrace_1571397
  have hstable : (prefixWord ++ tailWord_1571397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571397).length < 2 ^ (prefixWord ++ tailWord_1571397).sum := by decide
  have hdescent : baseEnd_1571397 < baseStart_1571397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571408 : List Nat := [2, 1, 1, 1, 1, 3, 2, 10]
def baseStart_1571408 : Nat := 118140960795 + 1571408 * 2 ^ 59
def prefixEnd_1571408 : Nat := 4983230072969 + 3 ^ 40 * 1571408 * 2
def baseEnd_1571408 : Nat := 119538904936369347062701

theorem tailTrace_1571408 : CollatzResearch.WordTrace tailWord_1571408 prefixEnd_1571408 119538904936369347062701 := by
  unfold tailWord_1571408
  simp only [CollatzResearch.WordTrace]
  refine ⟨28656979145532332982537439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38209305527376443976716585 28656979145532332982537439)
  ·
    refine ⟨42985468718298499473806159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28656979145532332982537439 42985468718298499473806159)
    ·
      refine ⟨64478203077447749210709239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42985468718298499473806159 64478203077447749210709239)
      ·
        refine ⟨96717304616171623816063859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64478203077447749210709239 96717304616171623816063859)
        ·
          refine ⟨145075956924257435724095789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96717304616171623816063859 145075956924257435724095789)
          ·
            refine ⟨54403483846596538396535921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145075956924257435724095789 54403483846596538396535921)
            ·
              refine ⟨40802612884947403797401941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54403483846596538396535921 40802612884947403797401941)
              ·
                refine ⟨119538904936369347062701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40802612884947403797401941 119538904936369347062701)
                ·
                  rfl

theorem cell21_1571408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_1571408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571408 prefixEnd_1571408 := by exact prefixLift 1571408
  have htrace : WordTrace (prefixWord ++ tailWord_1571408) baseStart_1571408 baseEnd_1571408 := by
    simpa [prefixWord, tailWord_1571408, baseEnd_1571408] using wordTrace_append hprefix tailTrace_1571408
  have hstable : (prefixWord ++ tailWord_1571408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571408).length < 2 ^ (prefixWord ++ tailWord_1571408).sum := by decide
  have hdescent : baseEnd_1571408 < baseStart_1571408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571445 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 4]
def baseStart_1571445 : Nat := 118140960795 + 1571445 * 2 ^ 59
def prefixEnd_1571445 : Nat := 4983230072969 + 3 ^ 40 * 1571445 * 2
def baseEnd_1571445 : Nat := 358625158713204199071361

theorem tailTrace_1571445 : CollatzResearch.WordTrace tailWord_1571445 prefixEnd_1571445 358625158713204199071361 := by
  unfold tailWord_1571445
  simp only [CollatzResearch.WordTrace]
  refine ⟨57315307791930621284171789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38210205194620414189447859 57315307791930621284171789)
  ·
    refine ⟨21493240421973982981564421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57315307791930621284171789 21493240421973982981564421)
    ·
      refine ⟨4029982579120121809043329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21493240421973982981564421 4029982579120121809043329)
      ·
        refine ⟨3022486934340091356782497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4029982579120121809043329 3022486934340091356782497)
        ·
          refine ⟨2266865200755068517586873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3022486934340091356782497 2266865200755068517586873)
          ·
            refine ⟨1700148900566301388190155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2266865200755068517586873 1700148900566301388190155)
            ·
              refine ⟨2550223350849452082285233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700148900566301388190155 2550223350849452082285233)
              ·
                refine ⟨1912667513137089061713925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550223350849452082285233 1912667513137089061713925)
                ·
                  refine ⟨358625158713204199071361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912667513137089061713925 358625158713204199071361)
                  ·
                    rfl

theorem cell21_1571445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_1571445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571445 prefixEnd_1571445 := by exact prefixLift 1571445
  have htrace : WordTrace (prefixWord ++ tailWord_1571445) baseStart_1571445 baseEnd_1571445 := by
    simpa [prefixWord, tailWord_1571445, baseEnd_1571445] using wordTrace_append hprefix tailTrace_1571445
  have hstable : (prefixWord ++ tailWord_1571445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571445).length < 2 ^ (prefixWord ++ tailWord_1571445).sum := by decide
  have hdescent : baseEnd_1571445 < baseStart_1571445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571456 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_1571456 : Nat := 118140960795 + 1571456 * 2 ^ 59
def prefixEnd_1571456 : Nat := 4983230072969 + 3 ^ 40 * 1571456 * 2
def baseEnd_1571456 : Nat := 358627669063070624388005

theorem tailTrace_1571456 : CollatzResearch.WordTrace tailWord_1571456 prefixEnd_1571456 358627669063070624388005 := by
  unfold tailWord_1571456
  simp only [CollatzResearch.WordTrace]
  refine ⟨28657854497445385081411111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38210472663260513441881481 28657854497445385081411111)
  ·
    refine ⟨42986781746168077622116667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28657854497445385081411111 42986781746168077622116667)
    ·
      refine ⟨64480172619252116433175001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42986781746168077622116667 64480172619252116433175001)
      ·
        refine ⟨48360129464439087324881251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64480172619252116433175001 48360129464439087324881251)
        ·
          refine ⟨72540194196658630987321877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48360129464439087324881251 72540194196658630987321877)
          ·
            refine ⟨3400321602968373327530713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72540194196658630987321877 3400321602968373327530713)
            ·
              refine ⟨2550241202226279995648035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3400321602968373327530713 2550241202226279995648035)
              ·
                refine ⟨3825361803339419993472053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2550241202226279995648035 3825361803339419993472053)
                ·
                  refine ⟨358627669063070624388005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3825361803339419993472053 358627669063070624388005)
                  ·
                    rfl

theorem cell21_1571456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_1571456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571456 prefixEnd_1571456 := by exact prefixLift 1571456
  have htrace : WordTrace (prefixWord ++ tailWord_1571456) baseStart_1571456 baseEnd_1571456 := by
    simpa [prefixWord, tailWord_1571456, baseEnd_1571456] using wordTrace_append hprefix tailTrace_1571456
  have hstable : (prefixWord ++ tailWord_1571456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571456).length < 2 ^ (prefixWord ++ tailWord_1571456).sum := by decide
  have hdescent : baseEnd_1571456 < baseStart_1571456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571501 : List Nat := [1, 5, 2, 1, 1, 2, 9]
def baseStart_1571501 : Nat := 118140960795 + 1571501 * 2 ^ 59
def prefixEnd_1571501 : Nat := 4983230072969 + 3 ^ 40 * 1571501 * 2
def baseEnd_1571501 : Nat := 39848659852906727348657

theorem tailTrace_1571501 : CollatzResearch.WordTrace tailWord_1571501 prefixEnd_1571501 39848659852906727348657 := by
  unfold tailWord_1571501
  simp only [CollatzResearch.WordTrace]
  refine ⟨57317350279727742848210357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38211566853151828565473571 57317350279727742848210357)
  ·
    refine ⟨5373501588724475892019721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57317350279727742848210357 5373501588724475892019721)
    ·
      refine ⟨4030126191543356919014791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5373501588724475892019721 4030126191543356919014791)
      ·
        refine ⟨6045189287315035378522187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030126191543356919014791 6045189287315035378522187)
        ·
          refine ⟨9067783930972553067783281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045189287315035378522187 9067783930972553067783281)
          ·
            refine ⟨6800837948229414800837461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9067783930972553067783281 6800837948229414800837461)
            ·
              refine ⟨39848659852906727348657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6800837948229414800837461 39848659852906727348657)
              ·
                rfl

theorem cell21_1571501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 9].length) (baseStart_1571501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571501 prefixEnd_1571501 := by exact prefixLift 1571501
  have htrace : WordTrace (prefixWord ++ tailWord_1571501) baseStart_1571501 baseEnd_1571501 := by
    simpa [prefixWord, tailWord_1571501, baseEnd_1571501] using wordTrace_append hprefix tailTrace_1571501
  have hstable : (prefixWord ++ tailWord_1571501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571501).length < 2 ^ (prefixWord ++ tailWord_1571501).sum := by decide
  have hdescent : baseEnd_1571501 < baseStart_1571501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571521 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 4]
def baseStart_1571521 : Nat := 118140960795 + 1571521 * 2 ^ 59
def prefixEnd_1571521 : Nat := 4983230072969 + 3 ^ 40 * 1571521 * 2
def baseEnd_1571521 : Nat := 358642502948644955804539

theorem tailTrace_1571521 : CollatzResearch.WordTrace tailWord_1571521 prefixEnd_1571521 358642502948644955804539 := by
  unfold tailWord_1571521
  simp only [CollatzResearch.WordTrace]
  refine ⟨57318079739655286263938417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38212053159770190842625611 57318079739655286263938417)
  ·
    refine ⟨42988559804741464697953813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57318079739655286263938417 42988559804741464697953813)
    ·
      refine ⟨2015088740847256157716585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42988559804741464697953813 2015088740847256157716585)
      ·
        refine ⟨1511316555635442118287439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2015088740847256157716585 1511316555635442118287439)
        ·
          refine ⟨2266974833453163177431159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511316555635442118287439 2266974833453163177431159)
          ·
            refine ⟨3400462250179744766146739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266974833453163177431159 3400462250179744766146739)
            ·
              refine ⟨5100693375269617149220109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400462250179744766146739 5100693375269617149220109)
              ·
                refine ⟨1912760015726106430957541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5100693375269617149220109 1912760015726106430957541)
                ·
                  refine ⟨358642502948644955804539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912760015726106430957541 358642502948644955804539)
                  ·
                    rfl

theorem cell21_1571521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_1571521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571521 prefixEnd_1571521 := by exact prefixLift 1571521
  have htrace : WordTrace (prefixWord ++ tailWord_1571521) baseStart_1571521 baseEnd_1571521 := by
    simpa [prefixWord, tailWord_1571521, baseEnd_1571521] using wordTrace_append hprefix tailTrace_1571521
  have hstable : (prefixWord ++ tailWord_1571521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571521).length < 2 ^ (prefixWord ++ tailWord_1571521).sum := by decide
  have hdescent : baseEnd_1571521 < baseStart_1571521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571560 : List Nat := [2, 1, 4, 1, 13]
def baseStart_1571560 : Nat := 118140960795 + 1571560 * 2 ^ 59
def prefixEnd_1571560 : Nat := 4983230072969 + 3 ^ 40 * 1571560 * 2
def baseEnd_1571560 : Nat := 4427795102222093267339

theorem tailTrace_1571560 : CollatzResearch.WordTrace tailWord_1571560 prefixEnd_1571560 4427795102222093267339 := by
  unfold tailWord_1571560
  simp only [CollatzResearch.WordTrace]
  refine ⟨28659751093256997962304067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38213001457675997283072089 28659751093256997962304067)
  ·
    refine ⟨42989626639885496943456101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28659751093256997962304067 42989626639885496943456101)
    ·
      refine ⟨8060554994978530676898019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42989626639885496943456101 8060554994978530676898019)
      ·
        refine ⟨12090832492467796015347029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8060554994978530676898019 12090832492467796015347029)
        ·
          refine ⟨4427795102222093267339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12090832492467796015347029 4427795102222093267339)
          ·
            rfl

theorem cell21_1571560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 13].length) (baseStart_1571560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571560 prefixEnd_1571560 := by exact prefixLift 1571560
  have htrace : WordTrace (prefixWord ++ tailWord_1571560) baseStart_1571560 baseEnd_1571560 := by
    simpa [prefixWord, tailWord_1571560, baseEnd_1571560] using wordTrace_append hprefix tailTrace_1571560
  have hstable : (prefixWord ++ tailWord_1571560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571560).length < 2 ^ (prefixWord ++ tailWord_1571560).sum := by decide
  have hdescent : baseEnd_1571560 < baseStart_1571560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571566 : List Nat := [4, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_1571566 : Nat := 118140960795 + 1571566 * 2 ^ 59
def prefixEnd_1571566 : Nat := 4983230072969 + 3 ^ 40 * 1571566 * 2
def baseEnd_1571566 : Nat := 358652772561734877554447

theorem tailTrace_1571566 : CollatzResearch.WordTrace tailWord_1571566 prefixEnd_1571566 358652772561734877554447 := by
  unfold tailWord_1571566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164965128061532368665819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38213147349661505966217701 7164965128061532368665819)
  ·
    refine ⟨10747447692092298552998729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7164965128061532368665819 10747447692092298552998729)
    ·
      refine ⟨8060585769069223914749047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10747447692092298552998729 8060585769069223914749047)
      ·
        refine ⟨12090878653603835872123571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8060585769069223914749047 12090878653603835872123571)
        ·
          refine ⟨18136317980405753808185357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12090878653603835872123571 18136317980405753808185357)
          ·
            refine ⟨6801119242652157678069509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18136317980405753808185357 6801119242652157678069509)
            ·
              refine ⟨1275209857997279564638033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6801119242652157678069509 1275209857997279564638033)
              ·
                refine ⟨956407393497959673478525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275209857997279564638033 956407393497959673478525)
                ·
                  refine ⟨358652772561734877554447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956407393497959673478525 358652772561734877554447)
                  ·
                    rfl

theorem cell21_1571566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_1571566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571566 prefixEnd_1571566 := by exact prefixLift 1571566
  have htrace : WordTrace (prefixWord ++ tailWord_1571566) baseStart_1571566 baseEnd_1571566 := by
    simpa [prefixWord, tailWord_1571566, baseEnd_1571566] using wordTrace_append hprefix tailTrace_1571566
  have hstable : (prefixWord ++ tailWord_1571566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571566).length < 2 ^ (prefixWord ++ tailWord_1571566).sum := by decide
  have hdescent : baseEnd_1571566 < baseStart_1571566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
