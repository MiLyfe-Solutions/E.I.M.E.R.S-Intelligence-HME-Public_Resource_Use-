import V185TrunkScan20Chunk142

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_870429 : List Nat := [1, 4, 2, 2, 2, 1, 4, 4]
def baseStart_870429 : Nat := 118140960795 + 870429 * 2 ^ 59
def prefixEnd_870429 : Nat := 4983230072969 + 3 ^ 40 * 870429 * 2
def baseEnd_870429 : Nat := 132429171144438570736141

theorem tailTrace_870429 : CollatzResearch.WordTrace tailWord_870429 prefixEnd_870429 132429171144438570736141 := by
  unfold tailWord_870429
  simp only [CollatzResearch.WordTrace]
  refine ⟨31747153763591865283086341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21164769175727910188724227 31747153763591865283086341)
  ·
    refine ⟨5952591330673474740578689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31747153763591865283086341 5952591330673474740578689)
    ·
      refine ⟨4464443498005106055434017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5952591330673474740578689 4464443498005106055434017)
      ·
        refine ⟨3348332623503829541575513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4464443498005106055434017 3348332623503829541575513)
        ·
          refine ⟨2511249467627872156181635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348332623503829541575513 2511249467627872156181635)
          ·
            refine ⟨3766874201441808234272453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511249467627872156181635 3766874201441808234272453)
            ·
              refine ⟨706288912770339043926085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3766874201441808234272453 706288912770339043926085)
              ·
                refine ⟨132429171144438570736141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706288912770339043926085 132429171144438570736141)
                ·
                  rfl

theorem cell20_870429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 4].length) (baseStart_870429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870429 prefixEnd_870429 := by exact prefixLift 870429
  have htrace : WordTrace (prefixWord ++ tailWord_870429) baseStart_870429 baseEnd_870429 := by
    simpa [prefixWord, tailWord_870429, baseEnd_870429] using wordTrace_append hprefix tailTrace_870429
  have hstable : (prefixWord ++ tailWord_870429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870429).length < 2 ^ (prefixWord ++ tailWord_870429).sum := by decide
  have hdescent : baseEnd_870429 < baseStart_870429 := by decide
  rcases family_descends (prefixWord ++ tailWord_870429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870443 : List Nat := [1, 1, 1, 1, 2, 1, 4, 7, 2]
def baseStart_870443 : Nat := 118140960795 + 870443 * 2 ^ 59
def prefixEnd_870443 : Nat := 4983230072969 + 3 ^ 40 * 870443 * 2
def baseEnd_870443 : Nat := 397293903414793885741699

theorem tailTrace_870443 : CollatzResearch.WordTrace tailWord_870443 prefixEnd_870443 397293903414793885741699 := by
  unfold tailWord_870443
  simp only [CollatzResearch.WordTrace]
  refine ⟨31747664385541145674095983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21165109590360763782730655 31747664385541145674095983)
  ·
    refine ⟨47621496578311718511143975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31747664385541145674095983 47621496578311718511143975)
    ·
      refine ⟨71432244867467577766715963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47621496578311718511143975 71432244867467577766715963)
      ·
        refine ⟨107148367301201366650073945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71432244867467577766715963 107148367301201366650073945)
        ·
          refine ⟨80361275475901024987555459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107148367301201366650073945 80361275475901024987555459)
          ·
            refine ⟨120541913213851537481333189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80361275475901024987555459 120541913213851537481333189)
            ·
              refine ⟨22601608727597163277749973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120541913213851537481333189 22601608727597163277749973)
              ·
                refine ⟨529725204553058514322265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22601608727597163277749973 529725204553058514322265)
                ·
                  refine ⟨397293903414793885741699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529725204553058514322265 397293903414793885741699)
                  ·
                    rfl

theorem cell20_870443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 2].length) (baseStart_870443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870443 prefixEnd_870443 := by exact prefixLift 870443
  have htrace : WordTrace (prefixWord ++ tailWord_870443) baseStart_870443 baseEnd_870443 := by
    simpa [prefixWord, tailWord_870443, baseEnd_870443] using wordTrace_append hprefix tailTrace_870443
  have hstable : (prefixWord ++ tailWord_870443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870443).length < 2 ^ (prefixWord ++ tailWord_870443).sum := by decide
  have hdescent : baseEnd_870443 < baseStart_870443 := by decide
  rcases family_descends (prefixWord ++ tailWord_870443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870450 : List Nat := [3, 2, 1, 1, 2, 5, 6]
def baseStart_870450 : Nat := 118140960795 + 870450 * 2 ^ 59
def prefixEnd_870450 : Nat := 4983230072969 + 3 ^ 40 * 870450 * 2
def baseEnd_870450 : Nat := 44144122045059219167593

theorem tailTrace_870450 : CollatzResearch.WordTrace tailWord_870450 prefixEnd_870450 44144122045059219167593 := by
  unfold tailWord_870450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7936979924128946467400201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21165279797677190579733869 7936979924128946467400201)
  ·
    refine ⟨5952734943096709850550151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7936979924128946467400201 5952734943096709850550151)
    ·
      refine ⟨8929102414645064775825227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952734943096709850550151 8929102414645064775825227)
      ·
        refine ⟨13393653621967597163737841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8929102414645064775825227 13393653621967597163737841)
        ·
          refine ⟨10045240216475697872803381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13393653621967597163737841 10045240216475697872803381)
          ·
            refine ⟨941741270294596675575317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10045240216475697872803381 941741270294596675575317)
            ·
              refine ⟨44144122045059219167593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 941741270294596675575317 44144122045059219167593)
              ·
                rfl

theorem cell20_870450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 6].length) (baseStart_870450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870450 prefixEnd_870450 := by exact prefixLift 870450
  have htrace : WordTrace (prefixWord ++ tailWord_870450) baseStart_870450 baseEnd_870450 := by
    simpa [prefixWord, tailWord_870450, baseEnd_870450] using wordTrace_append hprefix tailTrace_870450
  have hstable : (prefixWord ++ tailWord_870450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870450).length < 2 ^ (prefixWord ++ tailWord_870450).sum := by decide
  have hdescent : baseEnd_870450 < baseStart_870450 := by decide
  rcases family_descends (prefixWord ++ tailWord_870450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870512 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_870512 : Nat := 118140960795 + 870512 * 2 ^ 59
def prefixEnd_870512 : Nat := 4983230072969 + 3 ^ 40 * 870512 * 2
def baseEnd_870512 : Nat := 397325396894936312441417

theorem tailTrace_870512 : CollatzResearch.WordTrace tailWord_870512 prefixEnd_870512 397325396894936312441417 := by
  unfold tailWord_870512
  simp only [CollatzResearch.WordTrace]
  refine ⟨15875090511145585229178895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21166787348194113638905193 15875090511145585229178895)
  ·
    refine ⟨23812635766718377843768343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15875090511145585229178895 23812635766718377843768343)
    ·
      refine ⟨35718953650077566765652515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23812635766718377843768343 35718953650077566765652515)
      ·
        refine ⟨53578430475116350148478773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35718953650077566765652515 53578430475116350148478773)
        ·
          refine ⟨5022977857042157826419885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53578430475116350148478773 5022977857042157826419885)
          ·
            refine ⟨1883616696390809184907457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5022977857042157826419885 1883616696390809184907457)
            ·
              refine ⟨1412712522293106888680593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883616696390809184907457 1412712522293106888680593)
              ·
                refine ⟨1059534391719830166510445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1412712522293106888680593 1059534391719830166510445)
                ·
                  refine ⟨397325396894936312441417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059534391719830166510445 397325396894936312441417)
                  ·
                    rfl

theorem cell20_870512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_870512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870512 prefixEnd_870512 := by exact prefixLift 870512
  have htrace : WordTrace (prefixWord ++ tailWord_870512) baseStart_870512 baseEnd_870512 := by
    simpa [prefixWord, tailWord_870512, baseEnd_870512] using wordTrace_append hprefix tailTrace_870512
  have hstable : (prefixWord ++ tailWord_870512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870512).length < 2 ^ (prefixWord ++ tailWord_870512).sum := by decide
  have hdescent : baseEnd_870512 < baseStart_870512 := by decide
  rcases family_descends (prefixWord ++ tailWord_870512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870564 : List Nat := [2, 3, 1, 2, 4, 1, 7]
def baseStart_870564 : Nat := 118140960795 + 870564 * 2 ^ 59
def prefixEnd_870564 : Nat := 4983230072969 + 3 ^ 40 * 870564 * 2
def baseEnd_870564 : Nat := 44149903456872804745319

theorem tailTrace_870564 : CollatzResearch.WordTrace tailWord_870564 prefixEnd_870564 44149903456872804745319 := by
  unfold tailWord_870564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15876038809051391669625373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21168051745401855559500497 15876038809051391669625373)
  ·
    refine ⟨5953514553394271876109515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15876038809051391669625373 5953514553394271876109515)
    ·
      refine ⟨8930271830091407814164273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5953514553394271876109515 8930271830091407814164273)
      ·
        refine ⟨6697703872568555860623205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8930271830091407814164273 6697703872568555860623205)
        ·
          refine ⟨1255819476106604223866851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6697703872568555860623205 1255819476106604223866851)
          ·
            refine ⟨1883729214159906335800277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255819476106604223866851 1883729214159906335800277)
            ·
              refine ⟨44149903456872804745319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1883729214159906335800277 44149903456872804745319)
              ·
                rfl

theorem cell20_870564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 7].length) (baseStart_870564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870564 prefixEnd_870564 := by exact prefixLift 870564
  have htrace : WordTrace (prefixWord ++ tailWord_870564) baseStart_870564 baseEnd_870564 := by
    simpa [prefixWord, tailWord_870564, baseEnd_870564] using wordTrace_append hprefix tailTrace_870564
  have hstable : (prefixWord ++ tailWord_870564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870564).length < 2 ^ (prefixWord ++ tailWord_870564).sum := by decide
  have hdescent : baseEnd_870564 < baseStart_870564 := by decide
  rcases family_descends (prefixWord ++ tailWord_870564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870580 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 3]
def baseStart_870580 : Nat := 118140960795 + 870580 * 2 ^ 59
def prefixEnd_870580 : Nat := 4983230072969 + 3 ^ 40 * 870580 * 2
def baseEnd_870580 : Nat := 397356433947830298174473

theorem tailTrace_870580 : CollatzResearch.WordTrace tailWord_870580 prefixEnd_870580 397356433947830298174473 := by
  unfold tailWord_870580
  simp only [CollatzResearch.WordTrace]
  refine ⟨15876330593022409035916597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21168440790696545381222129 15876330593022409035916597)
  ·
    refine ⟨1488405993095850847117181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15876330593022409035916597 1488405993095850847117181)
    ·
      refine ⟨558152247410944067668943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1488405993095850847117181 558152247410944067668943)
      ·
        refine ⟨837228371116416101503415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558152247410944067668943 837228371116416101503415)
        ·
          refine ⟨1255842556674624152255123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837228371116416101503415 1255842556674624152255123)
          ·
            refine ⟨1883763835011936228382685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255842556674624152255123 1883763835011936228382685)
            ·
              refine ⟨706411438129476085643507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1883763835011936228382685 706411438129476085643507)
              ·
                refine ⟨1059617157194214128465261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706411438129476085643507 1059617157194214128465261)
                ·
                  refine ⟨397356433947830298174473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059617157194214128465261 397356433947830298174473)
                  ·
                    rfl

theorem cell20_870580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_870580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870580 prefixEnd_870580 := by exact prefixLift 870580
  have htrace : WordTrace (prefixWord ++ tailWord_870580) baseStart_870580 baseEnd_870580 := by
    simpa [prefixWord, tailWord_870580, baseEnd_870580] using wordTrace_append hprefix tailTrace_870580
  have hstable : (prefixWord ++ tailWord_870580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870580).length < 2 ^ (prefixWord ++ tailWord_870580).sum := by decide
  have hdescent : baseEnd_870580 < baseStart_870580 := by decide
  rcases family_descends (prefixWord ++ tailWord_870580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870585 : List Nat := [1, 2, 1, 4, 1, 2, 2, 7]
def baseStart_870585 : Nat := 118140960795 + 870585 * 2 ^ 59
def prefixEnd_870585 : Nat := 4983230072969 + 3 ^ 40 * 870585 * 2
def baseEnd_870585 : Nat := 132452905361357501002595

theorem tailTrace_870585 : CollatzResearch.WordTrace tailWord_870585 prefixEnd_870585 132452905361357501002595 := by
  unfold tailWord_870585
  simp only [CollatzResearch.WordTrace]
  refine ⟨31752843551026703925765209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21168562367351135950510139 31752843551026703925765209)
  ·
    refine ⟨23814632663270027944323907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31752843551026703925765209 23814632663270027944323907)
    ·
      refine ⟨35721948994905041916485861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23814632663270027944323907 35721948994905041916485861)
      ·
        refine ⟨6697865436544695359341099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35721948994905041916485861 6697865436544695359341099)
        ·
          refine ⟨10046798154817043039011649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6697865436544695359341099 10046798154817043039011649)
          ·
            refine ⟨7535098616112782279258737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10046798154817043039011649 7535098616112782279258737)
            ·
              refine ⟨5651323962084586709444053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7535098616112782279258737 5651323962084586709444053)
              ·
                refine ⟨132452905361357501002595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5651323962084586709444053 132452905361357501002595)
                ·
                  rfl

theorem cell20_870585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_870585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870585 prefixEnd_870585 := by exact prefixLift 870585
  have htrace : WordTrace (prefixWord ++ tailWord_870585) baseStart_870585 baseEnd_870585 := by
    simpa [prefixWord, tailWord_870585, baseEnd_870585] using wordTrace_append hprefix tailTrace_870585
  have hstable : (prefixWord ++ tailWord_870585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870585).length < 2 ^ (prefixWord ++ tailWord_870585).sum := by decide
  have hdescent : baseEnd_870585 < baseStart_870585 := by decide
  rcases family_descends (prefixWord ++ tailWord_870585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870629 : List Nat := [1, 3, 1, 4, 2, 2, 3, 2, 2]
def baseStart_870629 : Nat := 118140960795 + 870629 * 2 ^ 59
def prefixEnd_870629 : Nat := 4983230072969 + 3 ^ 40 * 870629 * 2
def baseEnd_870629 : Nat := 397378798883003905540939

theorem tailTrace_870629 : CollatzResearch.WordTrace tailWord_870629 prefixEnd_870629 397378798883003905540939 := by
  unfold tailWord_870629
  simp only [CollatzResearch.WordTrace]
  refine ⟨31754448362867299440366941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21169632241911532960244627 31754448362867299440366941)
  ·
    refine ⟨11907918136075237290137603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31754448362867299440366941 11907918136075237290137603)
    ·
      refine ⟨17861877204112855935206405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11907918136075237290137603 17861877204112855935206405)
      ·
        refine ⟨3349101975771160487851201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17861877204112855935206405 3349101975771160487851201)
        ·
          refine ⟨2511826481828370365888401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3349101975771160487851201 2511826481828370365888401)
          ·
            refine ⟨1883869861371277774416301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511826481828370365888401 1883869861371277774416301)
            ·
              refine ⟨706451198014229165406113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1883869861371277774416301 706451198014229165406113)
              ·
                refine ⟨529838398510671874054585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706451198014229165406113 529838398510671874054585)
                ·
                  refine ⟨397378798883003905540939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529838398510671874054585 397378798883003905540939)
                  ·
                    rfl

theorem cell20_870629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_870629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870629 prefixEnd_870629 := by exact prefixLift 870629
  have htrace : WordTrace (prefixWord ++ tailWord_870629) baseStart_870629 baseEnd_870629 := by
    simpa [prefixWord, tailWord_870629, baseEnd_870629] using wordTrace_append hprefix tailTrace_870629
  have hstable : (prefixWord ++ tailWord_870629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870629).length < 2 ^ (prefixWord ++ tailWord_870629).sum := by decide
  have hdescent : baseEnd_870629 < baseStart_870629 := by decide
  rcases family_descends (prefixWord ++ tailWord_870629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870688 : List Nat := [2, 1, 1, 5, 2, 2, 1, 4, 2]
def baseStart_870688 : Nat := 118140960795 + 870688 * 2 ^ 59
def prefixEnd_870688 : Nat := 4983230072969 + 3 ^ 40 * 870688 * 2
def baseEnd_870688 : Nat := 397405728090661922574031

theorem tailTrace_870688 : CollatzResearch.WordTrace tailWord_870688 prefixEnd_870688 397405728090661922574031 := by
  unfold tailWord_870688
  simp only [CollatzResearch.WordTrace]
  refine ⟨15878300134826776258382359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21171066846435701677843145 15878300134826776258382359)
  ·
    refine ⟨23817450202240164387573539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15878300134826776258382359 23817450202240164387573539)
    ·
      refine ⟨35726175303360246581360309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23817450202240164387573539 35726175303360246581360309)
      ·
        refine ⟨3349328934690023117002529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35726175303360246581360309 3349328934690023117002529)
        ·
          refine ⟨2511996701017517337751897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3349328934690023117002529 2511996701017517337751897)
          ·
            refine ⟨1883997525763138003313923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511996701017517337751897 1883997525763138003313923)
            ·
              refine ⟨2825996288644707004970885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883997525763138003313923 2825996288644707004970885)
              ·
                refine ⟨529874304120882563432041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2825996288644707004970885 529874304120882563432041)
                ·
                  refine ⟨397405728090661922574031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529874304120882563432041 397405728090661922574031)
                  ·
                    rfl

theorem cell20_870688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_870688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870688 prefixEnd_870688 := by exact prefixLift 870688
  have htrace : WordTrace (prefixWord ++ tailWord_870688) baseStart_870688 baseEnd_870688 := by
    simpa [prefixWord, tailWord_870688, baseEnd_870688] using wordTrace_append hprefix tailTrace_870688
  have hstable : (prefixWord ++ tailWord_870688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870688).length < 2 ^ (prefixWord ++ tailWord_870688).sum := by decide
  have hdescent : baseEnd_870688 < baseStart_870688 := by decide
  rcases family_descends (prefixWord ++ tailWord_870688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870716 : List Nat := [2, 2, 2, 2, 1, 2, 5, 4]
def baseStart_870716 : Nat := 118140960795 + 870716 * 2 ^ 59
def prefixEnd_870716 : Nat := 4983230072969 + 3 ^ 40 * 870716 * 2
def baseEnd_870716 : Nat := 132472836017872756546861

theorem tailTrace_870716 : CollatzResearch.WordTrace tailWord_870716 prefixEnd_870716 132472836017872756546861 := by
  unfold tailWord_870716
  simp only [CollatzResearch.WordTrace]
  refine ⟨15878810756776056649392001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21171747675701408865856001 15878810756776056649392001)
  ·
    refine ⟨11909108067582042487044001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15878810756776056649392001 11909108067582042487044001)
    ·
      refine ⟨8931831050686531865283001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11909108067582042487044001 8931831050686531865283001)
      ·
        refine ⟨6698873288014898898962251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8931831050686531865283001 6698873288014898898962251)
        ·
          refine ⟨10048309932022348348443377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6698873288014898898962251 10048309932022348348443377)
          ·
            refine ⟨7536232449016761261332533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10048309932022348348443377 7536232449016761261332533)
            ·
              refine ⟨706521792095321368249925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7536232449016761261332533 706521792095321368249925)
              ·
                refine ⟨132472836017872756546861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706521792095321368249925 132472836017872756546861)
                ·
                  rfl

theorem cell20_870716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_870716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870716 prefixEnd_870716 := by exact prefixLift 870716
  have htrace : WordTrace (prefixWord ++ tailWord_870716) baseStart_870716 baseEnd_870716 := by
    simpa [prefixWord, tailWord_870716, baseEnd_870716] using wordTrace_append hprefix tailTrace_870716
  have hstable : (prefixWord ++ tailWord_870716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870716).length < 2 ^ (prefixWord ++ tailWord_870716).sum := by decide
  have hdescent : baseEnd_870716 < baseStart_870716 := by decide
  rcases family_descends (prefixWord ++ tailWord_870716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870737 : List Nat := [1, 2, 2, 1, 4, 3, 7]
def baseStart_870737 : Nat := 118140960795 + 870737 * 2 ^ 59
def prefixEnd_870737 : Nat := 4983230072969 + 3 ^ 40 * 870737 * 2
def baseEnd_870737 : Nat := 44158677002870614437833

theorem tailTrace_870737 : CollatzResearch.WordTrace tailWord_870737 prefixEnd_870737 44158677002870614437833 := by
  unfold tailWord_870737
  simp only [CollatzResearch.WordTrace]
  refine ⟨31758387446476033885298465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21172258297650689256865643 31758387446476033885298465)
  ·
    refine ⟨23818790584857025413973849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31758387446476033885298465 23818790584857025413973849)
    ·
      refine ⟨17864092938642769060480387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23818790584857025413973849 17864092938642769060480387)
      ·
        refine ⟨26796139407964153590720581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17864092938642769060480387 26796139407964153590720581)
        ·
          refine ⟨5024276138993278798260109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26796139407964153590720581 5024276138993278798260109)
          ·
            refine ⟨1884103552122479549347541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5024276138993278798260109 1884103552122479549347541)
            ·
              refine ⟨44158677002870614437833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1884103552122479549347541 44158677002870614437833)
              ·
                rfl

theorem cell20_870737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 7].length) (baseStart_870737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870737 prefixEnd_870737 := by exact prefixLift 870737
  have htrace : WordTrace (prefixWord ++ tailWord_870737) baseStart_870737 baseEnd_870737 := by
    simpa [prefixWord, tailWord_870737, baseEnd_870737] using wordTrace_append hprefix tailTrace_870737
  have hstable : (prefixWord ++ tailWord_870737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870737).length < 2 ^ (prefixWord ++ tailWord_870737).sum := by decide
  have hdescent : baseEnd_870737 < baseStart_870737 := by decide
  rcases family_descends (prefixWord ++ tailWord_870737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870740 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_870740 : Nat := 118140960795 + 870740 * 2 ^ 59
def prefixEnd_870740 : Nat := 4983230072969 + 3 ^ 40 * 870740 * 2
def baseEnd_870740 : Nat := 397429462307580852840485

theorem tailTrace_870740 : CollatzResearch.WordTrace tailWord_870740 prefixEnd_870740 397429462307580852840485 := by
  unfold tailWord_870740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15879248432732582698828837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21172331243643443598438449 15879248432732582698828837)
  ·
    refine ⟨2977359081137359256030407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15879248432732582698828837 2977359081137359256030407)
    ·
      refine ⟨4466038621706038884045611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977359081137359256030407 4466038621706038884045611)
      ·
        refine ⟨6699057932559058326068417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466038621706038884045611 6699057932559058326068417)
        ·
          refine ⟨5024293449419293744551313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6699057932559058326068417 5024293449419293744551313)
          ·
            refine ⟨3768220087064470308413485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5024293449419293744551313 3768220087064470308413485)
            ·
              refine ⟨1413082532649176365655057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3768220087064470308413485 1413082532649176365655057)
              ·
                refine ⟨1059811899486882274241293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413082532649176365655057 1059811899486882274241293)
                ·
                  refine ⟨397429462307580852840485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059811899486882274241293 397429462307580852840485)
                  ·
                    rfl

theorem cell20_870740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_870740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870740 prefixEnd_870740 := by exact prefixLift 870740
  have htrace : WordTrace (prefixWord ++ tailWord_870740) baseStart_870740 baseEnd_870740 := by
    simpa [prefixWord, tailWord_870740, baseEnd_870740] using wordTrace_append hprefix tailTrace_870740
  have hstable : (prefixWord ++ tailWord_870740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870740).length < 2 ^ (prefixWord ++ tailWord_870740).sum := by decide
  have hdescent : baseEnd_870740 < baseStart_870740 := by decide
  rcases family_descends (prefixWord ++ tailWord_870740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870768 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_870768 : Nat := 118140960795 + 870768 * 2 ^ 59
def prefixEnd_870768 : Nat := 4983230072969 + 3 ^ 40 * 870768 * 2
def baseEnd_870768 : Nat := 397442242270537199907037

theorem tailTrace_870768 : CollatzResearch.WordTrace tailWord_870768 prefixEnd_870768 397442242270537199907037 := by
  unfold tailWord_870768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15879759054681863089838479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21173012072909150786451305 15879759054681863089838479)
  ·
    refine ⟨23819638582022794634757719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15879759054681863089838479 23819638582022794634757719)
    ·
      refine ⟨35729457873034191952136579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23819638582022794634757719 35729457873034191952136579)
      ·
        refine ⟨53594186809551287928204869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35729457873034191952136579 53594186809551287928204869)
        ·
          refine ⟨10048910026790866486538413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53594186809551287928204869 10048910026790866486538413)
          ·
            refine ⟨3768341260046574932451905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10048910026790866486538413 3768341260046574932451905)
            ·
              refine ⟨2826255945034931199338929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3768341260046574932451905 2826255945034931199338929)
              ·
                refine ⟨2119691958776198399504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2826255945034931199338929 2119691958776198399504197)
                ·
                  refine ⟨397442242270537199907037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2119691958776198399504197 397442242270537199907037)
                  ·
                    rfl

theorem cell20_870768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_870768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870768 prefixEnd_870768 := by exact prefixLift 870768
  have htrace : WordTrace (prefixWord ++ tailWord_870768) baseStart_870768 baseEnd_870768 := by
    simpa [prefixWord, tailWord_870768, baseEnd_870768] using wordTrace_append hprefix tailTrace_870768
  have hstable : (prefixWord ++ tailWord_870768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870768).length < 2 ^ (prefixWord ++ tailWord_870768).sum := by decide
  have hdescent : baseEnd_870768 < baseStart_870768 := by decide
  rcases family_descends (prefixWord ++ tailWord_870768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870816 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_870816 : Nat := 118140960795 + 870816 * 2 ^ 59
def prefixEnd_870816 : Nat := 4983230072969 + 3 ^ 40 * 870816 * 2
def baseEnd_870816 : Nat := 397464150778462366306841

theorem tailTrace_870816 : CollatzResearch.WordTrace tailWord_870816 prefixEnd_870816 397464150778462366306841 := by
  unfold tailWord_870816
  simp only [CollatzResearch.WordTrace]
  refine ⟨15880634406594915188712151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21174179208793220251616201 15880634406594915188712151)
  ·
    refine ⟨23820951609892372783068227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15880634406594915188712151 23820951609892372783068227)
    ·
      refine ⟨35731427414838559174602341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23820951609892372783068227 35731427414838559174602341)
      ·
        refine ⟨6699642640282229845237939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35731427414838559174602341 6699642640282229845237939)
        ·
          refine ⟨10049463960423344767856909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6699642640282229845237939 10049463960423344767856909)
          ·
            refine ⟨3768548985158754287946341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10049463960423344767856909 3768548985158754287946341)
            ·
              refine ⟨706602934717266428989939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3768548985158754287946341 706602934717266428989939)
              ·
                refine ⟨1059904402075899643484909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706602934717266428989939 1059904402075899643484909)
                ·
                  refine ⟨397464150778462366306841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059904402075899643484909 397464150778462366306841)
                  ·
                    rfl

theorem cell20_870816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_870816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870816 prefixEnd_870816 := by exact prefixLift 870816
  have htrace : WordTrace (prefixWord ++ tailWord_870816) baseStart_870816 baseEnd_870816 := by
    simpa [prefixWord, tailWord_870816, baseEnd_870816] using wordTrace_append hprefix tailTrace_870816
  have hstable : (prefixWord ++ tailWord_870816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870816).length < 2 ^ (prefixWord ++ tailWord_870816).sum := by decide
  have hdescent : baseEnd_870816 < baseStart_870816 := by decide
  rcases family_descends (prefixWord ++ tailWord_870816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870865 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_870865 : Nat := 118140960795 + 870865 * 2 ^ 59
def prefixEnd_870865 : Nat := 4983230072969 + 3 ^ 40 * 870865 * 2
def baseEnd_870865 : Nat := 397486515713635973673307

theorem tailTrace_870865 : CollatzResearch.WordTrace tailWord_870865 prefixEnd_870865 397486515713635973673307 := by
  unfold tailWord_870865
  simp only [CollatzResearch.WordTrace]
  refine ⟨31763055990012311745958049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21175370660008207830638699 31763055990012311745958049)
  ·
    refine ⟨23822291992509233809468537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31763055990012311745958049 23822291992509233809468537)
    ·
      refine ⟨17866718994381925357101403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23822291992509233809468537 17866718994381925357101403)
      ·
        refine ⟨26800078491572888035652105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17866718994381925357101403 26800078491572888035652105)
        ·
          refine ⟨20100058868679666026739079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26800078491572888035652105 20100058868679666026739079)
          ·
            refine ⟨30150088303019499040108619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20100058868679666026739079 30150088303019499040108619)
            ·
              refine ⟨45225132454529248560162929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30150088303019499040108619 45225132454529248560162929)
              ·
                refine ⟨33918849340896936420122197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45225132454529248560162929 33918849340896936420122197)
                ·
                  refine ⟨397486515713635973673307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33918849340896936420122197 397486515713635973673307)
                  ·
                    rfl

theorem cell20_870865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_870865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870865 prefixEnd_870865 := by exact prefixLift 870865
  have htrace : WordTrace (prefixWord ++ tailWord_870865) baseStart_870865 baseEnd_870865 := by
    simpa [prefixWord, tailWord_870865, baseEnd_870865] using wordTrace_append hprefix tailTrace_870865
  have hstable : (prefixWord ++ tailWord_870865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870865).length < 2 ^ (prefixWord ++ tailWord_870865).sum := by decide
  have hdescent : baseEnd_870865 < baseStart_870865 := by decide
  rcases family_descends (prefixWord ++ tailWord_870865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870868 : List Nat := [2, 4, 1, 2, 2, 1, 3, 5]
def baseStart_870868 : Nat := 118140960795 + 870868 * 2 ^ 59
def prefixEnd_870868 : Nat := 4983230072969 + 3 ^ 40 * 870868 * 2
def baseEnd_870868 : Nat := 132495961665127098857765

theorem tailTrace_870868 : CollatzResearch.WordTrace tailWord_870868 prefixEnd_870868 132495961665127098857765 := by
  unfold tailWord_870868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15881582704500721629158629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21175443606000962172211505 15881582704500721629158629)
  ·
    refine ⟨2977796757093885305467243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15881582704500721629158629 2977796757093885305467243)
    ·
      refine ⟨4466695135640827958200865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977796757093885305467243 4466695135640827958200865)
      ·
        refine ⟨3350021351730620968650649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4466695135640827958200865 3350021351730620968650649)
        ·
          refine ⟨2512516013797965726487987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3350021351730620968650649 2512516013797965726487987)
          ·
            refine ⟨3768774020696948589731981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512516013797965726487987 3768774020696948589731981)
            ·
              refine ⟨1413290257761355721149493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3768774020696948589731981 1413290257761355721149493)
              ·
                refine ⟨132495961665127098857765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1413290257761355721149493 132495961665127098857765)
                ·
                  rfl

theorem cell20_870868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_870868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870868 prefixEnd_870868 := by exact prefixLift 870868
  have htrace : WordTrace (prefixWord ++ tailWord_870868) baseStart_870868 baseEnd_870868 := by
    simpa [prefixWord, tailWord_870868, baseEnd_870868] using wordTrace_append hprefix tailTrace_870868
  have hstable : (prefixWord ++ tailWord_870868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870868).length < 2 ^ (prefixWord ++ tailWord_870868).sum := by decide
  have hdescent : baseEnd_870868 < baseStart_870868 := by decide
  rcases family_descends (prefixWord ++ tailWord_870868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870885 : List Nat := [1, 3, 1, 5, 2, 1, 3, 4]
def baseStart_870885 : Nat := 118140960795 + 870885 * 2 ^ 59
def prefixEnd_870885 : Nat := 4983230072969 + 3 ^ 40 * 870885 * 2
def baseEnd_870885 : Nat := 132498548086201597668853

theorem tailTrace_870885 : CollatzResearch.WordTrace tailWord_870885 prefixEnd_870885 132498548086201597668853 := by
  unfold tailWord_870885
  simp only [CollatzResearch.WordTrace]
  refine ⟨31763785449939855161686109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21175856966626570107790739 31763785449939855161686109)
  ·
    refine ⟨11911419543727445685632291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31763785449939855161686109 11911419543727445685632291)
    ·
      refine ⟨17867129315591168528448437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11911419543727445685632291 17867129315591168528448437)
      ·
        refine ⟨1675043373336672049542041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17867129315591168528448437 1675043373336672049542041)
        ·
          refine ⟨1256282530002504037156531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1675043373336672049542041 1256282530002504037156531)
          ·
            refine ⟨1884423795003756055734797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256282530002504037156531 1884423795003756055734797)
            ·
              refine ⟨706658923126408520900549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1884423795003756055734797 706658923126408520900549)
              ·
                refine ⟨132498548086201597668853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706658923126408520900549 132498548086201597668853)
                ·
                  rfl

theorem cell20_870885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 4].length) (baseStart_870885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870885 prefixEnd_870885 := by exact prefixLift 870885
  have htrace : WordTrace (prefixWord ++ tailWord_870885) baseStart_870885 baseEnd_870885 := by
    simpa [prefixWord, tailWord_870885, baseEnd_870885] using wordTrace_append hprefix tailTrace_870885
  have hstable : (prefixWord ++ tailWord_870885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870885).length < 2 ^ (prefixWord ++ tailWord_870885).sum := by decide
  have hdescent : baseEnd_870885 < baseStart_870885 := by decide
  rcases family_descends (prefixWord ++ tailWord_870885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870896 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_870896 : Nat := 118140960795 + 870896 * 2 ^ 59
def prefixEnd_870896 : Nat := 4983230072969 + 3 ^ 40 * 870896 * 2
def baseEnd_870896 : Nat := 397500664958337643639847

theorem tailTrace_870896 : CollatzResearch.WordTrace tailWord_870896 prefixEnd_870896 397500664958337643639847 := by
  unfold tailWord_870896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15882093326450002020168271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21176124435266669360224361 15882093326450002020168271)
  ·
    refine ⟨23823139989675003030252407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15882093326450002020168271 23823139989675003030252407)
    ·
      refine ⟨35734709984512504545378611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23823139989675003030252407 35734709984512504545378611)
      ·
        refine ⟨53602064976768756818067917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35734709984512504545378611 53602064976768756818067917)
        ·
          refine ⟨20100774366288283806775469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53602064976768756818067917 20100774366288283806775469)
          ·
            refine ⟨7537790387358106427540801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20100774366288283806775469 7537790387358106427540801)
            ·
              refine ⟨5653342790518579820655601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7537790387358106427540801 5653342790518579820655601)
              ·
                refine ⟨4240007092888934865491701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5653342790518579820655601 4240007092888934865491701)
                ·
                  refine ⟨397500664958337643639847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4240007092888934865491701 397500664958337643639847)
                  ·
                    rfl

theorem cell20_870896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_870896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870896 prefixEnd_870896 := by exact prefixLift 870896
  have htrace : WordTrace (prefixWord ++ tailWord_870896) baseStart_870896 baseEnd_870896 := by
    simpa [prefixWord, tailWord_870896, baseEnd_870896] using wordTrace_append hprefix tailTrace_870896
  have hstable : (prefixWord ++ tailWord_870896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870896).length < 2 ^ (prefixWord ++ tailWord_870896).sum := by decide
  have hdescent : baseEnd_870896 < baseStart_870896 := by decide
  rcases family_descends (prefixWord ++ tailWord_870896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870899 : List Nat := [1, 1, 1, 2, 2, 2, 6, 3, 2]
def baseStart_870899 : Nat := 118140960795 + 870899 * 2 ^ 59
def prefixEnd_870899 : Nat := 4983230072969 + 3 ^ 40 * 870899 * 2
def baseEnd_870899 : Nat := 397502034240082966539835

theorem tailTrace_870899 : CollatzResearch.WordTrace tailWord_870899 prefixEnd_870899 397502034240082966539835 := by
  unfold tailWord_870899
  simp only [CollatzResearch.WordTrace]
  refine ⟨31764296071889135552695751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21176197381259423701797167 31764296071889135552695751)
  ·
    refine ⟨47646444107833703329043627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31764296071889135552695751 47646444107833703329043627)
    ·
      refine ⟨71469666161750554993565441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47646444107833703329043627 71469666161750554993565441)
      ·
        refine ⟨53602249621312916245174081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71469666161750554993565441 53602249621312916245174081)
        ·
          refine ⟨40201687215984687183880561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53602249621312916245174081 40201687215984687183880561)
          ·
            refine ⟨30151265411988515387910421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40201687215984687183880561 30151265411988515387910421)
            ·
              refine ⟨1413340566186961658808301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30151265411988515387910421 1413340566186961658808301)
              ·
                refine ⟨530002712320110622053113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413340566186961658808301 530002712320110622053113)
                ·
                  refine ⟨397502034240082966539835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530002712320110622053113 397502034240082966539835)
                  ·
                    rfl

theorem cell20_870899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 2].length) (baseStart_870899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870899 prefixEnd_870899 := by exact prefixLift 870899
  have htrace : WordTrace (prefixWord ++ tailWord_870899) baseStart_870899 baseEnd_870899 := by
    simpa [prefixWord, tailWord_870899, baseEnd_870899] using wordTrace_append hprefix tailTrace_870899
  have hstable : (prefixWord ++ tailWord_870899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870899).length < 2 ^ (prefixWord ++ tailWord_870899).sum := by decide
  have hdescent : baseEnd_870899 < baseStart_870899 := by decide
  rcases family_descends (prefixWord ++ tailWord_870899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870913 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_870913 : Nat := 118140960795 + 870913 * 2 ^ 59
def prefixEnd_870913 : Nat := 4983230072969 + 3 ^ 40 * 870913 * 2
def baseEnd_870913 : Nat := 397508424221561140073111

theorem tailTrace_870913 : CollatzResearch.WordTrace tailWord_870913 prefixEnd_870913 397508424221561140073111 := by
  unfold tailWord_870913
  simp only [CollatzResearch.WordTrace]
  refine ⟨31764806693838415943705393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21176537795892277295803595 31764806693838415943705393)
  ·
    refine ⟨23823605020378811957779045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31764806693838415943705393 23823605020378811957779045)
    ·
      refine ⟨4466925941321027242083571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23823605020378811957779045 4466925941321027242083571)
      ·
        refine ⟨6700388911981540863125357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466925941321027242083571 6700388911981540863125357)
        ·
          refine ⟨2512645841993077823672009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6700388911981540863125357 2512645841993077823672009)
          ·
            refine ⟨1884484381494808367754007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2512645841993077823672009 1884484381494808367754007)
            ·
              refine ⟨2826726572242212551631011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884484381494808367754007 2826726572242212551631011)
              ·
                refine ⟨4240089858363318827446517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826726572242212551631011 4240089858363318827446517)
                ·
                  refine ⟨397508424221561140073111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4240089858363318827446517 397508424221561140073111)
                  ·
                    rfl

theorem cell20_870913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_870913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870913 prefixEnd_870913 := by exact prefixLift 870913
  have htrace : WordTrace (prefixWord ++ tailWord_870913) baseStart_870913 baseEnd_870913 := by
    simpa [prefixWord, tailWord_870913, baseEnd_870913] using wordTrace_append hprefix tailTrace_870913
  have hstable : (prefixWord ++ tailWord_870913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870913).length < 2 ^ (prefixWord ++ tailWord_870913).sum := by decide
  have hdescent : baseEnd_870913 < baseStart_870913 := by decide
  rcases family_descends (prefixWord ++ tailWord_870913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870916 : List Nat := [2, 3, 2, 3, 1, 1, 2, 4, 2]
def baseStart_870916 : Nat := 118140960795 + 870916 * 2 ^ 59
def prefixEnd_870916 : Nat := 4983230072969 + 3 ^ 40 * 870916 * 2
def baseEnd_870916 : Nat := 397509793503306462973099

theorem tailTrace_870916 : CollatzResearch.WordTrace tailWord_870916 prefixEnd_870916 397509793503306462973099 := by
  unfold tailWord_870916
  simp only [CollatzResearch.WordTrace]
  refine ⟨15882458056413773728032301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21176610741885031637376401 15882458056413773728032301)
  ·
    refine ⟨5955921771155165148012113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15882458056413773728032301 5955921771155165148012113)
    ·
      refine ⟨4466941328366373861009085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5955921771155165148012113 4466941328366373861009085)
      ·
        refine ⟨1675102998137390197878407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4466941328366373861009085 1675102998137390197878407)
        ·
          refine ⟨2512654497206085296817611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675102998137390197878407 2512654497206085296817611)
          ·
            refine ⟨3768981745809127945226417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512654497206085296817611 3768981745809127945226417)
            ·
              refine ⟨2826736309356845958919813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3768981745809127945226417 2826736309356845958919813)
              ·
                refine ⟨530013058004408617297465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2826736309356845958919813 530013058004408617297465)
                ·
                  refine ⟨397509793503306462973099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530013058004408617297465 397509793503306462973099)
                  ·
                    rfl

theorem cell20_870916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_870916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870916 prefixEnd_870916 := by exact prefixLift 870916
  have htrace : WordTrace (prefixWord ++ tailWord_870916) baseStart_870916 baseEnd_870916 := by
    simpa [prefixWord, tailWord_870916, baseEnd_870916] using wordTrace_append hprefix tailTrace_870916
  have hstable : (prefixWord ++ tailWord_870916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870916).length < 2 ^ (prefixWord ++ tailWord_870916).sum := by decide
  have hdescent : baseEnd_870916 < baseStart_870916 := by decide
  rcases family_descends (prefixWord ++ tailWord_870916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870944 : List Nat := [2, 1, 1, 6, 2, 1, 1, 6]
def baseStart_870944 : Nat := 118140960795 + 870944 * 2 ^ 59
def prefixEnd_870944 : Nat := 4983230072969 + 3 ^ 40 * 870944 * 2
def baseEnd_870944 : Nat := 132507524488754270013217

theorem tailTrace_870944 : CollatzResearch.WordTrace tailWord_870944 prefixEnd_870944 132507524488754270013217 := by
  unfold tailWord_870944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15882968678363054119041943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21177291571150738825389257 15882968678363054119041943)
  ·
    refine ⟨23824453017544581178562915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15882968678363054119041943 23824453017544581178562915)
    ·
      refine ⟨35736679526316871767844373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23824453017544581178562915 35736679526316871767844373)
      ·
        refine ⟨1675156852796103364117705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35736679526316871767844373 1675156852796103364117705)
        ·
          refine ⟨1256367639597077523088279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1675156852796103364117705 1256367639597077523088279)
          ·
            refine ⟨1884551459395616284632419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256367639597077523088279 1884551459395616284632419)
            ·
              refine ⟨2826827189093424426948629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884551459395616284632419 2826827189093424426948629)
              ·
                refine ⟨132507524488754270013217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2826827189093424426948629 132507524488754270013217)
                ·
                  rfl

theorem cell20_870944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_870944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870944 prefixEnd_870944 := by exact prefixLift 870944
  have htrace : WordTrace (prefixWord ++ tailWord_870944) baseStart_870944 baseEnd_870944 := by
    simpa [prefixWord, tailWord_870944, baseEnd_870944] using wordTrace_append hprefix tailTrace_870944
  have hstable : (prefixWord ++ tailWord_870944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870944).length < 2 ^ (prefixWord ++ tailWord_870944).sum := by decide
  have hdescent : baseEnd_870944 < baseStart_870944 := by decide
  rcases family_descends (prefixWord ++ tailWord_870944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870954 : List Nat := [3, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_870954 : Nat := 118140960795 + 870954 * 2 ^ 59
def prefixEnd_870954 : Nat := 4983230072969 + 3 ^ 40 * 870954 * 2
def baseEnd_870954 : Nat := 397527137738747219706277

theorem tailTrace_870954 : CollatzResearch.WordTrace tailWord_870954 prefixEnd_870954 397527137738747219706277 := by
  unfold tailWord_870954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941575521672469986486979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21177534724459919963965277 7941575521672469986486979)
  ·
    refine ⟨11912363282508704979730469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7941575521672469986486979 11912363282508704979730469)
    ·
      refine ⟨2233568115470382183699463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11912363282508704979730469 2233568115470382183699463)
      ·
        refine ⟨3350352173205573275549195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233568115470382183699463 3350352173205573275549195)
        ·
          refine ⟨5025528259808359913323793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350352173205573275549195 5025528259808359913323793)
          ·
            refine ⟨3769146194856269934992845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5025528259808359913323793 3769146194856269934992845)
            ·
              refine ⟨1413429823071101225622317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3769146194856269934992845 1413429823071101225622317)
              ·
                refine ⟨530036183651662959608369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413429823071101225622317 530036183651662959608369)
                ·
                  refine ⟨397527137738747219706277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530036183651662959608369 397527137738747219706277)
                  ·
                    rfl

theorem cell20_870954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_870954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870954 prefixEnd_870954 := by exact prefixLift 870954
  have htrace : WordTrace (prefixWord ++ tailWord_870954) baseStart_870954 baseEnd_870954 := by
    simpa [prefixWord, tailWord_870954, baseEnd_870954] using wordTrace_append hprefix tailTrace_870954
  have hstable : (prefixWord ++ tailWord_870954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870954).length < 2 ^ (prefixWord ++ tailWord_870954).sum := by decide
  have hdescent : baseEnd_870954 < baseStart_870954 := by decide
  rcases family_descends (prefixWord ++ tailWord_870954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870957 : List Nat := [1, 5, 4, 1, 2, 1, 6]
def baseStart_870957 : Nat := 118140960795 + 870957 * 2 ^ 59
def prefixEnd_870957 : Nat := 4983230072969 + 3 ^ 40 * 870957 * 2
def baseEnd_870957 : Nat := 44169834113388060289585

theorem tailTrace_870957 : CollatzResearch.WordTrace tailWord_870957 prefixEnd_870957 44169834113388060289585 := by
  unfold tailWord_870957
  simp only [CollatzResearch.WordTrace]
  refine ⟨31766411505679011458307125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21177607670452674305538083 31766411505679011458307125)
  ·
    refine ⟨2978101078657407324216293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31766411505679011458307125 2978101078657407324216293)
    ·
      refine ⟨558393952248263873290555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2978101078657407324216293 558393952248263873290555)
      ·
        refine ⟨837590928372395809935833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558393952248263873290555 837590928372395809935833)
        ·
          refine ⟨628193196279296857451875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837590928372395809935833 628193196279296857451875)
          ·
            refine ⟨942289794418945286177813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628193196279296857451875 942289794418945286177813)
            ·
              refine ⟨44169834113388060289585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 942289794418945286177813 44169834113388060289585)
              ·
                rfl

theorem cell20_870957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 6].length) (baseStart_870957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870957 prefixEnd_870957 := by exact prefixLift 870957
  have htrace : WordTrace (prefixWord ++ tailWord_870957) baseStart_870957 baseEnd_870957 := by
    simpa [prefixWord, tailWord_870957, baseEnd_870957] using wordTrace_append hprefix tailTrace_870957
  have hstable : (prefixWord ++ tailWord_870957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870957).length < 2 ^ (prefixWord ++ tailWord_870957).sum := by decide
  have hdescent : baseEnd_870957 < baseStart_870957 := by decide
  rcases family_descends (prefixWord ++ tailWord_870957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871024 : List Nat := [2, 1, 1, 1, 15]
def baseStart_871024 : Nat := 118140960795 + 871024 * 2 ^ 59
def prefixEnd_871024 : Nat := 4983230072969 + 3 ^ 40 * 871024 * 2
def baseEnd_871024 : Nat := 4908136884520223300897

theorem tailTrace_871024 : CollatzResearch.WordTrace tailWord_871024 prefixEnd_871024 4908136884520223300897 := by
  unfold tailWord_871024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15884427598218140950498063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21179236797624187933997417 15884427598218140950498063)
  ·
    refine ⟨23826641397327211425747095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15884427598218140950498063 23826641397327211425747095)
    ·
      refine ⟨35739962095990817138620643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23826641397327211425747095 35739962095990817138620643)
      ·
        refine ⟨53609943143986225707930965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35739962095990817138620643 53609943143986225707930965)
        ·
          refine ⟨4908136884520223300897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 53609943143986225707930965 4908136884520223300897)
          ·
            rfl

theorem cell20_871024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 15].length) (baseStart_871024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871024 prefixEnd_871024 := by exact prefixLift 871024
  have htrace : WordTrace (prefixWord ++ tailWord_871024) baseStart_871024 baseEnd_871024 := by
    simpa [prefixWord, tailWord_871024, baseEnd_871024] using wordTrace_append hprefix tailTrace_871024
  have hstable : (prefixWord ++ tailWord_871024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871024).length < 2 ^ (prefixWord ++ tailWord_871024).sum := by decide
  have hdescent : baseEnd_871024 < baseStart_871024 := by decide
  rcases family_descends (prefixWord ++ tailWord_871024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871026 : List Nat := [3, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_871026 : Nat := 118140960795 + 871026 * 2 ^ 59
def prefixEnd_871026 : Nat := 4983230072969 + 3 ^ 40 * 871026 * 2
def baseEnd_871026 : Nat := 397560000500634969305983

theorem tailTrace_871026 : CollatzResearch.WordTrace tailWord_871026 prefixEnd_871026 397560000500634969305983 := by
  unfold tailWord_871026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942232035607259060642233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21179285428286024161712621 7942232035607259060642233)
  ·
    refine ⟨5956674026705444295481675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7942232035607259060642233 5956674026705444295481675)
    ·
      refine ⟨8935011040058166443222513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956674026705444295481675 8935011040058166443222513)
      ·
        refine ⟨6701258280043624832416885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8935011040058166443222513 6701258280043624832416885)
        ·
          refine ⟨628242963754089828039083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6701258280043624832416885 628242963754089828039083)
          ·
            refine ⟨942364445631134742058625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628242963754089828039083 942364445631134742058625)
            ·
              refine ⟨706773334223351056543969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942364445631134742058625 706773334223351056543969)
              ·
                refine ⟨530080000667513292407977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706773334223351056543969 530080000667513292407977)
                ·
                  refine ⟨397560000500634969305983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530080000667513292407977 397560000500634969305983)
                  ·
                    rfl

theorem cell20_871026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_871026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871026 prefixEnd_871026 := by exact prefixLift 871026
  have htrace : WordTrace (prefixWord ++ tailWord_871026) baseStart_871026 baseEnd_871026 := by
    simpa [prefixWord, tailWord_871026, baseEnd_871026] using wordTrace_append hprefix tailTrace_871026
  have hstable : (prefixWord ++ tailWord_871026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871026).length < 2 ^ (prefixWord ++ tailWord_871026).sum := by decide
  have hdescent : baseEnd_871026 < baseStart_871026 := by decide
  rcases family_descends (prefixWord ++ tailWord_871026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871037 : List Nat := [1, 4, 1, 1, 6, 1, 1, 5]
def baseStart_871037 : Nat := 118140960795 + 871037 * 2 ^ 59
def prefixEnd_871037 : Nat := 4983230072969 + 3 ^ 40 * 871037 * 2
def baseEnd_871037 : Nat := 132521673733455939979757

theorem tailTrace_871037 : CollatzResearch.WordTrace tailWord_871037 prefixEnd_871037 132521673733455939979757 := by
  unfold tailWord_871037
  simp only [CollatzResearch.WordTrace]
  refine ⟨31769329345389185121219365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21179552896926123414146243 31769329345389185121219365)
  ·
    refine ⟨5956749252260472210228631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31769329345389185121219365 5956749252260472210228631)
    ·
      refine ⟨8935123878390708315342947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956749252260472210228631 8935123878390708315342947)
      ·
        refine ⟨13402685817586062473014421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935123878390708315342947 13402685817586062473014421)
        ·
          refine ⟨628250897699346678422551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13402685817586062473014421 628250897699346678422551)
          ·
            refine ⟨942376346549020017633827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628250897699346678422551 942376346549020017633827)
            ·
              refine ⟨1413564519823530026450741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942376346549020017633827 1413564519823530026450741)
              ·
                refine ⟨132521673733455939979757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1413564519823530026450741 132521673733455939979757)
                ·
                  rfl

theorem cell20_871037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 5].length) (baseStart_871037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871037 prefixEnd_871037 := by exact prefixLift 871037
  have htrace : WordTrace (prefixWord ++ tailWord_871037) baseStart_871037 baseEnd_871037 := by
    simpa [prefixWord, tailWord_871037, baseEnd_871037] using wordTrace_append hprefix tailTrace_871037
  have hstable : (prefixWord ++ tailWord_871037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871037).length < 2 ^ (prefixWord ++ tailWord_871037).sum := by decide
  have hdescent : baseEnd_871037 < baseStart_871037 := by decide
  rcases family_descends (prefixWord ++ tailWord_871037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871055 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_871055 : Nat := 118140960795 + 871055 * 2 ^ 59
def prefixEnd_871055 : Nat := 4983230072969 + 3 ^ 40 * 871055 * 2
def baseEnd_871055 : Nat := 397573236890839757339197

theorem tailTrace_871055 : CollatzResearch.WordTrace tailWord_871055 prefixEnd_871055 397573236890839757339197 := by
  unfold tailWord_871055
  simp only [CollatzResearch.WordTrace]
  refine ⟨31769985859323974195374619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21179990572882649463583079 31769985859323974195374619)
  ·
    refine ⟨47654978788985961293061929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31769985859323974195374619 47654978788985961293061929)
    ·
      refine ⟨35741234091739470969796447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47654978788985961293061929 35741234091739470969796447)
      ·
        refine ⟨53611851137609206454694671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35741234091739470969796447 53611851137609206454694671)
        ·
          refine ⟨80417776706413809682042007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53611851137609206454694671 80417776706413809682042007)
          ·
            refine ⟨120626665059620714523063011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80417776706413809682042007 120626665059620714523063011)
            ·
              refine ⟨180939997589431071784594517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120626665059620714523063011 180939997589431071784594517)
              ·
                refine ⟨2120390596751145372475717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 180939997589431071784594517 2120390596751145372475717)
                ·
                  refine ⟨397573236890839757339197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2120390596751145372475717 397573236890839757339197)
                  ·
                    rfl

theorem cell20_871055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_871055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871055 prefixEnd_871055 := by exact prefixLift 871055
  have htrace : WordTrace (prefixWord ++ tailWord_871055) baseStart_871055 baseEnd_871055 := by
    simpa [prefixWord, tailWord_871055, baseEnd_871055] using wordTrace_append hprefix tailTrace_871055
  have hstable : (prefixWord ++ tailWord_871055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871055).length < 2 ^ (prefixWord ++ tailWord_871055).sum := by decide
  have hdescent : baseEnd_871055 < baseStart_871055 := by decide
  rcases family_descends (prefixWord ++ tailWord_871055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871068 : List Nat := [2, 2, 3, 2, 2, 2, 2, 3, 2]
def baseStart_871068 : Nat := 118140960795 + 871068 * 2 ^ 59
def prefixEnd_871068 : Nat := 4983230072969 + 3 ^ 40 * 871068 * 2
def baseEnd_871068 : Nat := 397579170445069489905811

theorem tailTrace_871068 : CollatzResearch.WordTrace tailWord_871068 prefixEnd_871068 397579170445069489905811 := by
  unfold tailWord_871068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15885230004138438707798929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21180306672184584943731905 15885230004138438707798929)
  ·
    refine ⟨11913922503103829030849197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15885230004138438707798929 11913922503103829030849197)
    ·
      refine ⟨4467720938663935886568449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11913922503103829030849197 4467720938663935886568449)
      ·
        refine ⟨3350790703997951914926337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4467720938663935886568449 3350790703997951914926337)
        ·
          refine ⟨2513093027998463936194753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3350790703997951914926337 2513093027998463936194753)
          ·
            refine ⟨1884819770998847952146065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513093027998463936194753 1884819770998847952146065)
            ·
              refine ⟨1413614828249135964109549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884819770998847952146065 1413614828249135964109549)
              ·
                refine ⟨530105560593425986541081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413614828249135964109549 530105560593425986541081)
                ·
                  refine ⟨397579170445069489905811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530105560593425986541081 397579170445069489905811)
                  ·
                    rfl

theorem cell20_871068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_871068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871068 prefixEnd_871068 := by exact prefixLift 871068
  have htrace : WordTrace (prefixWord ++ tailWord_871068) baseStart_871068 baseEnd_871068 := by
    simpa [prefixWord, tailWord_871068, baseEnd_871068] using wordTrace_append hprefix tailTrace_871068
  have hstable : (prefixWord ++ tailWord_871068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871068).length < 2 ^ (prefixWord ++ tailWord_871068).sum := by decide
  have hdescent : baseEnd_871068 < baseStart_871068 := by decide
  rcases family_descends (prefixWord ++ tailWord_871068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871127 : List Nat := [1, 1, 3, 2, 1, 4, 3, 3, 2]
def baseStart_871127 : Nat := 118140960795 + 871127 * 2 ^ 59
def prefixEnd_871127 : Nat := 4983230072969 + 3 ^ 40 * 871127 * 2
def baseEnd_871127 : Nat := 397606099652727506938903

theorem tailTrace_871127 : CollatzResearch.WordTrace tailWord_871127 prefixEnd_871127 397606099652727506938903 := by
  unfold tailWord_871127
  simp only [CollatzResearch.WordTrace]
  refine ⟨31772611915063130491995635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21181741276708753661330423 31772611915063130491995635)
  ·
    refine ⟨47658917872594695737993453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31772611915063130491995635 47658917872594695737993453)
    ·
      refine ⟨17872094202223010901747545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47658917872594695737993453 17872094202223010901747545)
      ·
        refine ⟨13404070651667258176310659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17872094202223010901747545 13404070651667258176310659)
        ·
          refine ⟨20106105977500887264465989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13404070651667258176310659 20106105977500887264465989)
          ·
            refine ⟨3769894870781416362087373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20106105977500887264465989 3769894870781416362087373)
            ·
              refine ⟨1413710576543031135782765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3769894870781416362087373 1413710576543031135782765)
              ·
                refine ⟨530141466203636675918537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413710576543031135782765 530141466203636675918537)
                ·
                  refine ⟨397606099652727506938903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530141466203636675918537 397606099652727506938903)
                  ·
                    rfl

theorem cell20_871127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 2].length) (baseStart_871127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871127 prefixEnd_871127 := by exact prefixLift 871127
  have htrace : WordTrace (prefixWord ++ tailWord_871127) baseStart_871127 baseEnd_871127 := by
    simpa [prefixWord, tailWord_871127, baseEnd_871127] using wordTrace_append hprefix tailTrace_871127
  have hstable : (prefixWord ++ tailWord_871127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871127).length < 2 ^ (prefixWord ++ tailWord_871127).sum := by decide
  have hdescent : baseEnd_871127 < baseStart_871127 := by decide
  rcases family_descends (prefixWord ++ tailWord_871127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871144 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 4]
def baseStart_871144 : Nat := 118140960795 + 871144 * 2 ^ 59
def prefixEnd_871144 : Nat := 4983230072969 + 3 ^ 40 * 871144 * 2
def baseEnd_871144 : Nat := 397613858915951003372167

theorem tailTrace_871144 : CollatzResearch.WordTrace tailWord_871144 prefixEnd_871144 397613858915951003372167 := by
  unfold tailWord_871144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886615978000771197682243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21182154637334361596909657 15886615978000771197682243)
  ·
    refine ⟨23829923967001156796523365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15886615978000771197682243 23829923967001156796523365)
    ·
      refine ⟨4468110743812716899348131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23829923967001156796523365 4468110743812716899348131)
      ·
        refine ⟨6702166115719075349022197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468110743812716899348131 6702166115719075349022197)
        ·
          refine ⟨628328073348663313970831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6702166115719075349022197 628328073348663313970831)
          ·
            refine ⟨942492110022994970956247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628328073348663313970831 942492110022994970956247)
            ·
              refine ⟨1413738165034492456434371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942492110022994970956247 1413738165034492456434371)
              ·
                refine ⟨2120607247551738684651557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413738165034492456434371 2120607247551738684651557)
                ·
                  refine ⟨397613858915951003372167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2120607247551738684651557 397613858915951003372167)
                  ·
                    rfl

theorem cell20_871144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_871144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871144 prefixEnd_871144 := by exact prefixLift 871144
  have htrace : WordTrace (prefixWord ++ tailWord_871144) baseStart_871144 baseEnd_871144 := by
    simpa [prefixWord, tailWord_871144, baseEnd_871144] using wordTrace_append hprefix tailTrace_871144
  have hstable : (prefixWord ++ tailWord_871144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871144).length < 2 ^ (prefixWord ++ tailWord_871144).sum := by decide
  have hdescent : baseEnd_871144 < baseStart_871144 := by decide
  rcases family_descends (prefixWord ++ tailWord_871144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871169 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_871169 : Nat := 118140960795 + 871169 * 2 ^ 59
def prefixEnd_871169 : Nat := 4983230072969 + 3 ^ 40 * 871169 * 2
def baseEnd_871169 : Nat := 397625269597162027538731

theorem tailTrace_871169 : CollatzResearch.WordTrace tailWord_871169 prefixEnd_871169 397625269597162027538731 := by
  unfold tailWord_871169
  simp only [CollatzResearch.WordTrace]
  refine ⟨31774143780910971665024561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21182762520607314443349707 31774143780910971665024561)
  ·
    refine ⟨23830607835683228748768421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31774143780910971665024561 23830607835683228748768421)
    ·
      refine ⟨4468238969190605390394079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23830607835683228748768421 4468238969190605390394079)
      ·
        refine ⟨6702358453785908085591119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468238969190605390394079 6702358453785908085591119)
        ·
          refine ⟨10053537680678862128386679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6702358453785908085591119 10053537680678862128386679)
          ·
            refine ⟨15080306521018293192580019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10053537680678862128386679 15080306521018293192580019)
            ·
              refine ⟨22620459781527439788870029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15080306521018293192580019 22620459781527439788870029)
              ·
                refine ⟨8482672418072789920826261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22620459781527439788870029 8482672418072789920826261)
                ·
                  refine ⟨397625269597162027538731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8482672418072789920826261 397625269597162027538731)
                  ·
                    rfl

theorem cell20_871169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_871169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871169 prefixEnd_871169 := by exact prefixLift 871169
  have htrace : WordTrace (prefixWord ++ tailWord_871169) baseStart_871169 baseEnd_871169 := by
    simpa [prefixWord, tailWord_871169, baseEnd_871169] using wordTrace_append hprefix tailTrace_871169
  have hstable : (prefixWord ++ tailWord_871169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871169).length < 2 ^ (prefixWord ++ tailWord_871169).sum := by decide
  have hdescent : baseEnd_871169 < baseStart_871169 := by decide
  rcases family_descends (prefixWord ++ tailWord_871169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871241 : List Nat := [1, 2, 1, 1, 2, 6, 2, 3, 2]
def baseStart_871241 : Nat := 118140960795 + 871241 * 2 ^ 59
def prefixEnd_871241 : Nat := 4983230072969 + 3 ^ 40 * 871241 * 2
def baseEnd_871241 : Nat := 397658132359049777138437

theorem tailTrace_871241 : CollatzResearch.WordTrace tailWord_871241 prefixEnd_871241 397658132359049777138437 := by
  unfold tailWord_871241
  simp only [CollatzResearch.WordTrace]
  refine ⟨31776769836650127961645577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21184513224433418641097051 31776769836650127961645577)
  ·
    refine ⟨23832577377487595971234183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31776769836650127961645577 23832577377487595971234183)
    ·
      refine ⟨35748866066231393956851275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23832577377487595971234183 35748866066231393956851275)
      ·
        refine ⟨53623299099347090935276913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35748866066231393956851275 53623299099347090935276913)
        ·
          refine ⟨40217474324510318201457685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53623299099347090935276913 40217474324510318201457685)
          ·
            refine ⟨1885194108961421165693329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40217474324510318201457685 1885194108961421165693329)
            ·
              refine ⟨1413895581721065874269997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885194108961421165693329 1413895581721065874269997)
              ·
                refine ⟨530210843145399702851249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413895581721065874269997 530210843145399702851249)
                ·
                  refine ⟨397658132359049777138437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530210843145399702851249 397658132359049777138437)
                  ·
                    rfl

theorem cell20_871241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_871241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871241 prefixEnd_871241 := by exact prefixLift 871241
  have htrace : WordTrace (prefixWord ++ tailWord_871241) baseStart_871241 baseEnd_871241 := by
    simpa [prefixWord, tailWord_871241, baseEnd_871241] using wordTrace_append hprefix tailTrace_871241
  have hstable : (prefixWord ++ tailWord_871241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871241).length < 2 ^ (prefixWord ++ tailWord_871241).sum := by decide
  have hdescent : baseEnd_871241 < baseStart_871241 := by decide
  rcases family_descends (prefixWord ++ tailWord_871241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871255 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 3]
def baseStart_871255 : Nat := 118140960795 + 871255 * 2 ^ 59
def prefixEnd_871255 : Nat := 4983230072969 + 3 ^ 40 * 871255 * 2
def baseEnd_871255 : Nat := 397664522340527950671713

theorem tailTrace_871255 : CollatzResearch.WordTrace tailWord_871255 prefixEnd_871255 397664522340527950671713 := by
  unfold tailWord_871255
  simp only [CollatzResearch.WordTrace]
  refine ⟨31777280458599408352655219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21184853639066272235103479 31777280458599408352655219)
  ·
    refine ⟨47665920687899112528982829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31777280458599408352655219 47665920687899112528982829)
    ·
      refine ⟨17874720257962167198368561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47665920687899112528982829 17874720257962167198368561)
      ·
        refine ⟨13406040193471625398776421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17874720257962167198368561 13406040193471625398776421)
        ·
          refine ⟨2513632536275929762270579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13406040193471625398776421 2513632536275929762270579)
          ·
            refine ⟨3770448804413894643405869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513632536275929762270579 3770448804413894643405869)
            ·
              refine ⟨1413918301655210491277201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3770448804413894643405869 1413918301655210491277201)
              ·
                refine ⟨1060438726241407868457901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413918301655210491277201 1060438726241407868457901)
                ·
                  refine ⟨397664522340527950671713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060438726241407868457901 397664522340527950671713)
                  ·
                    rfl

theorem cell20_871255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_871255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871255 prefixEnd_871255 := by exact prefixLift 871255
  have htrace : WordTrace (prefixWord ++ tailWord_871255) baseStart_871255 baseEnd_871255 := by
    simpa [prefixWord, tailWord_871255, baseEnd_871255] using wordTrace_append hprefix tailTrace_871255
  have hstable : (prefixWord ++ tailWord_871255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871255).length < 2 ^ (prefixWord ++ tailWord_871255).sum := by decide
  have hdescent : baseEnd_871255 < baseStart_871255 := by decide
  rcases family_descends (prefixWord ++ tailWord_871255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871272 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_871272 : Nat := 118140960795 + 871272 * 2 ^ 59
def prefixEnd_871272 : Nat := 4983230072969 + 3 ^ 40 * 871272 * 2
def baseEnd_871272 : Nat := 397672281603751447104977

theorem tailTrace_871272 : CollatzResearch.WordTrace tailWord_871272 prefixEnd_871272 397672281603751447104977 := by
  unfold tailWord_871272
  simp only [CollatzResearch.WordTrace]
  refine ⟨15888950249768910128012035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21185266999691880170682713 15888950249768910128012035)
  ·
    refine ⟨23833425374653365192018053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15888950249768910128012035 23833425374653365192018053)
    ·
      refine ⟨4468767257747505973503385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23833425374653365192018053 4468767257747505973503385)
      ·
        refine ⟨3351575443310629480127539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4468767257747505973503385 3351575443310629480127539)
        ·
          refine ⟨5027363164965944220191309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351575443310629480127539 5027363164965944220191309)
          ·
            refine ⟨1885261186862229082571741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5027363164965944220191309 1885261186862229082571741)
            ·
              refine ⟨706972945073335905964403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1885261186862229082571741 706972945073335905964403)
              ·
                refine ⟨1060459417610003858946605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706972945073335905964403 1060459417610003858946605)
                ·
                  refine ⟨397672281603751447104977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060459417610003858946605 397672281603751447104977)
                  ·
                    rfl

theorem cell20_871272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_871272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871272 prefixEnd_871272 := by exact prefixLift 871272
  have htrace : WordTrace (prefixWord ++ tailWord_871272) baseStart_871272 baseEnd_871272 := by
    simpa [prefixWord, tailWord_871272, baseEnd_871272] using wordTrace_append hprefix tailTrace_871272
  have hstable : (prefixWord ++ tailWord_871272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871272).length < 2 ^ (prefixWord ++ tailWord_871272).sum := by decide
  have hdescent : baseEnd_871272 < baseStart_871272 := by decide
  rcases family_descends (prefixWord ++ tailWord_871272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871283 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_871283 : Nat := 118140960795 + 871283 * 2 ^ 59
def prefixEnd_871283 : Nat := 4983230072969 + 3 ^ 40 * 871283 * 2
def baseEnd_871283 : Nat := 397677302303484297738265

theorem tailTrace_871283 : CollatzResearch.WordTrace tailWord_871283 prefixEnd_871283 397677302303484297738265 := by
  unfold tailWord_871283
  simp only [CollatzResearch.WordTrace]
  refine ⟨31778301702497969134674503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21185534468331979423116335 31778301702497969134674503)
  ·
    refine ⟨47667452553746953702011755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31778301702497969134674503 47667452553746953702011755)
    ·
      refine ⟨71501178830620430553017633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47667452553746953702011755 71501178830620430553017633)
      ·
        refine ⟨53625884122965322914763225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71501178830620430553017633 53625884122965322914763225)
        ·
          refine ⟨40219413092223992186072419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53625884122965322914763225 40219413092223992186072419)
          ·
            refine ⟨60329119638335988279108629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40219413092223992186072419 60329119638335988279108629)
            ·
              refine ⟨2827927483046999450583217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60329119638335988279108629 2827927483046999450583217)
              ·
                refine ⟨2120945612285249587937413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827927483046999450583217 2120945612285249587937413)
                ·
                  refine ⟨397677302303484297738265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2120945612285249587937413 397677302303484297738265)
                  ·
                    rfl

theorem cell20_871283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_871283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871283 prefixEnd_871283 := by exact prefixLift 871283
  have htrace : WordTrace (prefixWord ++ tailWord_871283) baseStart_871283 baseEnd_871283 := by
    simpa [prefixWord, tailWord_871283, baseEnd_871283] using wordTrace_append hprefix tailTrace_871283
  have hstable : (prefixWord ++ tailWord_871283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871283).length < 2 ^ (prefixWord ++ tailWord_871283).sum := by decide
  have hdescent : baseEnd_871283 < baseStart_871283 := by decide
  rcases family_descends (prefixWord ++ tailWord_871283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871286 : List Nat := [5, 1, 1, 3, 1, 2, 1, 6]
def baseStart_871286 : Nat := 118140960795 + 871286 * 2 ^ 59
def prefixEnd_871286 : Nat := 4983230072969 + 3 ^ 40 * 871286 * 2
def baseEnd_871286 : Nat := 132559557195076540212751

theorem tailTrace_871286 : CollatzResearch.WordTrace tailWord_871286 prefixEnd_871286 132559557195076540212751 := by
  unfold tailWord_871286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1986150695092943790439607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21185607414324733764689141 1986150695092943790439607)
  ·
    refine ⟨2979226042639415685659411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1986150695092943790439607 2979226042639415685659411)
    ·
      refine ⟨4468839063959123528489117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979226042639415685659411 4468839063959123528489117)
      ·
        refine ⟨1675814648984671323183419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4468839063959123528489117 1675814648984671323183419)
        ·
          refine ⟨2513721973477006984775129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675814648984671323183419 2513721973477006984775129)
          ·
            refine ⟨1885291480107755238581347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513721973477006984775129 1885291480107755238581347)
            ·
              refine ⟨2827937220161632857872021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885291480107755238581347 2827937220161632857872021)
              ·
                refine ⟨132559557195076540212751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2827937220161632857872021 132559557195076540212751)
                ·
                  rfl

theorem cell20_871286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_871286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871286 prefixEnd_871286 := by exact prefixLift 871286
  have htrace : WordTrace (prefixWord ++ tailWord_871286) baseStart_871286 baseEnd_871286 := by
    simpa [prefixWord, tailWord_871286, baseEnd_871286] using wordTrace_append hprefix tailTrace_871286
  have hstable : (prefixWord ++ tailWord_871286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871286).length < 2 ^ (prefixWord ++ tailWord_871286).sum := by decide
  have hdescent : baseEnd_871286 < baseStart_871286 := by decide
  rcases family_descends (prefixWord ++ tailWord_871286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871324 : List Nat := [2, 2, 3, 3, 2, 1, 2, 5]
def baseStart_871324 : Nat := 118140960795 + 871324 * 2 ^ 59
def prefixEnd_871324 : Nat := 4983230072969 + 3 ^ 40 * 871324 * 2
def baseEnd_871324 : Nat := 132565338606890125790477

theorem tailTrace_871324 : CollatzResearch.WordTrace tailWord_871324 prefixEnd_871324 132565338606890125790477 := by
  unfold tailWord_871324
  simp only [CollatzResearch.WordTrace]
  refine ⟨15889898547674716568458513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21186531396899622091278017 15889898547674716568458513)
  ·
    refine ⟨11917423910756037426343885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15889898547674716568458513 11917423910756037426343885)
    ·
      refine ⟨4469033966533514034878957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11917423910756037426343885 4469033966533514034878957)
      ·
        refine ⟨1675887737450067763079609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4469033966533514034878957 1675887737450067763079609)
        ·
          refine ⟨1256915803087550822309707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1675887737450067763079609 1256915803087550822309707)
          ·
            refine ⟨1885373704631326233464561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256915803087550822309707 1885373704631326233464561)
            ·
              refine ⟨1414030278473494675098421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885373704631326233464561 1414030278473494675098421)
              ·
                refine ⟨132565338606890125790477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1414030278473494675098421 132565338606890125790477)
                ·
                  rfl

theorem cell20_871324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_871324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871324 prefixEnd_871324 := by exact prefixLift 871324
  have htrace : WordTrace (prefixWord ++ tailWord_871324) baseStart_871324 baseEnd_871324 := by
    simpa [prefixWord, tailWord_871324, baseEnd_871324] using wordTrace_append hprefix tailTrace_871324
  have hstable : (prefixWord ++ tailWord_871324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871324).length < 2 ^ (prefixWord ++ tailWord_871324).sum := by decide
  have hdescent : baseEnd_871324 < baseStart_871324 := by decide
  rcases family_descends (prefixWord ++ tailWord_871324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871328 : List Nat := [2, 1, 1, 4, 1, 1, 3, 7]
def baseStart_871328 : Nat := 118140960795 + 871328 * 2 ^ 59
def prefixEnd_871328 : Nat := 4983230072969 + 3 ^ 40 * 871328 * 2
def baseEnd_871328 : Nat := 132565947176554713746027

theorem tailTrace_871328 : CollatzResearch.WordTrace tailWord_871328 prefixEnd_871328 132565947176554713746027 := by
  unfold tailWord_871328
  simp only [CollatzResearch.WordTrace]
  refine ⟨15889971493667470910031319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21186628658223294546708425 15889971493667470910031319)
  ·
    refine ⟨23834957240501206365046979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15889971493667470910031319 23834957240501206365046979)
    ·
      refine ⟨35752435860751809547570469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23834957240501206365046979 35752435860751809547570469)
      ·
        refine ⟨6703581723890964290169463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35752435860751809547570469 6703581723890964290169463)
        ·
          refine ⟨10055372585836446435254195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703581723890964290169463 10055372585836446435254195)
          ·
            refine ⟨15083058878754669652881293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10055372585836446435254195 15083058878754669652881293)
            ·
              refine ⟨5656147079533001119830485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15083058878754669652881293 5656147079533001119830485)
              ·
                refine ⟨132565947176554713746027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5656147079533001119830485 132565947176554713746027)
                ·
                  rfl

theorem cell20_871328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_871328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871328 prefixEnd_871328 := by exact prefixLift 871328
  have htrace : WordTrace (prefixWord ++ tailWord_871328) baseStart_871328 baseEnd_871328 := by
    simpa [prefixWord, tailWord_871328, baseEnd_871328] using wordTrace_append hprefix tailTrace_871328
  have hstable : (prefixWord ++ tailWord_871328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871328).length < 2 ^ (prefixWord ++ tailWord_871328).sum := by decide
  have hdescent : baseEnd_871328 < baseStart_871328 := by decide
  rcases family_descends (prefixWord ++ tailWord_871328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871331 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 3]
def baseStart_871331 : Nat := 118140960795 + 871331 * 2 ^ 59
def prefixEnd_871331 : Nat := 4983230072969 + 3 ^ 40 * 871331 * 2
def baseEnd_871331 : Nat := 397699210811409464138069

theorem tailTrace_871331 : CollatzResearch.WordTrace tailWord_871331 prefixEnd_871331 397699210811409464138069 := by
  unfold tailWord_871331
  simp only [CollatzResearch.WordTrace]
  refine ⟨31780052406324073332421847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21186701604216048888281231 31780052406324073332421847)
  ·
    refine ⟨47670078609486109998632771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31780052406324073332421847 47670078609486109998632771)
    ·
      refine ⟨71505117914229164997949157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47670078609486109998632771 71505117914229164997949157)
      ·
        refine ⟨13407209608917968437115467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71505117914229164997949157 13407209608917968437115467)
        ·
          refine ⟨20110814413376952655673201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13407209608917968437115467 20110814413376952655673201)
          ·
            refine ⟨15083110810032714491754901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20110814413376952655673201 15083110810032714491754901)
            ·
              refine ⟨707020819220283491801011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15083110810032714491754901 707020819220283491801011)
              ·
                refine ⟨1060531228830425237701517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707020819220283491801011 1060531228830425237701517)
                ·
                  refine ⟨397699210811409464138069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060531228830425237701517 397699210811409464138069)
                  ·
                    rfl

theorem cell20_871331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 3].length) (baseStart_871331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871331 prefixEnd_871331 := by exact prefixLift 871331
  have htrace : WordTrace (prefixWord ++ tailWord_871331) baseStart_871331 baseEnd_871331 := by
    simpa [prefixWord, tailWord_871331, baseEnd_871331] using wordTrace_append hprefix tailTrace_871331
  have hstable : (prefixWord ++ tailWord_871331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871331).length < 2 ^ (prefixWord ++ tailWord_871331).sum := by decide
  have hdescent : baseEnd_871331 < baseStart_871331 := by decide
  rcases family_descends (prefixWord ++ tailWord_871331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871435 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_871435 : Nat := 118140960795 + 871435 * 2 ^ 59
def prefixEnd_871435 : Nat := 4983230072969 + 3 ^ 40 * 871435 * 2
def baseEnd_871435 : Nat := 397746679245247324670977

theorem tailTrace_871435 : CollatzResearch.WordTrace tailWord_871435 prefixEnd_871435 397746679245247324670977 := by
  unfold tailWord_871435
  simp only [CollatzResearch.WordTrace]
  refine ⟨31783845597947299094207759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21189230398631532729471839 31783845597947299094207759)
  ·
    refine ⟨47675768396920948641311639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31783845597947299094207759 47675768396920948641311639)
    ·
      refine ⟨71513652595381422961967459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47675768396920948641311639 71513652595381422961967459)
      ·
        refine ⟨107270478893072134442951189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71513652595381422961967459 107270478893072134442951189)
        ·
          refine ⟨5028303698112756302013337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107270478893072134442951189 5028303698112756302013337)
          ·
            refine ⟨3771227773584567226510003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5028303698112756302013337 3771227773584567226510003)
            ·
              refine ⟨5656841660376850839765005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771227773584567226510003 5656841660376850839765005)
              ·
                refine ⟨2121315622641319064911877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5656841660376850839765005 2121315622641319064911877)
                ·
                  refine ⟨397746679245247324670977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2121315622641319064911877 397746679245247324670977)
                  ·
                    rfl

theorem cell20_871435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_871435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871435 prefixEnd_871435 := by exact prefixLift 871435
  have htrace : WordTrace (prefixWord ++ tailWord_871435) baseStart_871435 baseEnd_871435 := by
    simpa [prefixWord, tailWord_871435, baseEnd_871435] using wordTrace_append hprefix tailTrace_871435
  have hstable : (prefixWord ++ tailWord_871435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871435).length < 2 ^ (prefixWord ++ tailWord_871435).sum := by decide
  have hdescent : baseEnd_871435 < baseStart_871435 := by decide
  rcases family_descends (prefixWord ++ tailWord_871435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871459 : List Nat := [1, 1, 1, 4, 3, 2, 4, 4]
def baseStart_871459 : Nat := 118140960795 + 871459 * 2 ^ 59
def prefixEnd_871459 : Nat := 4983230072969 + 3 ^ 40 * 871459 * 2
def baseEnd_871459 : Nat := 132585877833069969290293

theorem tailTrace_871459 : CollatzResearch.WordTrace tailWord_871459 prefixEnd_871459 132585877833069969290293 := by
  unfold tailWord_871459
  simp only [CollatzResearch.WordTrace]
  refine ⟨31784720949860351193081431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21189813966573567462054287 31784720949860351193081431)
  ·
    refine ⟨47677081424790526789622147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31784720949860351193081431 47677081424790526789622147)
    ·
      refine ⟨71515622137185790184433221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47677081424790526789622147 71515622137185790184433221)
      ·
        refine ⟨13409179150722335659581229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71515622137185790184433221 13409179150722335659581229)
        ·
          refine ⟨5028442181520875872342961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13409179150722335659581229 5028442181520875872342961)
          ·
            refine ⟨3771331636140656904257221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5028442181520875872342961 3771331636140656904257221)
            ·
              refine ⟨707124681776373169548229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3771331636140656904257221 707124681776373169548229)
              ·
                refine ⟨132585877833069969290293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 707124681776373169548229 132585877833069969290293)
                ·
                  rfl

theorem cell20_871459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 4].length) (baseStart_871459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871459 prefixEnd_871459 := by exact prefixLift 871459
  have htrace : WordTrace (prefixWord ++ tailWord_871459) baseStart_871459 baseEnd_871459 := by
    simpa [prefixWord, tailWord_871459, baseEnd_871459] using wordTrace_append hprefix tailTrace_871459
  have hstable : (prefixWord ++ tailWord_871459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871459).length < 2 ^ (prefixWord ++ tailWord_871459).sum := by decide
  have hdescent : baseEnd_871459 < baseStart_871459 := by decide
  rcases family_descends (prefixWord ++ tailWord_871459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871476 : List Nat := [2, 5, 1, 2, 1, 3, 6]
def baseStart_871476 : Nat := 118140960795 + 871476 * 2 ^ 59
def prefixEnd_871476 : Nat := 4983230072969 + 3 ^ 40 * 871476 * 2
def baseEnd_871476 : Nat := 44196154751381489367127

theorem tailTrace_871476 : CollatzResearch.WordTrace tailWord_871476 prefixEnd_871476 44196154751381489367127 := by
  unfold tailWord_871476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15892670495399381548225141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21190227327199175397633521 15892670495399381548225141)
  ·
    refine ⟨1489937858943692020146107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15892670495399381548225141 1489937858943692020146107)
    ·
      refine ⟨2234906788415538030219161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1489937858943692020146107 2234906788415538030219161)
      ·
        refine ⟨1676180091311653522664371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2234906788415538030219161 1676180091311653522664371)
        ·
          refine ⟨2514270136967480283996557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676180091311653522664371 2514270136967480283996557)
          ·
            refine ⟨942851301362805106498709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2514270136967480283996557 942851301362805106498709)
            ·
              refine ⟨44196154751381489367127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 942851301362805106498709 44196154751381489367127)
              ·
                rfl

theorem cell20_871476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 6].length) (baseStart_871476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871476 prefixEnd_871476 := by exact prefixLift 871476
  have htrace : WordTrace (prefixWord ++ tailWord_871476) baseStart_871476 baseEnd_871476 := by
    simpa [prefixWord, tailWord_871476, baseEnd_871476] using wordTrace_append hprefix tailTrace_871476
  have hstable : (prefixWord ++ tailWord_871476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871476).length < 2 ^ (prefixWord ++ tailWord_871476).sum := by decide
  have hdescent : baseEnd_871476 < baseStart_871476 := by decide
  rcases family_descends (prefixWord ++ tailWord_871476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871480 : List Nat := [2, 1, 2, 1, 5, 1, 8]
def baseStart_871480 : Nat := 118140960795 + 871480 * 2 ^ 59
def prefixEnd_871480 : Nat := 4983230072969 + 3 ^ 40 * 871480 * 2
def baseEnd_871480 : Nat := 44196357607936352018977

theorem tailTrace_871480 : CollatzResearch.WordTrace tailWord_871480 prefixEnd_871480 44196357607936352018977 := by
  unfold tailWord_871480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15892743441392135889797947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21190324588522847853063929 15892743441392135889797947)
  ·
    refine ⟨23839115162088203834696921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15892743441392135889797947 23839115162088203834696921)
    ·
      refine ⟨17879336371566152876022691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23839115162088203834696921 17879336371566152876022691)
      ·
        refine ⟨26819004557349229314034037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17879336371566152876022691 26819004557349229314034037)
        ·
          refine ⟨2514281677251490248190691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26819004557349229314034037 2514281677251490248190691)
          ·
            refine ⟨3771422515877235372286037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514281677251490248190691 3771422515877235372286037)
            ·
              refine ⟨44196357607936352018977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3771422515877235372286037 44196357607936352018977)
              ·
                rfl

theorem cell20_871480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 8].length) (baseStart_871480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871480 prefixEnd_871480 := by exact prefixLift 871480
  have htrace : WordTrace (prefixWord ++ tailWord_871480) baseStart_871480 baseEnd_871480 := by
    simpa [prefixWord, tailWord_871480, baseEnd_871480] using wordTrace_append hprefix tailTrace_871480
  have hstable : (prefixWord ++ tailWord_871480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871480).length < 2 ^ (prefixWord ++ tailWord_871480).sum := by decide
  have hdescent : baseEnd_871480 < baseStart_871480 := by decide
  rcases family_descends (prefixWord ++ tailWord_871480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871545 : List Nat := [1, 2, 1, 3, 5, 1, 1, 4, 2]
def baseStart_871545 : Nat := 118140960795 + 871545 * 2 ^ 59
def prefixEnd_871545 : Nat := 4983230072969 + 3 ^ 40 * 871545 * 2
def baseEnd_871545 : Nat := 397796886242575831003861

theorem tailTrace_871545 : CollatzResearch.WordTrace tailWord_871545 prefixEnd_871545 397796886242575831003861 := by
  unfold tailWord_871545
  simp only [CollatzResearch.WordTrace]
  refine ⟨31787857627548787880712089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21191905085032525253808059 31787857627548787880712089)
  ·
    refine ⟨23840893220661590910534067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31787857627548787880712089 23840893220661590910534067)
    ·
      refine ⟨35761339830992386365801101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23840893220661590910534067 35761339830992386365801101)
      ·
        refine ⟨13410502436622144887175413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35761339830992386365801101 13410502436622144887175413)
        ·
          refine ⟨1257234603433326083172695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13410502436622144887175413 1257234603433326083172695)
          ·
            refine ⟨1885851905149989124759043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257234603433326083172695 1885851905149989124759043)
            ·
              refine ⟨2828777857724983687138565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885851905149989124759043 2828777857724983687138565)
              ·
                refine ⟨530395848323434441338481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2828777857724983687138565 530395848323434441338481)
                ·
                  refine ⟨397796886242575831003861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530395848323434441338481 397796886242575831003861)
                  ·
                    rfl

theorem cell20_871545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_871545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871545 prefixEnd_871545 := by exact prefixLift 871545
  have htrace : WordTrace (prefixWord ++ tailWord_871545) baseStart_871545 baseEnd_871545 := by
    simpa [prefixWord, tailWord_871545, baseEnd_871545] using wordTrace_append hprefix tailTrace_871545
  have hstable : (prefixWord ++ tailWord_871545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871545).length < 2 ^ (prefixWord ++ tailWord_871545).sum := by decide
  have hdescent : baseEnd_871545 < baseStart_871545 := by decide
  rcases family_descends (prefixWord ++ tailWord_871545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871549 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_871549 : Nat := 118140960795 + 871549 * 2 ^ 59
def prefixEnd_871549 : Nat := 4983230072969 + 3 ^ 40 * 871549 * 2
def baseEnd_871549 : Nat := 397798711951569594870511

theorem tailTrace_871549 : CollatzResearch.WordTrace tailWord_871549 prefixEnd_871549 397798711951569594870511 := by
  unfold tailWord_871549
  simp only [CollatzResearch.WordTrace]
  refine ⟨31788003519534296563857701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21192002346356197709238467 31788003519534296563857701)
  ·
    refine ⟨5960250659912680605723319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31788003519534296563857701 5960250659912680605723319)
    ·
      refine ⟨8940375989869020908584979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5960250659912680605723319 8940375989869020908584979)
      ·
        refine ⟨13410563984803531362877469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8940375989869020908584979 13410563984803531362877469)
        ·
          refine ⟨5028961494301324261079051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13410563984803531362877469 5028961494301324261079051)
          ·
            refine ⟨7543442241451986391618577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5028961494301324261079051 7543442241451986391618577)
            ·
              refine ⟨5657581681088989793713933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7543442241451986391618577 5657581681088989793713933)
              ·
                refine ⟨2121593130408371172642725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5657581681088989793713933 2121593130408371172642725)
                ·
                  refine ⟨397798711951569594870511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2121593130408371172642725 397798711951569594870511)
                  ·
                    rfl

theorem cell20_871549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_871549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871549 prefixEnd_871549 := by exact prefixLift 871549
  have htrace : WordTrace (prefixWord ++ tailWord_871549) baseStart_871549 baseEnd_871549 := by
    simpa [prefixWord, tailWord_871549, baseEnd_871549] using wordTrace_append hprefix tailTrace_871549
  have hstable : (prefixWord ++ tailWord_871549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871549).length < 2 ^ (prefixWord ++ tailWord_871549).sum := by decide
  have hdescent : baseEnd_871549 < baseStart_871549 := by decide
  rcases family_descends (prefixWord ++ tailWord_871549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871566 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_871566 : Nat := 118140960795 + 871566 * 2 ^ 59
def prefixEnd_871566 : Nat := 4983230072969 + 3 ^ 40 * 871566 * 2
def baseEnd_871566 : Nat := 397806471214793091303775

theorem tailTrace_871566 : CollatzResearch.WordTrace tailWord_871566 prefixEnd_871566 397806471214793091303775 := by
  unfold tailWord_871566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973577945059088558403319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21192415706981805644817701 3973577945059088558403319)
  ·
    refine ⟨5960366917588632837604979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3973577945059088558403319 5960366917588632837604979)
    ·
      refine ⟨8940550376382949256407469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5960366917588632837604979 8940550376382949256407469)
      ·
        refine ⟨3352706391143605971152801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8940550376382949256407469 3352706391143605971152801)
        ·
          refine ⟨2514529793357704478364601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3352706391143605971152801 2514529793357704478364601)
          ·
            refine ⟨1885897345018278358773451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514529793357704478364601 1885897345018278358773451)
            ·
              refine ⟨2828846017527417538160177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885897345018278358773451 2828846017527417538160177)
              ·
                refine ⟨2121634513145563153620133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2828846017527417538160177 2121634513145563153620133)
                ·
                  refine ⟨397806471214793091303775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2121634513145563153620133 397806471214793091303775)
                  ·
                    rfl

theorem cell20_871566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_871566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871566 prefixEnd_871566 := by exact prefixLift 871566
  have htrace : WordTrace (prefixWord ++ tailWord_871566) baseStart_871566 baseEnd_871566 := by
    simpa [prefixWord, tailWord_871566, baseEnd_871566] using wordTrace_append hprefix tailTrace_871566
  have hstable : (prefixWord ++ tailWord_871566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871566).length < 2 ^ (prefixWord ++ tailWord_871566).sum := by decide
  have hdescent : baseEnd_871566 < baseStart_871566 := by decide
  rcases family_descends (prefixWord ++ tailWord_871566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871597 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 5]
def baseStart_871597 : Nat := 118140960795 + 871597 * 2 ^ 59
def prefixEnd_871597 : Nat := 4983230072969 + 3 ^ 40 * 871597 * 2
def baseEnd_871597 : Nat := 397820620459494761270315

theorem tailTrace_871597 : CollatzResearch.WordTrace tailWord_871597 prefixEnd_871597 397820620459494761270315 := by
  unfold tailWord_871597
  simp only [CollatzResearch.WordTrace]
  refine ⟨31789754223360400761605045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21193169482240267174403363 31789754223360400761605045)
  ·
    refine ⟨2980289458440037571400473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31789754223360400761605045 2980289458440037571400473)
    ·
      refine ⟨2235217093830028178550355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2980289458440037571400473 2235217093830028178550355)
      ·
        refine ⟨3352825640745042267825533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235217093830028178550355 3352825640745042267825533)
        ·
          refine ⟨1257309615279390850434575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3352825640745042267825533 1257309615279390850434575)
          ·
            refine ⟨1885964422919086275651863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257309615279390850434575 1885964422919086275651863)
            ·
              refine ⟨2828946634378629413477795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885964422919086275651863 2828946634378629413477795)
              ·
                refine ⟨4243419951567944120216693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828946634378629413477795 4243419951567944120216693)
                ·
                  refine ⟨397820620459494761270315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4243419951567944120216693 397820620459494761270315)
                  ·
                    rfl

theorem cell20_871597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_871597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871597 prefixEnd_871597 := by exact prefixLift 871597
  have htrace : WordTrace (prefixWord ++ tailWord_871597) baseStart_871597 baseEnd_871597 := by
    simpa [prefixWord, tailWord_871597, baseEnd_871597] using wordTrace_append hprefix tailTrace_871597
  have hstable : (prefixWord ++ tailWord_871597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871597).length < 2 ^ (prefixWord ++ tailWord_871597).sum := by decide
  have hdescent : baseEnd_871597 < baseStart_871597 := by decide
  rcases family_descends (prefixWord ++ tailWord_871597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871614 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_871614 : Nat := 118140960795 + 871614 * 2 ^ 59
def prefixEnd_871614 : Nat := 4983230072969 + 3 ^ 40 * 871614 * 2
def baseEnd_871614 : Nat := 397828379722718257703579

theorem tailTrace_871614 : CollatzResearch.WordTrace tailWord_871614 prefixEnd_871614 397828379722718257703579 := by
  unfold tailWord_871614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973796783037351583121737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21193582842865875109982597 3973796783037351583121737)
  ·
    refine ⟨2980347587278013687341303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3973796783037351583121737 2980347587278013687341303)
    ·
      refine ⟨4470521380917020531011955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2980347587278013687341303 4470521380917020531011955)
      ·
        refine ⟨6705782071375530796517933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4470521380917020531011955 6705782071375530796517933)
        ·
          refine ⟨2514668276765824048694225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6705782071375530796517933 2514668276765824048694225)
          ·
            refine ⟨1886001207574368036520669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514668276765824048694225 1886001207574368036520669)
            ·
              refine ⟨707250452840388013695251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1886001207574368036520669 707250452840388013695251)
              ·
                refine ⟨1060875679260582020542877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707250452840388013695251 1060875679260582020542877)
                ·
                  refine ⟨397828379722718257703579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060875679260582020542877 397828379722718257703579)
                  ·
                    rfl

theorem cell20_871614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_871614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871614 prefixEnd_871614 := by exact prefixLift 871614
  have htrace : WordTrace (prefixWord ++ tailWord_871614) baseStart_871614 baseEnd_871614 := by
    simpa [prefixWord, tailWord_871614, baseEnd_871614] using wordTrace_append hprefix tailTrace_871614
  have hstable : (prefixWord ++ tailWord_871614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871614).length < 2 ^ (prefixWord ++ tailWord_871614).sum := by decide
  have hdescent : baseEnd_871614 < baseStart_871614 := by decide
  rcases family_descends (prefixWord ++ tailWord_871614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871639 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_871639 : Nat := 118140960795 + 871639 * 2 ^ 59
def prefixEnd_871639 : Nat := 4983230072969 + 3 ^ 40 * 871639 * 2
def baseEnd_871639 : Nat := 397839790403929281870143

theorem tailTrace_871639 : CollatzResearch.WordTrace tailWord_871639 prefixEnd_871639 397839790403929281870143 := by
  unfold tailWord_871639
  simp only [CollatzResearch.WordTrace]
  refine ⟨31791286089208241934633971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21194190726138827956422647 31791286089208241934633971)
  ·
    refine ⟨47686929133812362901950957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31791286089208241934633971 47686929133812362901950957)
    ·
      refine ⟨17882598425179636088231609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47686929133812362901950957 17882598425179636088231609)
      ·
        refine ⟨13411948818884727066173707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17882598425179636088231609 13411948818884727066173707)
        ·
          refine ⟨20117923228327090599260561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13411948818884727066173707 20117923228327090599260561)
          ·
            refine ⟨15088442421245317949445421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20117923228327090599260561 15088442421245317949445421)
            ·
              refine ⟨5658165907966994231042033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15088442421245317949445421 5658165907966994231042033)
              ·
                refine ⟨4243624430975245673281525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5658165907966994231042033 4243624430975245673281525)
                ·
                  refine ⟨397839790403929281870143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4243624430975245673281525 397839790403929281870143)
                  ·
                    rfl

theorem cell20_871639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_871639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871639 prefixEnd_871639 := by exact prefixLift 871639
  have htrace : WordTrace (prefixWord ++ tailWord_871639) baseStart_871639 baseEnd_871639 := by
    simpa [prefixWord, tailWord_871639, baseEnd_871639] using wordTrace_append hprefix tailTrace_871639
  have hstable : (prefixWord ++ tailWord_871639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871639).length < 2 ^ (prefixWord ++ tailWord_871639).sum := by decide
  have hdescent : baseEnd_871639 < baseStart_871639 := by decide
  rcases family_descends (prefixWord ++ tailWord_871639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871656 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_871656 : Nat := 118140960795 + 871656 * 2 ^ 59
def prefixEnd_871656 : Nat := 4983230072969 + 3 ^ 40 * 871656 * 2
def baseEnd_871656 : Nat := 397847549667152778303407

theorem tailTrace_871656 : CollatzResearch.WordTrace tailWord_871656 prefixEnd_871656 397847549667152778303407 := by
  unfold tailWord_871656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15895953065073326919001411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21194604086764435892001881 15895953065073326919001411)
  ·
    refine ⟨23843929597609990378502117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15895953065073326919001411 23843929597609990378502117)
    ·
      refine ⟨4470736799551873195969147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23843929597609990378502117 4470736799551873195969147)
      ·
        refine ⟨6706105199327809793953721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4470736799551873195969147 6706105199327809793953721)
        ·
          refine ⟨5029578899495857345465291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6706105199327809793953721 5029578899495857345465291)
          ·
            refine ⟨7544368349243786018197937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029578899495857345465291 7544368349243786018197937)
            ·
              refine ⟨5658276261932839513648453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7544368349243786018197937 5658276261932839513648453)
              ·
                refine ⟨1060926799112407408809085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5658276261932839513648453 1060926799112407408809085)
                ·
                  refine ⟨397847549667152778303407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060926799112407408809085 397847549667152778303407)
                  ·
                    rfl

theorem cell20_871656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_871656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871656 prefixEnd_871656 := by exact prefixLift 871656
  have htrace : WordTrace (prefixWord ++ tailWord_871656) baseStart_871656 baseEnd_871656 := by
    simpa [prefixWord, tailWord_871656, baseEnd_871656] using wordTrace_append hprefix tailTrace_871656
  have hstable : (prefixWord ++ tailWord_871656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871656).length < 2 ^ (prefixWord ++ tailWord_871656).sum := by decide
  have hdescent : baseEnd_871656 < baseStart_871656 := by decide
  rcases family_descends (prefixWord ++ tailWord_871656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871659 : List Nat := [1, 1, 1, 1, 2, 7, 3, 2, 2]
def baseStart_871659 : Nat := 118140960795 + 871659 * 2 ^ 59
def prefixEnd_871659 : Nat := 4983230072969 + 3 ^ 40 * 871659 * 2
def baseEnd_871659 : Nat := 397848918948898101203395

theorem tailTrace_871659 : CollatzResearch.WordTrace tailWord_871659 prefixEnd_871659 397848918948898101203395 := by
  unfold tailWord_871659
  simp only [CollatzResearch.WordTrace]
  refine ⟨31792015549135785350362031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21194677032757190233574687 31792015549135785350362031)
  ·
    refine ⟨47688023323703678025543047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31792015549135785350362031 47688023323703678025543047)
    ·
      refine ⟨71532034985555517038314571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47688023323703678025543047 71532034985555517038314571)
      ·
        refine ⟨107298052478333275557471857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71532034985555517038314571 107298052478333275557471857)
        ·
          refine ⟨80473539358749956668103893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107298052478333275557471857 80473539358749956668103893)
          ·
            refine ⟨1886098578720702109408685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 80473539358749956668103893 1886098578720702109408685)
            ·
              refine ⟨707286967020263291028257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1886098578720702109408685 707286967020263291028257)
              ·
                refine ⟨530465225265197468271193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707286967020263291028257 530465225265197468271193)
                ·
                  refine ⟨397848918948898101203395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530465225265197468271193 397848918948898101203395)
                  ·
                    rfl

theorem cell20_871659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 2].length) (baseStart_871659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871659 prefixEnd_871659 := by exact prefixLift 871659
  have htrace : WordTrace (prefixWord ++ tailWord_871659) baseStart_871659 baseEnd_871659 := by
    simpa [prefixWord, tailWord_871659, baseEnd_871659] using wordTrace_append hprefix tailTrace_871659
  have hstable : (prefixWord ++ tailWord_871659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871659).length < 2 ^ (prefixWord ++ tailWord_871659).sum := by decide
  have hdescent : baseEnd_871659 < baseStart_871659 := by decide
  rcases family_descends (prefixWord ++ tailWord_871659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871710 : List Nat := [4, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_871710 : Nat := 118140960795 + 871710 * 2 ^ 59
def prefixEnd_871710 : Nat := 4983230072969 + 3 ^ 40 * 871710 * 2
def baseEnd_871710 : Nat := 397872196738568590503187

theorem tailTrace_871710 : CollatzResearch.WordTrace tailWord_871710 prefixEnd_871710 397872196738568590503187 := by
  unfold tailWord_871710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974234458993877632558573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21195917114634014040312389 3974234458993877632558573)
  ·
    refine ⟨1490337922122704112209465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3974234458993877632558573 1490337922122704112209465)
    ·
      refine ⟨1117753441592028084157099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1490337922122704112209465 1117753441592028084157099)
      ·
        refine ⟨1676630162388042126235649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117753441592028084157099 1676630162388042126235649)
        ·
          refine ⟨1257472621791031594676737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676630162388042126235649 1257472621791031594676737)
          ·
            refine ⟨943104466343273696007553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257472621791031594676737 943104466343273696007553)
            ·
              refine ⟨707328349757455272005665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943104466343273696007553 707328349757455272005665)
              ·
                refine ⟨530496262318091454004249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707328349757455272005665 530496262318091454004249)
                ·
                  refine ⟨397872196738568590503187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530496262318091454004249 397872196738568590503187)
                  ·
                    rfl

theorem cell20_871710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_871710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871710 prefixEnd_871710 := by exact prefixLift 871710
  have htrace : WordTrace (prefixWord ++ tailWord_871710) baseStart_871710 baseEnd_871710 := by
    simpa [prefixWord, tailWord_871710, baseEnd_871710] using wordTrace_append hprefix tailTrace_871710
  have hstable : (prefixWord ++ tailWord_871710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871710).length < 2 ^ (prefixWord ++ tailWord_871710).sum := by decide
  have hdescent : baseEnd_871710 < baseStart_871710 := by decide
  rcases family_descends (prefixWord ++ tailWord_871710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871711 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 3]
def baseStart_871711 : Nat := 118140960795 + 871711 * 2 ^ 59
def prefixEnd_871711 : Nat := 4983230072969 + 3 ^ 40 * 871711 * 2
def baseEnd_871711 : Nat := 397872653165817031469849

theorem tailTrace_871711 : CollatzResearch.WordTrace tailWord_871711 prefixEnd_871711 397872653165817031469849 := by
  unfold tailWord_871711
  simp only [CollatzResearch.WordTrace]
  refine ⟨31793912144947398231254987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21195941429964932154169991 31793912144947398231254987)
  ·
    refine ⟨47690868217421097346882481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31793912144947398231254987 47690868217421097346882481)
    ·
      refine ⟨35768151163065823010161861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47690868217421097346882481 35768151163065823010161861)
      ·
        refine ⟨6706528343074841814405349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35768151163065823010161861 6706528343074841814405349)
        ·
          refine ⟨1257474064326532840201003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6706528343074841814405349 1257474064326532840201003)
          ·
            refine ⟨1886211096489799260301505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257474064326532840201003 1886211096489799260301505)
            ·
              refine ⟨1414658322367349445226129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1886211096489799260301505 1414658322367349445226129)
              ·
                refine ⟨1060993741775512083919597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414658322367349445226129 1060993741775512083919597)
                ·
                  refine ⟨397872653165817031469849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060993741775512083919597 397872653165817031469849)
                  ·
                    rfl

theorem cell20_871711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_871711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871711 prefixEnd_871711 := by exact prefixLift 871711
  have htrace : WordTrace (prefixWord ++ tailWord_871711) baseStart_871711 baseEnd_871711 := by
    simpa [prefixWord, tailWord_871711, baseEnd_871711] using wordTrace_append hprefix tailTrace_871711
  have hstable : (prefixWord ++ tailWord_871711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871711).length < 2 ^ (prefixWord ++ tailWord_871711).sum := by decide
  have hdescent : baseEnd_871711 < baseStart_871711 := by decide
  rcases family_descends (prefixWord ++ tailWord_871711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871756 : List Nat := [2, 2, 1, 3, 2, 2, 1, 5, 2]
def baseStart_871756 : Nat := 118140960795 + 871756 * 2 ^ 59
def prefixEnd_871756 : Nat := 4983230072969 + 3 ^ 40 * 871756 * 2
def baseEnd_871756 : Nat := 397893192391996874969665

theorem tailTrace_871756 : CollatzResearch.WordTrace tailWord_871756 prefixEnd_871756 397893192391996874969665 := by
  unfold tailWord_871756
  simp only [CollatzResearch.WordTrace]
  refine ⟨15897776714892185458321561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21197035619856247277762081 15897776714892185458321561)
  ·
    refine ⟨11923332536169139093741171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15897776714892185458321561 11923332536169139093741171)
    ·
      refine ⟨17884998804253708640611757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11923332536169139093741171 17884998804253708640611757)
      ·
        refine ⟨6706874551595140740229409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17884998804253708640611757 6706874551595140740229409)
        ·
          refine ⟨5030155913696355555172057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6706874551595140740229409 5030155913696355555172057)
          ·
            refine ⟨3772616935272266666379043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030155913696355555172057 3772616935272266666379043)
            ·
              refine ⟨5658925402908399999568565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772616935272266666379043 5658925402908399999568565)
              ·
                refine ⟨530524256522662499959553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5658925402908399999568565 530524256522662499959553)
                ·
                  refine ⟨397893192391996874969665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530524256522662499959553 397893192391996874969665)
                  ·
                    rfl

theorem cell20_871756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_871756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871756 prefixEnd_871756 := by exact prefixLift 871756
  have htrace : WordTrace (prefixWord ++ tailWord_871756) baseStart_871756 baseEnd_871756 := by
    simpa [prefixWord, tailWord_871756, baseEnd_871756] using wordTrace_append hprefix tailTrace_871756
  have hstable : (prefixWord ++ tailWord_871756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871756).length < 2 ^ (prefixWord ++ tailWord_871756).sum := by decide
  have hdescent : baseEnd_871756 < baseStart_871756 := by decide
  rcases family_descends (prefixWord ++ tailWord_871756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871760 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_871760 : Nat := 118140960795 + 871760 * 2 ^ 59
def prefixEnd_871760 : Nat := 4983230072969 + 3 ^ 40 * 871760 * 2
def baseEnd_871760 : Nat := 397895018100990638836315

theorem tailTrace_871760 : CollatzResearch.WordTrace tailWord_871760 prefixEnd_871760 397895018100990638836315 := by
  unfold tailWord_871760
  simp only [CollatzResearch.WordTrace]
  refine ⟨15897849660884939799894367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21197132881179919733192489 15897849660884939799894367)
  ·
    refine ⟨23846774491327409699841551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15897849660884939799894367 23846774491327409699841551)
    ·
      refine ⟨35770161736991114549762327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23846774491327409699841551 35770161736991114549762327)
      ·
        refine ⟨53655242605486671824643491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35770161736991114549762327 53655242605486671824643491)
        ·
          refine ⟨80482863908230007736965237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53655242605486671824643491 80482863908230007736965237)
          ·
            refine ⟨7545268491396563225340491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80482863908230007736965237 7545268491396563225340491)
            ·
              refine ⟨11317902737094844838010737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7545268491396563225340491 11317902737094844838010737)
              ·
                refine ⟨8488427052821133628508053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11317902737094844838010737 8488427052821133628508053)
                ·
                  refine ⟨397895018100990638836315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8488427052821133628508053 397895018100990638836315)
                  ·
                    rfl

theorem cell20_871760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_871760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871760 prefixEnd_871760 := by exact prefixLift 871760
  have htrace : WordTrace (prefixWord ++ tailWord_871760) baseStart_871760 baseEnd_871760 := by
    simpa [prefixWord, tailWord_871760, baseEnd_871760] using wordTrace_append hprefix tailTrace_871760
  have hstable : (prefixWord ++ tailWord_871760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871760).length < 2 ^ (prefixWord ++ tailWord_871760).sum := by decide
  have hdescent : baseEnd_871760 < baseStart_871760 := by decide
  rcases family_descends (prefixWord ++ tailWord_871760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871770 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_871770 : Nat := 118140960795 + 871770 * 2 ^ 59
def prefixEnd_871770 : Nat := 4983230072969 + 3 ^ 40 * 871770 * 2
def baseEnd_871770 : Nat := 397899582373475048502941

theorem tailTrace_871770 : CollatzResearch.WordTrace tailWord_871770 prefixEnd_871770 397899582373475048502941 := by
  unfold tailWord_871770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949016012933412826913191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21197376034489100871768509 7949016012933412826913191)
  ·
    refine ⟨11923524019400119240369787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7949016012933412826913191 11923524019400119240369787)
    ·
      refine ⟨17885286029100178860554681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11923524019400119240369787 17885286029100178860554681)
      ·
        refine ⟨13413964521825134145416011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17885286029100178860554681 13413964521825134145416011)
        ·
          refine ⟨20120946782737701218124017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13413964521825134145416011 20120946782737701218124017)
          ·
            refine ⟨15090710087053275913593013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20120946782737701218124017 15090710087053275913593013)
            ·
              refine ⟨1414754070661244616899345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15090710087053275913593013 1414754070661244616899345)
              ·
                refine ⟨1061065552995933462674509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414754070661244616899345 1061065552995933462674509)
                ·
                  refine ⟨397899582373475048502941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061065552995933462674509 397899582373475048502941)
                  ·
                    rfl

theorem cell20_871770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_871770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871770 prefixEnd_871770 := by exact prefixLift 871770
  have htrace : WordTrace (prefixWord ++ tailWord_871770) baseStart_871770 baseEnd_871770 := by
    simpa [prefixWord, tailWord_871770, baseEnd_871770] using wordTrace_append hprefix tailTrace_871770
  have hstable : (prefixWord ++ tailWord_871770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871770).length < 2 ^ (prefixWord ++ tailWord_871770).sum := by decide
  have hdescent : baseEnd_871770 < baseStart_871770 := by decide
  rcases family_descends (prefixWord ++ tailWord_871770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871797 : List Nat := [1, 3, 4, 1, 4, 1, 2, 4]
def baseStart_871797 : Nat := 118140960795 + 871797 * 2 ^ 59
def prefixEnd_871797 : Nat := 4983230072969 + 3 ^ 40 * 871797 * 2
def baseEnd_871797 : Nat := 132637301969727651534277

theorem tailTrace_871797 : CollatzResearch.WordTrace tailWord_871797 prefixEnd_871797 132637301969727651534277 := by
  unfold tailWord_871797
  simp only [CollatzResearch.WordTrace]
  refine ⟨31797048822635834918885645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21198032548423889945923763 31797048822635834918885645)
  ·
    refine ⟨11923893308488438094582117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31797048822635834918885645 11923893308488438094582117)
    ·
      refine ⟨2235729995341582142734147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11923893308488438094582117 2235729995341582142734147)
      ·
        refine ⟨3353594993012373214101221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235729995341582142734147 3353594993012373214101221)
        ·
          refine ⟨628799061189819977643979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3353594993012373214101221 628799061189819977643979)
          ·
            refine ⟨943198591784729966465969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628799061189819977643979 943198591784729966465969)
            ·
              refine ⟨707398943838547474849477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943198591784729966465969 707398943838547474849477)
              ·
                refine ⟨132637301969727651534277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 707398943838547474849477 132637301969727651534277)
                ·
                  rfl

theorem cell20_871797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 4].length) (baseStart_871797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871797 prefixEnd_871797 := by exact prefixLift 871797
  have htrace : WordTrace (prefixWord ++ tailWord_871797) baseStart_871797 baseEnd_871797 := by
    simpa [prefixWord, tailWord_871797, baseEnd_871797] using wordTrace_append hprefix tailTrace_871797
  have hstable : (prefixWord ++ tailWord_871797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871797).length < 2 ^ (prefixWord ++ tailWord_871797).sum := by decide
  have hdescent : baseEnd_871797 < baseStart_871797 := by decide
  rcases family_descends (prefixWord ++ tailWord_871797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871811 : List Nat := [1, 1, 1, 3, 5, 3, 1, 3, 2]
def baseStart_871811 : Nat := 118140960795 + 871811 * 2 ^ 59
def prefixEnd_871811 : Nat := 4983230072969 + 3 ^ 40 * 871811 * 2
def baseEnd_871811 : Nat := 397918295890661128136107

theorem tailTrace_871811 : CollatzResearch.WordTrace tailWord_871811 prefixEnd_871811 397918295890661128136107 := by
  unfold tailWord_871811
  simp only [CollatzResearch.WordTrace]
  refine ⟨31797559444585115309895287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21198372963056743539930191 31797559444585115309895287)
  ·
    refine ⟨47696339166877672964842931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31797559444585115309895287 47696339166877672964842931)
    ·
      refine ⟨71544508750316509447264397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47696339166877672964842931 71544508750316509447264397)
      ·
        refine ⟨26829190781368691042724149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71544508750316509447264397 26829190781368691042724149)
        ·
          refine ⟨2515236635753314785255389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26829190781368691042724149 2515236635753314785255389)
          ·
            refine ⟨943213738407493044470771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2515236635753314785255389 943213738407493044470771)
            ·
              refine ⟨1414820607611239566706157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943213738407493044470771 1414820607611239566706157)
              ·
                refine ⟨530557727854214837514809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1414820607611239566706157 530557727854214837514809)
                ·
                  refine ⟨397918295890661128136107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530557727854214837514809 397918295890661128136107)
                  ·
                    rfl

theorem cell20_871811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 2].length) (baseStart_871811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871811 prefixEnd_871811 := by exact prefixLift 871811
  have htrace : WordTrace (prefixWord ++ tailWord_871811) baseStart_871811 baseEnd_871811 := by
    simpa [prefixWord, tailWord_871811, baseEnd_871811] using wordTrace_append hprefix tailTrace_871811
  have hstable : (prefixWord ++ tailWord_871811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871811).length < 2 ^ (prefixWord ++ tailWord_871811).sum := by decide
  have hdescent : baseEnd_871811 < baseStart_871811 := by decide
  rcases family_descends (prefixWord ++ tailWord_871811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871828 : List Nat := [2, 4, 2, 1, 2, 2, 3, 2, 2]
def baseStart_871828 : Nat := 118140960795 + 871828 * 2 ^ 59
def prefixEnd_871828 : Nat := 4983230072969 + 3 ^ 40 * 871828 * 2
def baseEnd_871828 : Nat := 397926055153884624569371

theorem tailTrace_871828 : CollatzResearch.WordTrace tailWord_871828 prefixEnd_871828 397926055153884624569371 := by
  unfold tailWord_871828
  simp only [CollatzResearch.WordTrace]
  refine ⟨15899089742761763606632069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21198786323682351475509425 15899089742761763606632069)
  ·
    refine ⟨2981079326767830676243513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15899089742761763606632069 2981079326767830676243513)
    ·
      refine ⟨2235809495075873007182635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2981079326767830676243513 2235809495075873007182635)
      ·
        refine ⟨3353714242613809510773953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235809495075873007182635 3353714242613809510773953)
        ·
          refine ⟨2515285681960357133080465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3353714242613809510773953 2515285681960357133080465)
          ·
            refine ⟨1886464261470267849810349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515285681960357133080465 1886464261470267849810349)
            ·
              refine ⟨707424098051350443678881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1886464261470267849810349 707424098051350443678881)
              ·
                refine ⟨530568073538512832759161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707424098051350443678881 530568073538512832759161)
                ·
                  refine ⟨397926055153884624569371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530568073538512832759161 397926055153884624569371)
                  ·
                    rfl

theorem cell20_871828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_871828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871828 prefixEnd_871828 := by exact prefixLift 871828
  have htrace : WordTrace (prefixWord ++ tailWord_871828) baseStart_871828 baseEnd_871828 := by
    simpa [prefixWord, tailWord_871828, baseEnd_871828] using wordTrace_append hprefix tailTrace_871828
  have hstable : (prefixWord ++ tailWord_871828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871828).length < 2 ^ (prefixWord ++ tailWord_871828).sum := by decide
  have hdescent : baseEnd_871828 < baseStart_871828 := by decide
  rcases family_descends (prefixWord ++ tailWord_871828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871829 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_871829 : Nat := 118140960795 + 871829 * 2 ^ 59
def prefixEnd_871829 : Nat := 4983230072969 + 3 ^ 40 * 871829 * 2
def baseEnd_871829 : Nat := 397926511581133065536033

theorem tailTrace_871829 : CollatzResearch.WordTrace tailWord_871829 prefixEnd_871829 397926511581133065536033 := by
  unfold tailWord_871829
  simp only [CollatzResearch.WordTrace]
  refine ⟨31798215958519904384050541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21198810639013269589367027 31798215958519904384050541)
  ·
    refine ⟨11924330984444964144018953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31798215958519904384050541 11924330984444964144018953)
    ·
      refine ⟨8943248238333723108014215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11924330984444964144018953 8943248238333723108014215)
      ·
        refine ⟨13414872357500584662021323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8943248238333723108014215 13414872357500584662021323)
        ·
          refine ⟨20122308536250876993031985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13414872357500584662021323 20122308536250876993031985)
          ·
            refine ⟨15091731402188157744773989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20122308536250876993031985 15091731402188157744773989)
            ·
              refine ⟨2829699637910279577145123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15091731402188157744773989 2829699637910279577145123)
              ·
                refine ⟨4244549456865419365717685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829699637910279577145123 4244549456865419365717685)
                ·
                  refine ⟨397926511581133065536033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4244549456865419365717685 397926511581133065536033)
                  ·
                    rfl

theorem cell20_871829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_871829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871829 prefixEnd_871829 := by exact prefixLift 871829
  have htrace : WordTrace (prefixWord ++ tailWord_871829) baseStart_871829 baseEnd_871829 := by
    simpa [prefixWord, tailWord_871829, baseEnd_871829] using wordTrace_append hprefix tailTrace_871829
  have hstable : (prefixWord ++ tailWord_871829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871829).length < 2 ^ (prefixWord ++ tailWord_871829).sum := by decide
  have hdescent : baseEnd_871829 < baseStart_871829 := by decide
  rcases family_descends (prefixWord ++ tailWord_871829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871838 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_871838 : Nat := 118140960795 + 871838 * 2 ^ 59
def prefixEnd_871838 : Nat := 4983230072969 + 3 ^ 40 * 871838 * 2
def baseEnd_871838 : Nat := 397930619426369034235997

theorem tailTrace_871838 : CollatzResearch.WordTrace tailWord_871838 prefixEnd_871838 397930619426369034235997 := by
  unfold tailWord_871838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974818026935912365141021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21199029476991532614085445 3974818026935912365141021)
  ·
    refine ⟨1490556760100967136927883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3974818026935912365141021 1490556760100967136927883)
    ·
      refine ⟨2235835140151450705391825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1490556760100967136927883 2235835140151450705391825)
      ·
        refine ⟨1676876355113588029043869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2235835140151450705391825 1676876355113588029043869)
        ·
          refine ⟨628828633167595510891451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1676876355113588029043869 628828633167595510891451)
          ·
            refine ⟨943242949751393266337177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628828633167595510891451 943242949751393266337177)
            ·
              refine ⟨707432212313544949752883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943242949751393266337177 707432212313544949752883)
              ·
                refine ⟨1061148318470317424629325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707432212313544949752883 1061148318470317424629325)
                ·
                  refine ⟨397930619426369034235997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061148318470317424629325 397930619426369034235997)
                  ·
                    rfl

theorem cell20_871838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_871838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871838 prefixEnd_871838 := by exact prefixLift 871838
  have htrace : WordTrace (prefixWord ++ tailWord_871838) baseStart_871838 baseEnd_871838 := by
    simpa [prefixWord, tailWord_871838, baseEnd_871838] using wordTrace_append hprefix tailTrace_871838
  have hstable : (prefixWord ++ tailWord_871838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871838).length < 2 ^ (prefixWord ++ tailWord_871838).sum := by decide
  have hdescent : baseEnd_871838 < baseStart_871838 := by decide
  rcases family_descends (prefixWord ++ tailWord_871838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871842 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_871842 : Nat := 118140960795 + 871842 * 2 ^ 59
def prefixEnd_871842 : Nat := 4983230072969 + 3 ^ 40 * 871842 * 2
def baseEnd_871842 : Nat := 397932445135362798102647

theorem tailTrace_871842 : CollatzResearch.WordTrace tailWord_871842 prefixEnd_871842 397932445135362798102647 := by
  unfold tailWord_871842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949672526868201901068445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21199126738315205069515853 7949672526868201901068445)
  ·
    refine ⟨2981127197575575712900667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7949672526868201901068445 2981127197575575712900667)
    ·
      refine ⟨4471690796363363569351001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981127197575575712900667 4471690796363363569351001)
      ·
        refine ⟨3353768097272522677013251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4471690796363363569351001 3353768097272522677013251)
        ·
          refine ⟨5030652145908784015519877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353768097272522677013251 5030652145908784015519877)
          ·
            refine ⟨943247277357897002909977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5030652145908784015519877 943247277357897002909977)
            ·
              refine ⟨707435458018422752182483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943247277357897002909977 707435458018422752182483)
              ·
                refine ⟨1061153187027634128273725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707435458018422752182483 1061153187027634128273725)
                ·
                  refine ⟨397932445135362798102647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061153187027634128273725 397932445135362798102647)
                  ·
                    rfl

theorem cell20_871842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_871842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871842 prefixEnd_871842 := by exact prefixLift 871842
  have htrace : WordTrace (prefixWord ++ tailWord_871842) baseStart_871842 baseEnd_871842 := by
    simpa [prefixWord, tailWord_871842, baseEnd_871842] using wordTrace_append hprefix tailTrace_871842
  have hstable : (prefixWord ++ tailWord_871842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871842).length < 2 ^ (prefixWord ++ tailWord_871842).sum := by decide
  have hdescent : baseEnd_871842 < baseStart_871842 := by decide
  rcases family_descends (prefixWord ++ tailWord_871842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871870 : List Nat := [4, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_871870 : Nat := 118140960795 + 871870 * 2 ^ 59
def prefixEnd_871870 : Nat := 4983230072969 + 3 ^ 40 * 871870 * 2
def baseEnd_871870 : Nat := 397945225098319145169199

theorem tailTrace_871870 : CollatzResearch.WordTrace tailWord_871870 prefixEnd_871870 397945225098319145169199 := by
  unfold tailWord_871870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974963918921421048286633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21199807567580912257528709 3974963918921421048286633)
  ·
    refine ⟨2981222939191065786214975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3974963918921421048286633 2981222939191065786214975)
    ·
      refine ⟨4471834408786598679322463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981222939191065786214975 4471834408786598679322463)
      ·
        refine ⟨6707751613179898018983695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471834408786598679322463 6707751613179898018983695)
        ·
          refine ⟨10061627419769847028475543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6707751613179898018983695 10061627419769847028475543)
          ·
            refine ⟨15092441129654770542713315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10061627419769847028475543 15092441129654770542713315)
            ·
              refine ⟨22638661694482155814069973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15092441129654770542713315 22638661694482155814069973)
              ·
                refine ⟨530593633464425526892265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22638661694482155814069973 530593633464425526892265)
                ·
                  refine ⟨397945225098319145169199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530593633464425526892265 397945225098319145169199)
                  ·
                    rfl

theorem cell20_871870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_871870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871870 prefixEnd_871870 := by exact prefixLift 871870
  have htrace : WordTrace (prefixWord ++ tailWord_871870) baseStart_871870 baseEnd_871870 := by
    simpa [prefixWord, tailWord_871870, baseEnd_871870] using wordTrace_append hprefix tailTrace_871870
  have hstable : (prefixWord ++ tailWord_871870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871870).length < 2 ^ (prefixWord ++ tailWord_871870).sum := by decide
  have hdescent : baseEnd_871870 < baseStart_871870 := by decide
  rcases family_descends (prefixWord ++ tailWord_871870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871884 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_871884 : Nat := 118140960795 + 871884 * 2 ^ 59
def prefixEnd_871884 : Nat := 4983230072969 + 3 ^ 40 * 871884 * 2
def baseEnd_871884 : Nat := 397951615079797318702475

theorem tailTrace_871884 : CollatzResearch.WordTrace tailWord_871884 prefixEnd_871884 397951615079797318702475 := by
  unfold tailWord_871884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15900110986660324388651353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21200147982213765851535137 15900110986660324388651353)
  ·
    refine ⟨11925083239995243291488515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15900110986660324388651353 11925083239995243291488515)
    ·
      refine ⟨17887624859992864937232773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11925083239995243291488515 17887624859992864937232773)
      ·
        refine ⟨3353929661248662175731145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17887624859992864937232773 3353929661248662175731145)
        ·
          refine ⟨2515447245936496631798359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3353929661248662175731145 2515447245936496631798359)
          ·
            refine ⟨3773170868904744947697539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515447245936496631798359 3773170868904744947697539)
            ·
              refine ⟨5659756303357117421546309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773170868904744947697539 5659756303357117421546309)
              ·
                refine ⟨1061204306879459516539933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5659756303357117421546309 1061204306879459516539933)
                ·
                  refine ⟨397951615079797318702475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061204306879459516539933 397951615079797318702475)
                  ·
                    rfl

theorem cell20_871884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_871884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871884 prefixEnd_871884 := by exact prefixLift 871884
  have htrace : WordTrace (prefixWord ++ tailWord_871884) baseStart_871884 baseEnd_871884 := by
    simpa [prefixWord, tailWord_871884, baseEnd_871884] using wordTrace_append hprefix tailTrace_871884
  have hstable : (prefixWord ++ tailWord_871884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871884).length < 2 ^ (prefixWord ++ tailWord_871884).sum := by decide
  have hdescent : baseEnd_871884 < baseStart_871884 := by decide
  rcases family_descends (prefixWord ++ tailWord_871884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871894 : List Nat := [5, 2, 1, 1, 1, 4, 1, 5]
def baseStart_871894 : Nat := 118140960795 + 871894 * 2 ^ 59
def prefixEnd_871894 : Nat := 4983230072969 + 3 ^ 40 * 871894 * 2
def baseEnd_871894 : Nat := 132652059784093909456367

theorem tailTrace_871894 : CollatzResearch.WordTrace tailWord_871894 prefixEnd_871894 132652059784093909456367 := by
  unfold tailWord_871894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987536668955276280322921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21200391135522946990111157 1987536668955276280322921)
  ·
    refine ⟨1490652501716457210242191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1987536668955276280322921 1490652501716457210242191)
    ·
      refine ⟨2235978752574685815363287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1490652501716457210242191 2235978752574685815363287)
      ·
        refine ⟨3353968128862028723044931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235978752574685815363287 3353968128862028723044931)
        ·
          refine ⟨5030952193293043084567397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353968128862028723044931 5030952193293043084567397)
          ·
            refine ⟨943303536242445578356387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5030952193293043084567397 943303536242445578356387)
            ·
              refine ⟨1414955304363668367534581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943303536242445578356387 1414955304363668367534581)
              ·
                refine ⟨132652059784093909456367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1414955304363668367534581 132652059784093909456367)
                ·
                  rfl

theorem cell20_871894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_871894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871894 prefixEnd_871894 := by exact prefixLift 871894
  have htrace : WordTrace (prefixWord ++ tailWord_871894) baseStart_871894 baseEnd_871894 := by
    simpa [prefixWord, tailWord_871894, baseEnd_871894] using wordTrace_append hprefix tailTrace_871894
  have hstable : (prefixWord ++ tailWord_871894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871894).length < 2 ^ (prefixWord ++ tailWord_871894).sum := by decide
  have hdescent : baseEnd_871894 < baseStart_871894 := by decide
  rcases family_descends (prefixWord ++ tailWord_871894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871898 : List Nat := [3, 1, 1, 2, 3, 2, 3, 5]
def baseStart_871898 : Nat := 118140960795 + 871898 * 2 ^ 59
def prefixEnd_871898 : Nat := 4983230072969 + 3 ^ 40 * 871898 * 2
def baseEnd_871898 : Nat := 132652668353758497411917

theorem tailTrace_871898 : CollatzResearch.WordTrace tailWord_871898 prefixEnd_871898 132652668353758497411917 := by
  unfold tailWord_871898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950183148817482292078087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21200488396846619445541565 7950183148817482292078087)
  ·
    refine ⟨11925274723226223438117131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7950183148817482292078087 11925274723226223438117131)
    ·
      refine ⟨17887912084839335157175697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11925274723226223438117131 17887912084839335157175697)
      ·
        refine ⟨13415934063629501367881773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17887912084839335157175697 13415934063629501367881773)
        ·
          refine ⟨5030975273861063012955665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13415934063629501367881773 5030975273861063012955665)
          ·
            refine ⟨3773231455395797259716749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030975273861063012955665 3773231455395797259716749)
            ·
              refine ⟨1414961795773423972393781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3773231455395797259716749 1414961795773423972393781)
              ·
                refine ⟨132652668353758497411917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1414961795773423972393781 132652668353758497411917)
                ·
                  rfl

theorem cell20_871898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_871898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871898 prefixEnd_871898 := by exact prefixLift 871898
  have htrace : WordTrace (prefixWord ++ tailWord_871898) baseStart_871898 baseEnd_871898 := by
    simpa [prefixWord, tailWord_871898, baseEnd_871898] using wordTrace_append hprefix tailTrace_871898
  have hstable : (prefixWord ++ tailWord_871898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871898).length < 2 ^ (prefixWord ++ tailWord_871898).sum := by decide
  have hdescent : baseEnd_871898 < baseStart_871898 := by decide
  rcases family_descends (prefixWord ++ tailWord_871898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871919 : List Nat := [1, 1, 2, 1, 4, 1, 2, 8]
def baseStart_871919 : Nat := 118140960795 + 871919 * 2 ^ 59
def prefixEnd_871919 : Nat := 4983230072969 + 3 ^ 40 * 871919 * 2
def baseEnd_871919 : Nat := 132655863344497584178555

theorem tailTrace_871919 : CollatzResearch.WordTrace tailWord_871919 prefixEnd_871919 132655863344497584178555 := by
  unfold tailWord_871919
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801498528193849754826811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21200999018795899836551207 31801498528193849754826811)
  ·
    refine ⟨47702247792290774632240217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31801498528193849754826811 47702247792290774632240217)
    ·
      refine ⟨35776685844218080974180163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47702247792290774632240217 35776685844218080974180163)
      ·
        refine ⟨53665028766327121461270245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35776685844218080974180163 53665028766327121461270245)
        ·
          refine ⟨10062192893686335273988171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53665028766327121461270245 10062192893686335273988171)
          ·
            refine ⟨15093289340529502910982257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10062192893686335273988171 15093289340529502910982257)
            ·
              refine ⟨11319967005397127183236693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15093289340529502910982257 11319967005397127183236693)
              ·
                refine ⟨132655863344497584178555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11319967005397127183236693 132655863344497584178555)
                ·
                  rfl

theorem cell20_871919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_871919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871919 prefixEnd_871919 := by exact prefixLift 871919
  have htrace : WordTrace (prefixWord ++ tailWord_871919) baseStart_871919 baseEnd_871919 := by
    simpa [prefixWord, tailWord_871919, baseEnd_871919] using wordTrace_append hprefix tailTrace_871919
  have hstable : (prefixWord ++ tailWord_871919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871919).length < 2 ^ (prefixWord ++ tailWord_871919).sum := by decide
  have hdescent : baseEnd_871919 < baseStart_871919 := by decide
  rcases family_descends (prefixWord ++ tailWord_871919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871925 : List Nat := [1, 3, 5, 1, 1, 1, 1, 5, 2]
def baseStart_871925 : Nat := 118140960795 + 871925 * 2 ^ 59
def prefixEnd_871925 : Nat := 4983230072969 + 3 ^ 40 * 871925 * 2
def baseEnd_871925 : Nat := 397970328596983398335641

theorem tailTrace_871925 : CollatzResearch.WordTrace tailWord_871925 prefixEnd_871925 397970328596983398335641 := by
  unfold tailWord_871925
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801717366172112779545229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21201144910781408519696819 31801717366172112779545229)
  ·
    refine ⟨11925644012314542292329461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31801717366172112779545229 11925644012314542292329461)
    ·
      refine ⟨1118029126154488339905887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11925644012314542292329461 1118029126154488339905887)
      ·
        refine ⟨1677043689231732509858831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118029126154488339905887 1677043689231732509858831)
        ·
          refine ⟨2515565533847598764788247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677043689231732509858831 2515565533847598764788247)
          ·
            refine ⟨3773348300771398147182371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515565533847598764788247 3773348300771398147182371)
            ·
              refine ⟨5660022451157097220773557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773348300771398147182371 5660022451157097220773557)
              ·
                refine ⟨530627104795977864447521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5660022451157097220773557 530627104795977864447521)
                ·
                  refine ⟨397970328596983398335641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530627104795977864447521 397970328596983398335641)
                  ·
                    rfl

theorem cell20_871925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_871925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871925 prefixEnd_871925 := by exact prefixLift 871925
  have htrace : WordTrace (prefixWord ++ tailWord_871925) baseStart_871925 baseEnd_871925 := by
    simpa [prefixWord, tailWord_871925, baseEnd_871925] using wordTrace_append hprefix tailTrace_871925
  have hstable : (prefixWord ++ tailWord_871925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871925).length < 2 ^ (prefixWord ++ tailWord_871925).sum := by decide
  have hdescent : baseEnd_871925 < baseStart_871925 := by decide
  rcases family_descends (prefixWord ++ tailWord_871925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871946 : List Nat := [3, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_871946 : Nat := 118140960795 + 871946 * 2 ^ 59
def prefixEnd_871946 : Nat := 4983230072969 + 3 ^ 40 * 871946 * 2
def baseEnd_871946 : Nat := 397979913569200658635555

theorem tailTrace_871946 : CollatzResearch.WordTrace tailWord_871946 prefixEnd_871946 397979913569200658635555 := by
  unfold tailWord_871946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950620824774008341514923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21201655532730688910706461 7950620824774008341514923)
  ·
    refine ⟨11925931237161012512272385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7950620824774008341514923 11925931237161012512272385)
    ·
      refine ⟨8944448427870759384204289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11925931237161012512272385 8944448427870759384204289)
      ·
        refine ⟨6708336320903069538153217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8944448427870759384204289 6708336320903069538153217)
        ·
          refine ⟨5031252240677302153614913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6708336320903069538153217 5031252240677302153614913)
          ·
            refine ⟨3773439180507976615211185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5031252240677302153614913 3773439180507976615211185)
            ·
              refine ⟨2830079385380982461408389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3773439180507976615211185 2830079385380982461408389)
              ·
                refine ⟨530639884758934211514073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2830079385380982461408389 530639884758934211514073)
                ·
                  refine ⟨397979913569200658635555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530639884758934211514073 397979913569200658635555)
                  ·
                    rfl

theorem cell20_871946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_871946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_871946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_871946 prefixEnd_871946 := by exact prefixLift 871946
  have htrace : WordTrace (prefixWord ++ tailWord_871946) baseStart_871946 baseEnd_871946 := by
    simpa [prefixWord, tailWord_871946, baseEnd_871946] using wordTrace_append hprefix tailTrace_871946
  have hstable : (prefixWord ++ tailWord_871946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871946).length < 2 ^ (prefixWord ++ tailWord_871946).sum := by decide
  have hdescent : baseEnd_871946 < baseStart_871946 := by decide
  rcases family_descends (prefixWord ++ tailWord_871946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872001 : List Nat := [1, 2, 5, 1, 1, 1, 5, 2, 2]
def baseStart_872001 : Nat := 118140960795 + 872001 * 2 ^ 59
def prefixEnd_872001 : Nat := 4983230072969 + 3 ^ 40 * 872001 * 2
def baseEnd_872001 : Nat := 398005017067864911801997

theorem tailTrace_872001 : CollatzResearch.WordTrace tailWord_872001 prefixEnd_872001 398005017067864911801997 := by
  unfold tailWord_872001
  simp only [CollatzResearch.WordTrace]
  refine ⟨31804489313896777759311857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21202992875931185172874571 31804489313896777759311857)
  ·
    refine ⟨23853366985422583319483893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31804489313896777759311857 23853366985422583319483893)
    ·
      refine ⟨2236253154883367186201615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23853366985422583319483893 2236253154883367186201615)
      ·
        refine ⟨3354379732325050779302423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2236253154883367186201615 3354379732325050779302423)
        ·
          refine ⟨5031569598487576168953635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354379732325050779302423 5031569598487576168953635)
          ·
            refine ⟨7547354397731364253430453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031569598487576168953635 7547354397731364253430453)
            ·
              refine ⟨707564474787315398759105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7547354397731364253430453 707564474787315398759105)
              ·
                refine ⟨530673356090486549069329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707564474787315398759105 530673356090486549069329)
                ·
                  refine ⟨398005017067864911801997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530673356090486549069329 398005017067864911801997)
                  ·
                    rfl

theorem cell20_872001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_872001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872001 prefixEnd_872001 := by exact prefixLift 872001
  have htrace : WordTrace (prefixWord ++ tailWord_872001) baseStart_872001 baseEnd_872001 := by
    simpa [prefixWord, tailWord_872001, baseEnd_872001] using wordTrace_append hprefix tailTrace_872001
  have hstable : (prefixWord ++ tailWord_872001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872001).length < 2 ^ (prefixWord ++ tailWord_872001).sum := by decide
  have hdescent : baseEnd_872001 < baseStart_872001 := by decide
  rcases family_descends (prefixWord ++ tailWord_872001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872012 : List Nat := [2, 2, 1, 3, 1, 4, 2, 5]
def baseStart_872012 : Nat := 118140960795 + 872012 * 2 ^ 59
def prefixEnd_872012 : Nat := 4983230072969 + 3 ^ 40 * 872012 * 2
def baseEnd_872012 : Nat := 132670012589199254145095

theorem tailTrace_872012 : CollatzResearch.WordTrace tailWord_872012 prefixEnd_872012 132670012589199254145095 := by
  unfold tailWord_872012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902445258428463318981145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21203260344571284425308193 15902445258428463318981145)
  ·
    refine ⟨11926833943821347489235859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15902445258428463318981145 11926833943821347489235859)
    ·
      refine ⟨17890250915732021233853789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11926833943821347489235859 17890250915732021233853789)
      ·
        refine ⟨6708844093399507962695171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17890250915732021233853789 6708844093399507962695171)
        ·
          refine ⟨10063266140099261944042757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708844093399507962695171 10063266140099261944042757)
          ·
            refine ⟨1886862401268611614508017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10063266140099261944042757 1886862401268611614508017)
            ·
              refine ⟨1415146800951458710881013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1886862401268611614508017 1415146800951458710881013)
              ·
                refine ⟨132670012589199254145095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1415146800951458710881013 132670012589199254145095)
                ·
                  rfl

theorem cell20_872012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_872012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872012 prefixEnd_872012 := by exact prefixLift 872012
  have htrace : WordTrace (prefixWord ++ tailWord_872012) baseStart_872012 baseEnd_872012 := by
    simpa [prefixWord, tailWord_872012, baseEnd_872012] using wordTrace_append hprefix tailTrace_872012
  have hstable : (prefixWord ++ tailWord_872012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872012).length < 2 ^ (prefixWord ++ tailWord_872012).sum := by decide
  have hdescent : baseEnd_872012 < baseStart_872012 := by decide
  rcases family_descends (prefixWord ++ tailWord_872012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872026 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_872026 : Nat := 118140960795 + 872026 * 2 ^ 59
def prefixEnd_872026 : Nat := 4983230072969 + 3 ^ 40 * 872026 * 2
def baseEnd_872026 : Nat := 398016427749075935968561

theorem tailTrace_872026 : CollatzResearch.WordTrace tailWord_872026 prefixEnd_872026 398016427749075935968561 := by
  unfold tailWord_872026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951350284701551757242983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21203600759204138019314621 7951350284701551757242983)
  ·
    refine ⟨11927025427052327635864475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7951350284701551757242983 11927025427052327635864475)
    ·
      refine ⟨17890538140578491453796713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11927025427052327635864475 17890538140578491453796713)
      ·
        refine ⟨13417903605433868590347535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17890538140578491453796713 13417903605433868590347535)
        ·
          refine ⟨20126855408150802885521303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13417903605433868590347535 20126855408150802885521303)
          ·
            refine ⟨30190283112226204328281955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20126855408150802885521303 30190283112226204328281955)
            ·
              refine ⟨45285424668339306492422933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30190283112226204328281955 45285424668339306492422933)
              ·
                refine ⟨2122754281328404991832325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45285424668339306492422933 2122754281328404991832325)
                ·
                  refine ⟨398016427749075935968561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122754281328404991832325 398016427749075935968561)
                  ·
                    rfl

theorem cell20_872026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_872026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872026 prefixEnd_872026 := by exact prefixLift 872026
  have htrace : WordTrace (prefixWord ++ tailWord_872026) baseStart_872026 baseEnd_872026 := by
    simpa [prefixWord, tailWord_872026, baseEnd_872026] using wordTrace_append hprefix tailTrace_872026
  have hstable : (prefixWord ++ tailWord_872026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872026).length < 2 ^ (prefixWord ++ tailWord_872026).sum := by decide
  have hdescent : baseEnd_872026 < baseStart_872026 := by decide
  rcases family_descends (prefixWord ++ tailWord_872026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872033 : List Nat := [1, 2, 3, 1, 1, 3, 1, 8]
def baseStart_872033 : Nat := 118140960795 + 872033 * 2 ^ 59
def prefixEnd_872033 : Nat := 4983230072969 + 3 ^ 40 * 872033 * 2
def baseEnd_872033 : Nat := 132673207579938340911733

theorem tailTrace_872033 : CollatzResearch.WordTrace tailWord_872033 prefixEnd_872033 132673207579938340911733 := by
  unfold tailWord_872033
  simp only [CollatzResearch.WordTrace]
  refine ⟨31805656449780847224476753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21203770966520564816317835 31805656449780847224476753)
  ·
    refine ⟨23854242337335635418357565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31805656449780847224476753 23854242337335635418357565)
    ·
      refine ⟨8945340876500863281884087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23854242337335635418357565 8945340876500863281884087)
      ·
        refine ⟨13418011314751294922826131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8945340876500863281884087 13418011314751294922826131)
        ·
          refine ⟨20127016972126942384239197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13418011314751294922826131 20127016972126942384239197)
          ·
            refine ⟨7547631364547603394089699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20127016972126942384239197 7547631364547603394089699)
            ·
              refine ⟨11321447046821405091134549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7547631364547603394089699 11321447046821405091134549)
              ·
                refine ⟨132673207579938340911733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11321447046821405091134549 132673207579938340911733)
                ·
                  rfl

theorem cell20_872033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_872033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872033 prefixEnd_872033 := by exact prefixLift 872033
  have htrace : WordTrace (prefixWord ++ tailWord_872033) baseStart_872033 baseEnd_872033 := by
    simpa [prefixWord, tailWord_872033, baseEnd_872033] using wordTrace_append hprefix tailTrace_872033
  have hstable : (prefixWord ++ tailWord_872033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872033).length < 2 ^ (prefixWord ++ tailWord_872033).sum := by decide
  have hdescent : baseEnd_872033 < baseStart_872033 := by decide
  rcases family_descends (prefixWord ++ tailWord_872033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872053 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 3]
def baseStart_872053 : Nat := 118140960795 + 872053 * 2 ^ 59
def prefixEnd_872053 : Nat := 4983230072969 + 3 ^ 40 * 872053 * 2
def baseEnd_872053 : Nat := 398028751284783842068451

theorem tailTrace_872053 : CollatzResearch.WordTrace tailWord_872053 prefixEnd_872053 398028751284783842068451 := by
  unfold tailWord_872053
  simp only [CollatzResearch.WordTrace]
  refine ⟨31806385909708390640204813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21204257273138927093469875 31806385909708390640204813)
  ·
    refine ⟨11927394716140646490076805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31806385909708390640204813 11927394716140646490076805)
    ·
      refine ⟨2236386509276371216889401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11927394716140646490076805 2236386509276371216889401)
      ·
        refine ⟨1677289881957278412667051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2236386509276371216889401 1677289881957278412667051)
        ·
          refine ⟨2515934822935917619000577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677289881957278412667051 2515934822935917619000577)
          ·
            refine ⟨1886951117201938214250433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515934822935917619000577 1886951117201938214250433)
            ·
              refine ⟨1415213337901453660687825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1886951117201938214250433 1415213337901453660687825)
              ·
                refine ⟨1061410003426090245515869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415213337901453660687825 1061410003426090245515869)
                ·
                  refine ⟨398028751284783842068451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061410003426090245515869 398028751284783842068451)
                  ·
                    rfl

theorem cell20_872053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_872053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872053 prefixEnd_872053 := by exact prefixLift 872053
  have htrace : WordTrace (prefixWord ++ tailWord_872053) baseStart_872053 baseEnd_872053 := by
    simpa [prefixWord, tailWord_872053, baseEnd_872053] using wordTrace_append hprefix tailTrace_872053
  have hstable : (prefixWord ++ tailWord_872053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872053).length < 2 ^ (prefixWord ++ tailWord_872053).sum := by decide
  have hdescent : baseEnd_872053 < baseStart_872053 := by decide
  rcases family_descends (prefixWord ++ tailWord_872053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872064 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_872064 : Nat := 118140960795 + 872064 * 2 ^ 59
def prefixEnd_872064 : Nat := 4983230072969 + 3 ^ 40 * 872064 * 2
def baseEnd_872064 : Nat := 398033771984516692701739

theorem tailTrace_872064 : CollatzResearch.WordTrace tailWord_872064 prefixEnd_872064 398033771984516692701739 := by
  unfold tailWord_872064
  simp only [CollatzResearch.WordTrace]
  refine ⟨15903393556334269759427623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21204524741779026345903497 15903393556334269759427623)
  ·
    refine ⟨23855090334501404639141435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15903393556334269759427623 23855090334501404639141435)
    ·
      refine ⟨35782635501752106958712153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23855090334501404639141435 35782635501752106958712153)
      ·
        refine ⟨26836976626314080219034115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35782635501752106958712153 26836976626314080219034115)
        ·
          refine ⟨40255464939471120328551173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26836976626314080219034115 40255464939471120328551173)
          ·
            refine ⟨7547899676150835061603345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40255464939471120328551173 7547899676150835061603345)
            ·
              refine ⟨5660924757113126296202509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7547899676150835061603345 5660924757113126296202509)
              ·
                refine ⟨2122846783917422361075941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5660924757113126296202509 2122846783917422361075941)
                ·
                  refine ⟨398033771984516692701739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122846783917422361075941 398033771984516692701739)
                  ·
                    rfl

theorem cell20_872064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_872064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872064 prefixEnd_872064 := by exact prefixLift 872064
  have htrace : WordTrace (prefixWord ++ tailWord_872064) baseStart_872064 baseEnd_872064 := by
    simpa [prefixWord, tailWord_872064, baseEnd_872064] using wordTrace_append hprefix tailTrace_872064
  have hstable : (prefixWord ++ tailWord_872064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872064).length < 2 ^ (prefixWord ++ tailWord_872064).sum := by decide
  have hdescent : baseEnd_872064 < baseStart_872064 := by decide
  rcases family_descends (prefixWord ++ tailWord_872064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872074 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_872074 : Nat := 118140960795 + 872074 * 2 ^ 59
def prefixEnd_872074 : Nat := 4983230072969 + 3 ^ 40 * 872074 * 2
def baseEnd_872074 : Nat := 398038336257001102368365

theorem tailTrace_872074 : CollatzResearch.WordTrace tailWord_872074 prefixEnd_872074 398038336257001102368365 := by
  unfold tailWord_872074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951787960658077806679819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21204767895088207484479517 7951787960658077806679819)
  ·
    refine ⟨11927681940987116710019729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7951787960658077806679819 11927681940987116710019729)
    ·
      refine ⟨8945761455740337532514797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11927681940987116710019729 8945761455740337532514797)
      ·
        refine ⟨3354660545902626574693049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8945761455740337532514797 3354660545902626574693049)
        ·
          refine ⟨2515995409426969931019787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3354660545902626574693049 2515995409426969931019787)
          ·
            refine ⟨3773993114140454896529681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515995409426969931019787 3773993114140454896529681)
            ·
              refine ⟨2830494835605341172397261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3773993114140454896529681 2830494835605341172397261)
              ·
                refine ⟨1061435563352002939648973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2830494835605341172397261 1061435563352002939648973)
                ·
                  refine ⟨398038336257001102368365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061435563352002939648973 398038336257001102368365)
                  ·
                    rfl

theorem cell20_872074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_872074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872074 prefixEnd_872074 := by exact prefixLift 872074
  have htrace : WordTrace (prefixWord ++ tailWord_872074) baseStart_872074 baseEnd_872074 := by
    simpa [prefixWord, tailWord_872074, baseEnd_872074] using wordTrace_append hprefix tailTrace_872074
  have hstable : (prefixWord ++ tailWord_872074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872074).length < 2 ^ (prefixWord ++ tailWord_872074).sum := by decide
  have hdescent : baseEnd_872074 < baseStart_872074 := by decide
  rcases family_descends (prefixWord ++ tailWord_872074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872084 : List Nat := [2, 4, 2, 2, 2, 1, 3, 4]
def baseStart_872084 : Nat := 118140960795 + 872084 * 2 ^ 59
def prefixEnd_872084 : Nat := 4983230072969 + 3 ^ 40 * 872084 * 2
def baseEnd_872084 : Nat := 132680966843161837344997

theorem tailTrace_872084 : CollatzResearch.WordTrace tailWord_872084 prefixEnd_872084 132680966843161837344997 := by
  unfold tailWord_872084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15903758286298041467291653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21205011048397388623055537 15903758286298041467291653)
  ·
    refine ⟨2981954678680882775117185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15903758286298041467291653 2981954678680882775117185)
    ·
      refine ⟨2236466009010662081337889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2981954678680882775117185 2236466009010662081337889)
      ·
        refine ⟨1677349506757996561003417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2236466009010662081337889 1677349506757996561003417)
        ·
          refine ⟨1258012130068497420752563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1677349506757996561003417 1258012130068497420752563)
          ·
            refine ⟨1887018195102746131128845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258012130068497420752563 1887018195102746131128845)
            ·
              refine ⟨707631823163529799173317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1887018195102746131128845 707631823163529799173317)
              ·
                refine ⟨132680966843161837344997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 707631823163529799173317 132680966843161837344997)
                ·
                  rfl

theorem cell20_872084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_872084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872084 prefixEnd_872084 := by exact prefixLift 872084
  have htrace : WordTrace (prefixWord ++ tailWord_872084) baseStart_872084 baseEnd_872084 := by
    simpa [prefixWord, tailWord_872084, baseEnd_872084] using wordTrace_append hprefix tailTrace_872084
  have hstable : (prefixWord ++ tailWord_872084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872084).length < 2 ^ (prefixWord ++ tailWord_872084).sum := by decide
  have hdescent : baseEnd_872084 < baseStart_872084 := by decide
  rcases family_descends (prefixWord ++ tailWord_872084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872104 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 3]
def baseStart_872104 : Nat := 118140960795 + 872104 * 2 ^ 59
def prefixEnd_872104 : Nat := 4983230072969 + 3 ^ 40 * 872104 * 2
def baseEnd_872104 : Nat := 398052029074454331368243

theorem tailTrace_872104 : CollatzResearch.WordTrace tailWord_872104 prefixEnd_872104 398052029074454331368243 := by
  unfold tailWord_872104
  simp only [CollatzResearch.WordTrace]
  refine ⟨15904123016261813175155683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21205497355015750900207577 15904123016261813175155683)
  ·
    refine ⟨23856184524392719762733525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15904123016261813175155683 23856184524392719762733525)
    ·
      refine ⟨559129324790454369439067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23856184524392719762733525 559129324790454369439067)
      ·
        refine ⟨838693987185681554158601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559129324790454369439067 838693987185681554158601)
        ·
          refine ⟨629020490389261165618951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838693987185681554158601 629020490389261165618951)
          ·
            refine ⟨943530735583891748428427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629020490389261165618951 943530735583891748428427)
            ·
              refine ⟨1415296103375837622642641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943530735583891748428427 1415296103375837622642641)
              ·
                refine ⟨1061472077531878216981981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415296103375837622642641 1061472077531878216981981)
                ·
                  refine ⟨398052029074454331368243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061472077531878216981981 398052029074454331368243)
                  ·
                    rfl

theorem cell20_872104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_872104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872104 prefixEnd_872104 := by exact prefixLift 872104
  have htrace : WordTrace (prefixWord ++ tailWord_872104) baseStart_872104 baseEnd_872104 := by
    simpa [prefixWord, tailWord_872104, baseEnd_872104] using wordTrace_append hprefix tailTrace_872104
  have hstable : (prefixWord ++ tailWord_872104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872104).length < 2 ^ (prefixWord ++ tailWord_872104).sum := by decide
  have hdescent : baseEnd_872104 < baseStart_872104 := by decide
  rcases family_descends (prefixWord ++ tailWord_872104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872119 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_872119 : Nat := 118140960795 + 872119 * 2 ^ 59
def prefixEnd_872119 : Nat := 4983230072969 + 3 ^ 40 * 872119 * 2
def baseEnd_872119 : Nat := 398058875483180945868181

theorem tailTrace_872119 : CollatzResearch.WordTrace tailWord_872119 prefixEnd_872119 398058875483180945868181 := by
  unfold tailWord_872119
  simp only [CollatzResearch.WordTrace]
  refine ⟨31808793127469283912107411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21205862084979522608071607 31808793127469283912107411)
  ·
    refine ⟨47713189691203925868161117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31808793127469283912107411 47713189691203925868161117)
    ·
      refine ⟨17892446134201472200560419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47713189691203925868161117 17892446134201472200560419)
      ·
        refine ⟨26838669201302208300840629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17892446134201472200560419 26838669201302208300840629)
        ·
          refine ⟨2516125237622082028203809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26838669201302208300840629 2516125237622082028203809)
          ·
            refine ⟨1887093928216561521152857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2516125237622082028203809 1887093928216561521152857)
            ·
              refine ⟨1415320446162421140864643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887093928216561521152857 1415320446162421140864643)
              ·
                refine ⟨2122980669243631711296965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415320446162421140864643 2122980669243631711296965)
                ·
                  refine ⟨398058875483180945868181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122980669243631711296965 398058875483180945868181)
                  ·
                    rfl

theorem cell20_872119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_872119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872119 prefixEnd_872119 := by exact prefixLift 872119
  have htrace : WordTrace (prefixWord ++ tailWord_872119) baseStart_872119 baseEnd_872119 := by
    simpa [prefixWord, tailWord_872119, baseEnd_872119] using wordTrace_append hprefix tailTrace_872119
  have hstable : (prefixWord ++ tailWord_872119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872119).length < 2 ^ (prefixWord ++ tailWord_872119).sum := by decide
  have hdescent : baseEnd_872119 < baseStart_872119 := by decide
  rcases family_descends (prefixWord ++ tailWord_872119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872226 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_872226 : Nat := 118140960795 + 872226 * 2 ^ 59
def prefixEnd_872226 : Nat := 4983230072969 + 3 ^ 40 * 872226 * 2
def baseEnd_872226 : Nat := 398107713198764129301077

theorem tailTrace_872226 : CollatzResearch.WordTrace tailWord_872226 prefixEnd_872226 398107713198764129301077 := by
  unfold tailWord_872226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953173934520410296563133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21208463825387760790835021 7953173934520410296563133)
  ·
    refine ⟨2982440225445153861211175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7953173934520410296563133 2982440225445153861211175)
    ·
      refine ⟨4473660338167730791816763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2982440225445153861211175 4473660338167730791816763)
      ·
        refine ⟨6710490507251596187725145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473660338167730791816763 6710490507251596187725145)
        ·
          refine ⟨5032867880438697140793859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6710490507251596187725145 5032867880438697140793859)
          ·
            refine ⟨7549301820658045711190789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5032867880438697140793859 7549301820658045711190789)
            ·
              refine ⟨1415494091373383570848273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7549301820658045711190789 1415494091373383570848273)
              ·
                refine ⟨1061620568530037678136205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415494091373383570848273 1061620568530037678136205)
                ·
                  refine ⟨398107713198764129301077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061620568530037678136205 398107713198764129301077)
                  ·
                    rfl

theorem cell20_872226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_872226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872226 prefixEnd_872226 := by exact prefixLift 872226
  have htrace : WordTrace (prefixWord ++ tailWord_872226) baseStart_872226 baseEnd_872226 := by
    simpa [prefixWord, tailWord_872226, baseEnd_872226] using wordTrace_append hprefix tailTrace_872226
  have hstable : (prefixWord ++ tailWord_872226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872226).length < 2 ^ (prefixWord ++ tailWord_872226).sum := by decide
  have hdescent : baseEnd_872226 < baseStart_872226 := by decide
  rcases family_descends (prefixWord ++ tailWord_872226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872229 : List Nat := [1, 3, 1, 2, 3, 4, 2, 2, 2]
def baseStart_872229 : Nat := 118140960795 + 872229 * 2 ^ 59
def prefixEnd_872229 : Nat := 4983230072969 + 3 ^ 40 * 872229 * 2
def baseEnd_872229 : Nat := 398109082480509452201065

theorem tailTrace_872229 : CollatzResearch.WordTrace tailWord_872229 prefixEnd_872229 398109082480509452201065 := by
  unfold tailWord_872229
  simp only [CollatzResearch.WordTrace]
  refine ⟨31812805157070772698611741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21208536771380515132407827 31812805157070772698611741)
  ·
    refine ⟨11929801933901539761979403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31812805157070772698611741 11929801933901539761979403)
    ·
      refine ⟨17894702900852309642969105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11929801933901539761979403 17894702900852309642969105)
      ·
        refine ⟨13421027175639232232226829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17894702900852309642969105 13421027175639232232226829)
        ·
          refine ⟨5032885190864712087085061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13421027175639232232226829 5032885190864712087085061)
          ·
            refine ⟨943665973287133516328449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5032885190864712087085061 943665973287133516328449)
            ·
              refine ⟨707749479965350137246337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943665973287133516328449 707749479965350137246337)
              ·
                refine ⟨530812109974012602934753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707749479965350137246337 530812109974012602934753)
                ·
                  refine ⟨398109082480509452201065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530812109974012602934753 398109082480509452201065)
                  ·
                    rfl

theorem cell20_872229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_872229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872229 prefixEnd_872229 := by exact prefixLift 872229
  have htrace : WordTrace (prefixWord ++ tailWord_872229) baseStart_872229 baseEnd_872229 := by
    simpa [prefixWord, tailWord_872229, baseEnd_872229] using wordTrace_append hprefix tailTrace_872229
  have hstable : (prefixWord ++ tailWord_872229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872229).length < 2 ^ (prefixWord ++ tailWord_872229).sum := by decide
  have hdescent : baseEnd_872229 < baseStart_872229 := by decide
  rcases family_descends (prefixWord ++ tailWord_872229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872298 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_872298 : Nat := 118140960795 + 872298 * 2 ^ 59
def prefixEnd_872298 : Nat := 4983230072969 + 3 ^ 40 * 872298 * 2
def baseEnd_872298 : Nat := 398140575960651878900783

theorem tailTrace_872298 : CollatzResearch.WordTrace tailWord_872298 prefixEnd_872298 398140575960651878900783 := by
  unfold tailWord_872298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953830448455199370718387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21210214529213864988582365 7953830448455199370718387)
  ·
    refine ⟨11930745672682799056077581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7953830448455199370718387 11930745672682799056077581)
    ·
      refine ⟨4474029627256049646029093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11930745672682799056077581 4474029627256049646029093)
      ·
        refine ⟨838880555110509308630455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4474029627256049646029093 838880555110509308630455)
        ·
          refine ⟨1258320832665763962945683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838880555110509308630455 1258320832665763962945683)
          ·
            refine ⟨1887481248998645944418525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258320832665763962945683 1887481248998645944418525)
            ·
              refine ⟨707805468374492229156947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1887481248998645944418525 707805468374492229156947)
              ·
                refine ⟨1061708202561738343735421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707805468374492229156947 1061708202561738343735421)
                ·
                  refine ⟨398140575960651878900783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061708202561738343735421 398140575960651878900783)
                  ·
                    rfl

theorem cell20_872298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_872298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872298 prefixEnd_872298 := by exact prefixLift 872298
  have htrace : WordTrace (prefixWord ++ tailWord_872298) baseStart_872298 baseEnd_872298 := by
    simpa [prefixWord, tailWord_872298, baseEnd_872298] using wordTrace_append hprefix tailTrace_872298
  have hstable : (prefixWord ++ tailWord_872298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872298).length < 2 ^ (prefixWord ++ tailWord_872298).sum := by decide
  have hdescent : baseEnd_872298 < baseStart_872298 := by decide
  rcases family_descends (prefixWord ++ tailWord_872298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872350 : List Nat := [4, 3, 1, 3, 1, 1, 2, 5]
def baseStart_872350 : Nat := 118140960795 + 872350 * 2 ^ 59
def prefixEnd_872350 : Nat := 4983230072969 + 3 ^ 40 * 872350 * 2
def baseEnd_872350 : Nat := 132721436725856936389079

theorem tailTrace_872350 : CollatzResearch.WordTrace tailWord_872350 prefixEnd_872350 132721436725856936389079 := by
  unfold tailWord_872350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977152298704051295470813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21211478926421606909177669 3977152298704051295470813)
  ·
    refine ⟨1491432112014019235801555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3977152298704051295470813 1491432112014019235801555)
    ·
      refine ⟨2237148168021028853702333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491432112014019235801555 2237148168021028853702333)
      ·
        refine ⟨838930563007885820138375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2237148168021028853702333 838930563007885820138375)
        ·
          refine ⟨1258395844511828730207563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838930563007885820138375 1258395844511828730207563)
          ·
            refine ⟨1887593766767743095311345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258395844511828730207563 1887593766767743095311345)
            ·
              refine ⟨1415695325075807321483509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887593766767743095311345 1415695325075807321483509)
              ·
                refine ⟨132721436725856936389079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1415695325075807321483509 132721436725856936389079)
                ·
                  rfl

theorem cell20_872350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_872350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872350 prefixEnd_872350 := by exact prefixLift 872350
  have htrace : WordTrace (prefixWord ++ tailWord_872350) baseStart_872350 baseEnd_872350 := by
    simpa [prefixWord, tailWord_872350, baseEnd_872350] using wordTrace_append hprefix tailTrace_872350
  have hstable : (prefixWord ++ tailWord_872350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872350).length < 2 ^ (prefixWord ++ tailWord_872350).sum := by decide
  have hdescent : baseEnd_872350 < baseStart_872350 := by decide
  rcases family_descends (prefixWord ++ tailWord_872350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872389 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_872389 : Nat := 118140960795 + 872389 * 2 ^ 59
def prefixEnd_872389 : Nat := 4983230072969 + 3 ^ 40 * 872389 * 2
def baseEnd_872389 : Nat := 398182110840260006867077

theorem tailTrace_872389 : CollatzResearch.WordTrace tailWord_872389 prefixEnd_872389 398182110840260006867077 := by
  unfold tailWord_872389
  simp only [CollatzResearch.WordTrace]
  refine ⟨31818640836491120024436221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21212427224327413349624147 31818640836491120024436221)
  ·
    refine ⟨11931990313684170009163583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31818640836491120024436221 11931990313684170009163583)
    ·
      refine ⟨17897985470526255013745375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11931990313684170009163583 17897985470526255013745375)
      ·
        refine ⟨26846978205789382520618063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17897985470526255013745375 26846978205789382520618063)
        ·
          refine ⟨40270467308684073780927095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26846978205789382520618063 40270467308684073780927095)
          ·
            refine ⟨60405700963026110671390643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40270467308684073780927095 60405700963026110671390643)
            ·
              refine ⟨90608551444539166007085965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60405700963026110671390643 90608551444539166007085965)
              ·
                refine ⟨33978206791702187252657237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90608551444539166007085965 33978206791702187252657237)
                ·
                  refine ⟨398182110840260006867077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33978206791702187252657237 398182110840260006867077)
                  ·
                    rfl

theorem cell20_872389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_872389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872389 prefixEnd_872389 := by exact prefixLift 872389
  have htrace : WordTrace (prefixWord ++ tailWord_872389) baseStart_872389 baseEnd_872389 := by
    simpa [prefixWord, tailWord_872389, baseEnd_872389] using wordTrace_append hprefix tailTrace_872389
  have hstable : (prefixWord ++ tailWord_872389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872389).length < 2 ^ (prefixWord ++ tailWord_872389).sum := by decide
  have hdescent : baseEnd_872389 < baseStart_872389 := by decide
  rcases family_descends (prefixWord ++ tailWord_872389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872399 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 3]
def baseStart_872399 : Nat := 118140960795 + 872399 * 2 ^ 59
def prefixEnd_872399 : Nat := 4983230072969 + 3 ^ 40 * 872399 * 2
def baseEnd_872399 : Nat := 398186675112744416533703

theorem tailTrace_872399 : CollatzResearch.WordTrace tailWord_872399 prefixEnd_872399 398186675112744416533703 := by
  unfold tailWord_872399
  simp only [CollatzResearch.WordTrace]
  refine ⟨31819005566454891732300251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21212670377636594488200167 31819005566454891732300251)
  ·
    refine ⟨47728508349682337598450377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31819005566454891732300251 47728508349682337598450377)
    ·
      refine ⟨35796381262261753198837783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47728508349682337598450377 35796381262261753198837783)
      ·
        refine ⟨53694571893392629798256675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35796381262261753198837783 53694571893392629798256675)
        ·
          refine ⟨80541857840088944697385013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53694571893392629798256675 80541857840088944697385013)
          ·
            refine ⟨7550799172508338565379845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80541857840088944697385013 7550799172508338565379845)
            ·
              refine ⟨1415774844845313481008721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7550799172508338565379845 1415774844845313481008721)
              ·
                refine ⟨1061831133633985110756541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415774844845313481008721 1061831133633985110756541)
                ·
                  refine ⟨398186675112744416533703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061831133633985110756541 398186675112744416533703)
                  ·
                    rfl

theorem cell20_872399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_872399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872399 prefixEnd_872399 := by exact prefixLift 872399
  have htrace : WordTrace (prefixWord ++ tailWord_872399) baseStart_872399 baseEnd_872399 := by
    simpa [prefixWord, tailWord_872399, baseEnd_872399] using wordTrace_append hprefix tailTrace_872399
  have hstable : (prefixWord ++ tailWord_872399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872399).length < 2 ^ (prefixWord ++ tailWord_872399).sum := by decide
  have hdescent : baseEnd_872399 < baseStart_872399 := by decide
  rcases family_descends (prefixWord ++ tailWord_872399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872409 : List Nat := [1, 2, 1, 2, 7, 1, 1, 5]
def baseStart_872409 : Nat := 118140960795 + 872409 * 2 ^ 59
def prefixEnd_872409 : Nat := 4983230072969 + 3 ^ 40 * 872409 * 2
def baseEnd_872409 : Nat := 132730413128409608733443

theorem tailTrace_872409 : CollatzResearch.WordTrace tailWord_872409 prefixEnd_872409 132730413128409608733443 := by
  unfold tailWord_872409
  simp only [CollatzResearch.WordTrace]
  refine ⟨31819370296418663440164281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21212913530945775626776187 31819370296418663440164281)
  ·
    refine ⟨23864527722313997580123211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31819370296418663440164281 23864527722313997580123211)
    ·
      refine ⟨35796791583470996370184817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23864527722313997580123211 35796791583470996370184817)
      ·
        refine ⟨26847593687603247277638613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35796791583470996370184817 26847593687603247277638613)
        ·
          refine ⟨629240477053201108069655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26847593687603247277638613 629240477053201108069655)
          ·
            refine ⟨943860715579801662104483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629240477053201108069655 943860715579801662104483)
            ·
              refine ⟨1415791073369702493156725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943860715579801662104483 1415791073369702493156725)
              ·
                refine ⟨132730413128409608733443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1415791073369702493156725 132730413128409608733443)
                ·
                  rfl

theorem cell20_872409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 5].length) (baseStart_872409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872409 prefixEnd_872409 := by exact prefixLift 872409
  have htrace : WordTrace (prefixWord ++ tailWord_872409) baseStart_872409 baseEnd_872409 := by
    simpa [prefixWord, tailWord_872409, baseEnd_872409] using wordTrace_append hprefix tailTrace_872409
  have hstable : (prefixWord ++ tailWord_872409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872409).length < 2 ^ (prefixWord ++ tailWord_872409).sum := by decide
  have hdescent : baseEnd_872409 < baseStart_872409 := by decide
  rcases family_descends (prefixWord ++ tailWord_872409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872423 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 4]
def baseStart_872423 : Nat := 118140960795 + 872423 * 2 ^ 59
def prefixEnd_872423 : Nat := 4983230072969 + 3 ^ 40 * 872423 * 2
def baseEnd_872423 : Nat := 398197629366706999733605

theorem tailTrace_872423 : CollatzResearch.WordTrace tailWord_872423 prefixEnd_872423 398197629366706999733605 := by
  unfold tailWord_872423
  simp only [CollatzResearch.WordTrace]
  refine ⟨31819880918367943831173923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21213253945578629220782615 31819880918367943831173923)
  ·
    refine ⟨47729821377551915746760885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31819880918367943831173923 47729821377551915746760885)
    ·
      refine ⟨4474670754145492101258833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47729821377551915746760885 4474670754145492101258833)
      ·
        refine ⟨3356003065609119075944125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4474670754145492101258833 3356003065609119075944125)
        ·
          refine ⟨1258501149603419653479047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3356003065609119075944125 1258501149603419653479047)
          ·
            refine ⟨1887751724405129480218571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258501149603419653479047 1887751724405129480218571)
            ·
              refine ⟨2831627586607694220327857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887751724405129480218571 2831627586607694220327857)
              ·
                refine ⟨2123720689955770665245893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831627586607694220327857 2123720689955770665245893)
                ·
                  refine ⟨398197629366706999733605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123720689955770665245893 398197629366706999733605)
                  ·
                    rfl

theorem cell20_872423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_872423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872423 prefixEnd_872423 := by exact prefixLift 872423
  have htrace : WordTrace (prefixWord ++ tailWord_872423) baseStart_872423 baseEnd_872423 := by
    simpa [prefixWord, tailWord_872423, baseEnd_872423] using wordTrace_append hprefix tailTrace_872423
  have hstable : (prefixWord ++ tailWord_872423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872423).length < 2 ^ (prefixWord ++ tailWord_872423).sum := by decide
  have hdescent : baseEnd_872423 < baseStart_872423 := by decide
  rcases family_descends (prefixWord ++ tailWord_872423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872471 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 3]
def baseStart_872471 : Nat := 118140960795 + 872471 * 2 ^ 59
def prefixEnd_872471 : Nat := 4983230072969 + 3 ^ 40 * 872471 * 2
def baseEnd_872471 : Nat := 398219537874632166133409

theorem tailTrace_872471 : CollatzResearch.WordTrace tailWord_872471 prefixEnd_872471 398219537874632166133409 := by
  unfold tailWord_872471
  simp only [CollatzResearch.WordTrace]
  refine ⟨31821631622194048028921267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21214421081462698685947511 31821631622194048028921267)
  ·
    refine ⟨47732447433291072043381901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31821631622194048028921267 47732447433291072043381901)
    ·
      refine ⟨17899667787484152016268213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47732447433291072043381901 17899667787484152016268213)
      ·
        refine ⟨1678093855076639251525145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17899667787484152016268213 1678093855076639251525145)
        ·
          refine ⟨1258570391307479438643859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678093855076639251525145 1258570391307479438643859)
          ·
            refine ⟨1887855586961219157965789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258570391307479438643859 1887855586961219157965789)
            ·
              refine ⟨707945845110457184237171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1887855586961219157965789 707945845110457184237171)
              ·
                refine ⟨1061918767665685776355757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707945845110457184237171 1061918767665685776355757)
                ·
                  refine ⟨398219537874632166133409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061918767665685776355757 398219537874632166133409)
                  ·
                    rfl

theorem cell20_872471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 3].length) (baseStart_872471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872471 prefixEnd_872471 := by exact prefixLift 872471
  have htrace : WordTrace (prefixWord ++ tailWord_872471) baseStart_872471 baseEnd_872471 := by
    simpa [prefixWord, tailWord_872471, baseEnd_872471] using wordTrace_append hprefix tailTrace_872471
  have hstable : (prefixWord ++ tailWord_872471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872471).length < 2 ^ (prefixWord ++ tailWord_872471).sum := by decide
  have hdescent : baseEnd_872471 < baseStart_872471 := by decide
  rcases family_descends (prefixWord ++ tailWord_872471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872482 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_872482 : Nat := 118140960795 + 872482 * 2 ^ 59
def prefixEnd_872482 : Nat := 4983230072969 + 3 ^ 40 * 872482 * 2
def baseEnd_872482 : Nat := 398224558574365016766697

theorem tailTrace_872482 : CollatzResearch.WordTrace tailWord_872482 prefixEnd_872482 398224558574365016766697 := by
  unfold tailWord_872482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7955508206288549226892925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21214688550102797938381133 7955508206288549226892925)
  ·
    refine ⟨2983315577358205960084847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7955508206288549226892925 2983315577358205960084847)
    ·
      refine ⟨4474973366037308940127271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983315577358205960084847 4474973366037308940127271)
      ·
        refine ⟨6712460049055963410190907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474973366037308940127271 6712460049055963410190907)
        ·
          refine ⟨10068690073583945115286361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712460049055963410190907 10068690073583945115286361)
          ·
            refine ⟨7551517555187958836464771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10068690073583945115286361 7551517555187958836464771)
            ·
              refine ⟨11327276332781938254697157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7551517555187958836464771 11327276332781938254697157)
              ·
                refine ⟨2123864312396613422755717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11327276332781938254697157 2123864312396613422755717)
                ·
                  refine ⟨398224558574365016766697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123864312396613422755717 398224558574365016766697)
                  ·
                    rfl

theorem cell20_872482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_872482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872482 prefixEnd_872482 := by exact prefixLift 872482
  have htrace : WordTrace (prefixWord ++ tailWord_872482) baseStart_872482 baseEnd_872482 := by
    simpa [prefixWord, tailWord_872482, baseEnd_872482] using wordTrace_append hprefix tailTrace_872482
  have hstable : (prefixWord ++ tailWord_872482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872482).length < 2 ^ (prefixWord ++ tailWord_872482).sum := by decide
  have hdescent : baseEnd_872482 < baseStart_872482 := by decide
  rcases family_descends (prefixWord ++ tailWord_872482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872496 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_872496 : Nat := 118140960795 + 872496 * 2 ^ 59
def prefixEnd_872496 : Nat := 4983230072969 + 3 ^ 40 * 872496 * 2
def baseEnd_872496 : Nat := 398230948555843190299973

theorem tailTrace_872496 : CollatzResearch.WordTrace tailWord_872496 prefixEnd_872496 398230948555843190299973 := by
  unfold tailWord_872496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15911271723551738649290671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21215028964735651532387561 15911271723551738649290671)
  ·
    refine ⟨23866907585327607973936007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15911271723551738649290671 23866907585327607973936007)
    ·
      refine ⟨35800361377991411960904011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23866907585327607973936007 35800361377991411960904011)
      ·
        refine ⟨53700542066987117941356017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35800361377991411960904011 53700542066987117941356017)
        ·
          refine ⟨40275406550240338456017013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53700542066987117941356017 40275406550240338456017013)
          ·
            refine ⟨3775819364085031730251595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40275406550240338456017013 3775819364085031730251595)
            ·
              refine ⟨5663729046127547595377393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775819364085031730251595 5663729046127547595377393)
              ·
                refine ⟨4247796784595660696533045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663729046127547595377393 4247796784595660696533045)
                ·
                  refine ⟨398230948555843190299973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247796784595660696533045 398230948555843190299973)
                  ·
                    rfl

theorem cell20_872496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_872496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872496 prefixEnd_872496 := by exact prefixLift 872496
  have htrace : WordTrace (prefixWord ++ tailWord_872496) baseStart_872496 baseEnd_872496 := by
    simpa [prefixWord, tailWord_872496, baseEnd_872496] using wordTrace_append hprefix tailTrace_872496
  have hstable : (prefixWord ++ tailWord_872496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872496).length < 2 ^ (prefixWord ++ tailWord_872496).sum := by decide
  have hdescent : baseEnd_872496 < baseStart_872496 := by decide
  rcases family_descends (prefixWord ++ tailWord_872496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872499 : List Nat := [1, 1, 1, 2, 4, 1, 5, 3, 2]
def baseStart_872499 : Nat := 118140960795 + 872499 * 2 ^ 59
def prefixEnd_872499 : Nat := 4983230072969 + 3 ^ 40 * 872499 * 2
def baseEnd_872499 : Nat := 398232317837588513199961

theorem tailTrace_872499 : CollatzResearch.WordTrace tailWord_872499 prefixEnd_872499 398232317837588513199961 := by
  unfold tailWord_872499
  simp only [CollatzResearch.WordTrace]
  refine ⟨31822652866092608810940551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21215101910728405873960367 31822652866092608810940551)
  ·
    refine ⟨47733979299138913216410827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31822652866092608810940551 47733979299138913216410827)
    ·
      refine ⟨71600968948708369824616241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47733979299138913216410827 71600968948708369824616241)
      ·
        refine ⟨53700726711531277368462181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71600968948708369824616241 53700726711531277368462181)
        ·
          refine ⟨10068886258412114506586659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53700726711531277368462181 10068886258412114506586659)
          ·
            refine ⟨15103329387618171759879989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10068886258412114506586659 15103329387618171759879989)
            ·
              refine ⟨1415937130089203602488749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15103329387618171759879989 1415937130089203602488749)
              ·
                refine ⟨530976423783451350933281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1415937130089203602488749 530976423783451350933281)
                ·
                  refine ⟨398232317837588513199961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530976423783451350933281 398232317837588513199961)
                  ·
                    rfl

theorem cell20_872499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 2].length) (baseStart_872499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872499 prefixEnd_872499 := by exact prefixLift 872499
  have htrace : WordTrace (prefixWord ++ tailWord_872499) baseStart_872499 baseEnd_872499 := by
    simpa [prefixWord, tailWord_872499, baseEnd_872499] using wordTrace_append hprefix tailTrace_872499
  have hstable : (prefixWord ++ tailWord_872499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872499).length < 2 ^ (prefixWord ++ tailWord_872499).sum := by decide
  have hdescent : baseEnd_872499 < baseStart_872499 := by decide
  rcases family_descends (prefixWord ++ tailWord_872499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872503 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_872503 : Nat := 118140960795 + 872503 * 2 ^ 59
def prefixEnd_872503 : Nat := 4983230072969 + 3 ^ 40 * 872503 * 2
def baseEnd_872503 : Nat := 398234143546582277066611

theorem tailTrace_872503 : CollatzResearch.WordTrace tailWord_872503 prefixEnd_872503 398234143546582277066611 := by
  unfold tailWord_872503
  simp only [CollatzResearch.WordTrace]
  refine ⟨31822798758078117494086163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21215199172052078329390775 31822798758078117494086163)
  ·
    refine ⟨47734198137117176241129245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31822798758078117494086163 47734198137117176241129245)
    ·
      refine ⟨17900324301418941090423467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47734198137117176241129245 17900324301418941090423467)
      ·
        refine ⟨26850486452128411635635201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17900324301418941090423467 26850486452128411635635201)
        ·
          refine ⟨20137864839096308726726401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26850486452128411635635201 20137864839096308726726401)
          ·
            refine ⟨15103398629322231545044801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20137864839096308726726401 15103398629322231545044801)
            ·
              refine ⟨11327548971991673658783601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15103398629322231545044801 11327548971991673658783601)
              ·
                refine ⟨8495661728993755244087701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11327548971991673658783601 8495661728993755244087701)
                ·
                  refine ⟨398234143546582277066611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8495661728993755244087701 398234143546582277066611)
                  ·
                    rfl

theorem cell20_872503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_872503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872503 prefixEnd_872503 := by exact prefixLift 872503
  have htrace : WordTrace (prefixWord ++ tailWord_872503) baseStart_872503 baseEnd_872503 := by
    simpa [prefixWord, tailWord_872503, baseEnd_872503] using wordTrace_append hprefix tailTrace_872503
  have hstable : (prefixWord ++ tailWord_872503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872503).length < 2 ^ (prefixWord ++ tailWord_872503).sum := by decide
  have hdescent : baseEnd_872503 < baseStart_872503 := by decide
  rcases family_descends (prefixWord ++ tailWord_872503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872513 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_872513 : Nat := 118140960795 + 872513 * 2 ^ 59
def prefixEnd_872513 : Nat := 4983230072969 + 3 ^ 40 * 872513 * 2
def baseEnd_872513 : Nat := 398238707819066686733237

theorem tailTrace_872513 : CollatzResearch.WordTrace tailWord_872513 prefixEnd_872513 398238707819066686733237 := by
  unfold tailWord_872513
  simp only [CollatzResearch.WordTrace]
  refine ⟨31823163488041889201950193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21215442325361259467966795 31823163488041889201950193)
  ·
    refine ⟨23867372616031416901462645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31823163488041889201950193 23867372616031416901462645)
    ·
      refine ⟨2237566182752945334512123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23867372616031416901462645 2237566182752945334512123)
      ·
        refine ⟨3356349274129418001768185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237566182752945334512123 3356349274129418001768185)
        ·
          refine ⟨2517261955597063501326139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3356349274129418001768185 2517261955597063501326139)
          ·
            refine ⟨3775892933395595251989209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517261955597063501326139 3775892933395595251989209)
            ·
              refine ⟨2831919700046696438991907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3775892933395595251989209 2831919700046696438991907)
              ·
                refine ⟨4247879550070044658487861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831919700046696438991907 4247879550070044658487861)
                ·
                  refine ⟨398238707819066686733237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247879550070044658487861 398238707819066686733237)
                  ·
                    rfl

theorem cell20_872513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_872513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872513 prefixEnd_872513 := by exact prefixLift 872513
  have htrace : WordTrace (prefixWord ++ tailWord_872513) baseStart_872513 baseEnd_872513 := by
    simpa [prefixWord, tailWord_872513, baseEnd_872513] using wordTrace_append hprefix tailTrace_872513
  have hstable : (prefixWord ++ tailWord_872513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872513).length < 2 ^ (prefixWord ++ tailWord_872513).sum := by decide
  have hdescent : baseEnd_872513 < baseStart_872513 := by decide
  rcases family_descends (prefixWord ++ tailWord_872513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872530 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_872530 : Nat := 118140960795 + 872530 * 2 ^ 59
def prefixEnd_872530 : Nat := 4983230072969 + 3 ^ 40 * 872530 * 2
def baseEnd_872530 : Nat := 398246467082290183166501

theorem tailTrace_872530 : CollatzResearch.WordTrace tailWord_872530 prefixEnd_872530 398246467082290183166501 := by
  unfold tailWord_872530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7955945882245075276329761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21215855685986867403546029 7955945882245075276329761)
  ·
    refine ⟨5966959411683806457247321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7955945882245075276329761 5966959411683806457247321)
    ·
      refine ⟨4475219558762854842935491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5966959411683806457247321 4475219558762854842935491)
      ·
        refine ⟨6712829338144282264403237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4475219558762854842935491 6712829338144282264403237)
        ·
          refine ⟨1258655500902052924575607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6712829338144282264403237 1258655500902052924575607)
          ·
            refine ⟨1887983251353079386863411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258655500902052924575607 1887983251353079386863411)
            ·
              refine ⟨2831974877029619080295117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887983251353079386863411 2831974877029619080295117)
              ·
                refine ⟨1061990578886107155110669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2831974877029619080295117 1061990578886107155110669)
                ·
                  refine ⟨398246467082290183166501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061990578886107155110669 398246467082290183166501)
                  ·
                    rfl

theorem cell20_872530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_872530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872530 prefixEnd_872530 := by exact prefixLift 872530
  have htrace : WordTrace (prefixWord ++ tailWord_872530) baseStart_872530 baseEnd_872530 := by
    simpa [prefixWord, tailWord_872530, baseEnd_872530] using wordTrace_append hprefix tailTrace_872530
  have hstable : (prefixWord ++ tailWord_872530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872530).length < 2 ^ (prefixWord ++ tailWord_872530).sum := by decide
  have hdescent : baseEnd_872530 < baseStart_872530 := by decide
  rcases family_descends (prefixWord ++ tailWord_872530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872613 : List Nat := [1, 3, 1, 2, 1, 3, 4, 3, 2]
def baseStart_872613 : Nat := 118140960795 + 872613 * 2 ^ 59
def prefixEnd_872613 : Nat := 4983230072969 + 3 ^ 40 * 872613 * 2
def baseEnd_872613 : Nat := 398284350543910783399495

theorem tailTrace_872613 : CollatzResearch.WordTrace tailWord_872613 prefixEnd_872613 398284350543910783399495 := by
  unfold tailWord_872613
  simp only [CollatzResearch.WordTrace]
  refine ⟨31826810787679606280590493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21217873858453070853726995 31826810787679606280590493)
  ·
    refine ⟨11935054045379852355221435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31826810787679606280590493 11935054045379852355221435)
    ·
      refine ⟨17902581068069778532832153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11935054045379852355221435 17902581068069778532832153)
      ·
        refine ⟨13426935801052333899624115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17902581068069778532832153 13426935801052333899624115)
        ·
          refine ⟨20140403701578500849436173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13426935801052333899624115 20140403701578500849436173)
          ·
            refine ⟨7552651388091937818538565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20140403701578500849436173 7552651388091937818538565)
            ·
              refine ⟨1416122135267238340975981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7552651388091937818538565 1416122135267238340975981)
              ·
                refine ⟨531045800725214377865993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1416122135267238340975981 531045800725214377865993)
                ·
                  refine ⟨398284350543910783399495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531045800725214377865993 398284350543910783399495)
                  ·
                    rfl

theorem cell20_872613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_872613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872613 prefixEnd_872613 := by exact prefixLift 872613
  have htrace : WordTrace (prefixWord ++ tailWord_872613) baseStart_872613 baseEnd_872613 := by
    simpa [prefixWord, tailWord_872613, baseEnd_872613] using wordTrace_append hprefix tailTrace_872613
  have hstable : (prefixWord ++ tailWord_872613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872613).length < 2 ^ (prefixWord ++ tailWord_872613).sum := by decide
  have hdescent : baseEnd_872613 < baseStart_872613 := by decide
  rcases family_descends (prefixWord ++ tailWord_872613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872655 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_872655 : Nat := 118140960795 + 872655 * 2 ^ 59
def prefixEnd_872655 : Nat := 4983230072969 + 3 ^ 40 * 872655 * 2
def baseEnd_872655 : Nat := 398303520488345303999323

theorem tailTrace_872655 : CollatzResearch.WordTrace tailWord_872655 prefixEnd_872655 398303520488345303999323 := by
  unfold tailWord_872655
  simp only [CollatzResearch.WordTrace]
  refine ⟨31828342653527447453619419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21218895102351631635746279 31828342653527447453619419)
  ·
    refine ⟨47742513980291171180429129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31828342653527447453619419 47742513980291171180429129)
    ·
      refine ⟨35806885485218378385321847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47742513980291171180429129 35806885485218378385321847)
      ·
        refine ⟨53710328227827567577982771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35806885485218378385321847 53710328227827567577982771)
        ·
          refine ⟨80565492341741351366974157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53710328227827567577982771 80565492341741351366974157)
          ·
            refine ⟨30212059628153006762615309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80565492341741351366974157 30212059628153006762615309)
            ·
              refine ⟨11329522360557377535980741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30212059628153006762615309 11329522360557377535980741)
              ·
                refine ⟨2124285442604508287996389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11329522360557377535980741 2124285442604508287996389)
                ·
                  refine ⟨398303520488345303999323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124285442604508287996389 398303520488345303999323)
                  ·
                    rfl

theorem cell20_872655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_872655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872655 prefixEnd_872655 := by exact prefixLift 872655
  have htrace : WordTrace (prefixWord ++ tailWord_872655) baseStart_872655 baseEnd_872655 := by
    simpa [prefixWord, tailWord_872655, baseEnd_872655] using wordTrace_append hprefix tailTrace_872655
  have hstable : (prefixWord ++ tailWord_872655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872655).length < 2 ^ (prefixWord ++ tailWord_872655).sum := by decide
  have hdescent : baseEnd_872655 < baseStart_872655 := by decide
  rcases family_descends (prefixWord ++ tailWord_872655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872658 : List Nat := [3, 2, 2, 2, 1, 2, 4, 4]
def baseStart_872658 : Nat := 118140960795 + 872658 * 2 ^ 59
def prefixEnd_872658 : Nat := 4983230072969 + 3 ^ 40 * 872658 * 2
def baseEnd_872658 : Nat := 132768296590030208966437

theorem tailTrace_872658 : CollatzResearch.WordTrace tailWord_872658 prefixEnd_872658 132768296590030208966437 := by
  unfold tailWord_872658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957113018129144741494657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21218968048344385977319085 7957113018129144741494657)
  ·
    refine ⟨5967834763596858556120993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7957113018129144741494657 5967834763596858556120993)
    ·
      refine ⟨4475876072697643917090745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5967834763596858556120993 4475876072697643917090745)
      ·
        refine ⟨3356907054523232937818059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4475876072697643917090745 3356907054523232937818059)
        ·
          refine ⟨5035360581784849406727089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356907054523232937818059 5035360581784849406727089)
          ·
            refine ⟨3776520436338637055045317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5035360581784849406727089 3776520436338637055045317)
            ·
              refine ⟨708097581813494447820997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3776520436338637055045317 708097581813494447820997)
              ·
                refine ⟨132768296590030208966437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708097581813494447820997 132768296590030208966437)
                ·
                  rfl

theorem cell20_872658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_872658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872658 prefixEnd_872658 := by exact prefixLift 872658
  have htrace : WordTrace (prefixWord ++ tailWord_872658) baseStart_872658 baseEnd_872658 := by
    simpa [prefixWord, tailWord_872658, baseEnd_872658] using wordTrace_append hprefix tailTrace_872658
  have hstable : (prefixWord ++ tailWord_872658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872658).length < 2 ^ (prefixWord ++ tailWord_872658).sum := by decide
  have hdescent : baseEnd_872658 < baseStart_872658 := by decide
  rcases family_descends (prefixWord ++ tailWord_872658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872675 : List Nat := [1, 1, 1, 8, 2, 1, 6]
def baseStart_872675 : Nat := 118140960795 + 872675 * 2 ^ 59
def prefixEnd_872675 : Nat := 4983230072969 + 3 ^ 40 * 872675 * 2
def baseEnd_872675 : Nat := 44256961003701569259175

theorem tailTrace_872675 : CollatzResearch.WordTrace tailWord_872675 prefixEnd_872675 44256961003701569259175 := by
  unfold tailWord_872675
  simp only [CollatzResearch.WordTrace]
  refine ⟨31829072113454990869347479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21219381408969993912898319 31829072113454990869347479)
  ·
    refine ⟨47743608170182486304021219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31829072113454990869347479 47743608170182486304021219)
    ·
      refine ⟨71615412255273729456031829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47743608170182486304021219 71615412255273729456031829)
      ·
        refine ⟨839243112366489017062873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 71615412255273729456031829 839243112366489017062873)
        ·
          refine ⟨629432334274866762797155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839243112366489017062873 629432334274866762797155)
          ·
            refine ⟨944148501412300144195733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629432334274866762797155 944148501412300144195733)
            ·
              refine ⟨44256961003701569259175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 944148501412300144195733 44256961003701569259175)
              ·
                rfl

theorem cell20_872675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 6].length) (baseStart_872675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872675 prefixEnd_872675 := by exact prefixLift 872675
  have htrace : WordTrace (prefixWord ++ tailWord_872675) baseStart_872675 baseEnd_872675 := by
    simpa [prefixWord, tailWord_872675, baseEnd_872675] using wordTrace_append hprefix tailTrace_872675
  have hstable : (prefixWord ++ tailWord_872675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872675).length < 2 ^ (prefixWord ++ tailWord_872675).sum := by decide
  have hdescent : baseEnd_872675 < baseStart_872675 := by decide
  rcases family_descends (prefixWord ++ tailWord_872675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872679 : List Nat := [1, 1, 5, 3, 1, 1, 8]
def baseStart_872679 : Nat := 118140960795 + 872679 * 2 ^ 59
def prefixEnd_872679 : Nat := 4983230072969 + 3 ^ 40 * 872679 * 2
def baseEnd_872679 : Nat := 44257163860256431911025

theorem tailTrace_872679 : CollatzResearch.WordTrace tailWord_872679 prefixEnd_872679 44257163860256431911025 := by
  unfold tailWord_872679
  simp only [CollatzResearch.WordTrace]
  refine ⟨31829218005440499552493091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21219478670293666368328727 31829218005440499552493091)
  ·
    refine ⟨47743827008160749328739637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31829218005440499552493091 47743827008160749328739637)
    ·
      refine ⟨4475983782015070249569341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47743827008160749328739637 4475983782015070249569341)
      ·
        refine ⟨1678493918255651343588503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4475983782015070249569341 1678493918255651343588503)
        ·
          refine ⟨2517740877383477015382755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678493918255651343588503 2517740877383477015382755)
          ·
            refine ⟨3776611316075215523074133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517740877383477015382755 3776611316075215523074133)
            ·
              refine ⟨44257163860256431911025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3776611316075215523074133 44257163860256431911025)
              ·
                rfl

theorem cell20_872679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 8].length) (baseStart_872679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872679 prefixEnd_872679 := by exact prefixLift 872679
  have htrace : WordTrace (prefixWord ++ tailWord_872679) baseStart_872679 baseEnd_872679 := by
    simpa [prefixWord, tailWord_872679, baseEnd_872679] using wordTrace_append hprefix tailTrace_872679
  have hstable : (prefixWord ++ tailWord_872679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872679).length < 2 ^ (prefixWord ++ tailWord_872679).sum := by decide
  have hdescent : baseEnd_872679 < baseStart_872679 := by decide
  rcases family_descends (prefixWord ++ tailWord_872679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872685 : List Nat := [1, 5, 1, 2, 3, 1, 3, 2, 2]
def baseStart_872685 : Nat := 118140960795 + 872685 * 2 ^ 59
def prefixEnd_872685 : Nat := 4983230072969 + 3 ^ 40 * 872685 * 2
def baseEnd_872685 : Nat := 398317213305798532999201

theorem tailTrace_872685 : CollatzResearch.WordTrace tailWord_872685 prefixEnd_872685 398317213305798532999201 := by
  unfold tailWord_872685
  simp only [CollatzResearch.WordTrace]
  refine ⟨31829436843418762577211509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21219624562279175051474339 31829436843418762577211509)
  ·
    refine ⟨2984009704070508991613579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31829436843418762577211509 2984009704070508991613579)
    ·
      refine ⟨4476014556105763487420369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2984009704070508991613579 4476014556105763487420369)
      ·
        refine ⟨3357010917079322615565277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4476014556105763487420369 3357010917079322615565277)
        ·
          refine ⟨1258879093904745980836979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3357010917079322615565277 1258879093904745980836979)
          ·
            refine ⟨1888318640857118971255469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258879093904745980836979 1888318640857118971255469)
            ·
              refine ⟨708119490321419614220801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1888318640857118971255469 708119490321419614220801)
              ·
                refine ⟨531089617741064710665601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708119490321419614220801 531089617741064710665601)
                ·
                  refine ⟨398317213305798532999201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531089617741064710665601 398317213305798532999201)
                  ·
                    rfl

theorem cell20_872685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_872685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872685 prefixEnd_872685 := by exact prefixLift 872685
  have htrace : WordTrace (prefixWord ++ tailWord_872685) baseStart_872685 baseEnd_872685 := by
    simpa [prefixWord, tailWord_872685, baseEnd_872685] using wordTrace_append hprefix tailTrace_872685
  have hstable : (prefixWord ++ tailWord_872685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872685).length < 2 ^ (prefixWord ++ tailWord_872685).sum := by decide
  have hdescent : baseEnd_872685 < baseStart_872685 := by decide
  rcases family_descends (prefixWord ++ tailWord_872685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872734 : List Nat := [4, 3, 2, 1, 1, 9]
def baseStart_872734 : Nat := 118140960795 + 872734 * 2 ^ 59
def prefixEnd_872734 : Nat := 4983230072969 + 3 ^ 40 * 872734 * 2
def baseEnd_872734 : Nat := 14753317712628597791321

theorem tailTrace_872734 : CollatzResearch.WordTrace tailWord_872734 prefixEnd_872734 14753317712628597791321 := by
  unfold tailWord_872734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978903002530155493218157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21220816013494162630496837 3978903002530155493218157)
  ·
    refine ⟨1492088625948808309956809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3978903002530155493218157 1492088625948808309956809)
    ·
      refine ⟨1119066469461606232467607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1492088625948808309956809 1119066469461606232467607)
      ·
        refine ⟨1678599704192409348701411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119066469461606232467607 1678599704192409348701411)
        ·
          refine ⟨2517899556288614023052117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678599704192409348701411 2517899556288614023052117)
          ·
            refine ⟨14753317712628597791321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2517899556288614023052117 14753317712628597791321)
            ·
              rfl

theorem cell20_872734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 9].length) (baseStart_872734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872734 prefixEnd_872734 := by exact prefixLift 872734
  have htrace : WordTrace (prefixWord ++ tailWord_872734) baseStart_872734 baseEnd_872734 := by
    simpa [prefixWord, tailWord_872734, baseEnd_872734] using wordTrace_append hprefix tailTrace_872734
  have hstable : (prefixWord ++ tailWord_872734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872734).length < 2 ^ (prefixWord ++ tailWord_872734).sum := by decide
  have hdescent : baseEnd_872734 < baseStart_872734 := by decide
  rcases family_descends (prefixWord ++ tailWord_872734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872744 : List Nat := [2, 1, 5, 1, 3, 1, 1, 4, 2]
def baseStart_872744 : Nat := 118140960795 + 872744 * 2 ^ 59
def prefixEnd_872744 : Nat := 4983230072969 + 3 ^ 40 * 872744 * 2
def baseEnd_872744 : Nat := 398344142513456550032293

theorem tailTrace_872744 : CollatzResearch.WordTrace tailWord_872744 prefixEnd_872744 398344142513456550032293 := by
  unfold tailWord_872744
  simp only [CollatzResearch.WordTrace]
  refine ⟨15915794375102507826804643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21221059166803343769072857 15915794375102507826804643)
  ·
    refine ⟨23873691562653761740206965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15915794375102507826804643 23873691562653761740206965)
    ·
      refine ⟨2238158583998790163144403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23873691562653761740206965 2238158583998790163144403)
      ·
        refine ⟨3357237875998185244716605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238158583998790163144403 3357237875998185244716605)
        ·
          refine ⟨1258964203499319466768727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3357237875998185244716605 1258964203499319466768727)
          ·
            refine ⟨1888446305248979200153091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258964203499319466768727 1888446305248979200153091)
            ·
              refine ⟨2832669457873468800229637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888446305248979200153091 2832669457873468800229637)
              ·
                refine ⟨531125523351275400043057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2832669457873468800229637 531125523351275400043057)
                ·
                  refine ⟨398344142513456550032293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531125523351275400043057 398344142513456550032293)
                  ·
                    rfl

theorem cell20_872744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_872744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872744 prefixEnd_872744 := by exact prefixLift 872744
  have htrace : WordTrace (prefixWord ++ tailWord_872744) baseStart_872744 baseEnd_872744 := by
    simpa [prefixWord, tailWord_872744, baseEnd_872744] using wordTrace_append hprefix tailTrace_872744
  have hstable : (prefixWord ++ tailWord_872744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872744).length < 2 ^ (prefixWord ++ tailWord_872744).sum := by decide
  have hdescent : baseEnd_872744 < baseStart_872744 := by decide
  rcases family_descends (prefixWord ++ tailWord_872744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872776 : List Nat := [2, 1, 3, 1, 1, 2, 2, 8]
def baseStart_872776 : Nat := 118140960795 + 872776 * 2 ^ 59
def prefixEnd_872776 : Nat := 4983230072969 + 3 ^ 40 * 872776 * 2
def baseEnd_872776 : Nat := 132786249395135553655165

theorem tailTrace_872776 : CollatzResearch.WordTrace tailWord_872776 prefixEnd_872776 132786249395135553655165 := by
  unfold tailWord_872776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916377943044542559387091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21221837257392723412516121 15916377943044542559387091)
  ·
    refine ⟨23874566914566813839080637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15916377943044542559387091 23874566914566813839080637)
    ·
      refine ⟨8952962592962555189655239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23874566914566813839080637 8952962592962555189655239)
      ·
        refine ⟨13429443889443832784482859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8952962592962555189655239 13429443889443832784482859)
        ·
          refine ⟨20144165834165749176724289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429443889443832784482859 20144165834165749176724289)
          ·
            refine ⟨15108124375624311882543217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20144165834165749176724289 15108124375624311882543217)
            ·
              refine ⟨11331093281718233911907413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15108124375624311882543217 11331093281718233911907413)
              ·
                refine ⟨132786249395135553655165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11331093281718233911907413 132786249395135553655165)
                ·
                  rfl

theorem cell20_872776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_872776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872776 prefixEnd_872776 := by exact prefixLift 872776
  have htrace : WordTrace (prefixWord ++ tailWord_872776) baseStart_872776 baseEnd_872776 := by
    simpa [prefixWord, tailWord_872776, baseEnd_872776] using wordTrace_append hprefix tailTrace_872776
  have hstable : (prefixWord ++ tailWord_872776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872776).length < 2 ^ (prefixWord ++ tailWord_872776).sum := by decide
  have hdescent : baseEnd_872776 < baseStart_872776 := by decide
  rcases family_descends (prefixWord ++ tailWord_872776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872796 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_872796 : Nat := 118140960795 + 872796 * 2 ^ 59
def prefixEnd_872796 : Nat := 4983230072969 + 3 ^ 40 * 872796 * 2
def baseEnd_872796 : Nat := 398367876730375480298747

theorem tailTrace_872796 : CollatzResearch.WordTrace tailWord_872796 prefixEnd_872796 398367876730375480298747 := by
  unfold tailWord_872796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916742673008314267251121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21222323564011085689668161 15916742673008314267251121)
  ·
    refine ⟨11937557004756235700438341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15916742673008314267251121 11937557004756235700438341)
    ·
      refine ⟨2238291938391794193832189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11937557004756235700438341 2238291938391794193832189)
      ·
        refine ⟨839359476896922822687071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2238291938391794193832189 839359476896922822687071)
        ·
          refine ⟨1259039215345384234030607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839359476896922822687071 1259039215345384234030607)
          ·
            refine ⟨1888558823018076351045911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259039215345384234030607 1888558823018076351045911)
            ·
              refine ⟨2832838234527114526568867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888558823018076351045911 2832838234527114526568867)
              ·
                refine ⟨4249257351790671789853301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2832838234527114526568867 4249257351790671789853301)
                ·
                  refine ⟨398367876730375480298747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4249257351790671789853301 398367876730375480298747)
                  ·
                    rfl

theorem cell20_872796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_872796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872796 prefixEnd_872796 := by exact prefixLift 872796
  have htrace : WordTrace (prefixWord ++ tailWord_872796) baseStart_872796 baseEnd_872796 := by
    simpa [prefixWord, tailWord_872796, baseEnd_872796] using wordTrace_append hprefix tailTrace_872796
  have hstable : (prefixWord ++ tailWord_872796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872796).length < 2 ^ (prefixWord ++ tailWord_872796).sum := by decide
  have hdescent : baseEnd_872796 < baseStart_872796 := by decide
  rcases family_descends (prefixWord ++ tailWord_872796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872841 : List Nat := [1, 2, 1, 1, 6, 1, 3, 3, 2]
def baseStart_872841 : Nat := 118140960795 + 872841 * 2 ^ 59
def prefixEnd_872841 : Nat := 4983230072969 + 3 ^ 40 * 872841 * 2
def baseEnd_872841 : Nat := 398388415956555323798563

theorem tailTrace_872841 : CollatzResearch.WordTrace tailWord_872841 prefixEnd_872841 398388415956555323798563 := by
  unfold tailWord_872841
  simp only [CollatzResearch.WordTrace]
  refine ⟨31835126630853601219890377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21223417753902400813260251 31835126630853601219890377)
  ·
    refine ⟨23876344973140200914917783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31835126630853601219890377 23876344973140200914917783)
    ·
      refine ⟨35814517459710301372376675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23876344973140200914917783 35814517459710301372376675)
      ·
        refine ⟨53721776189565452058565013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35814517459710301372376675 53721776189565452058565013)
        ·
          refine ⟨2518208258885880565245235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53721776189565452058565013 2518208258885880565245235)
          ·
            refine ⟨3777312388328820847867853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518208258885880565245235 3777312388328820847867853)
            ·
              refine ⟨1416492145623307817950445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3777312388328820847867853 1416492145623307817950445)
              ·
                refine ⟨531184554608740431731417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1416492145623307817950445 531184554608740431731417)
                ·
                  refine ⟨398388415956555323798563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531184554608740431731417 398388415956555323798563)
                  ·
                    rfl

theorem cell20_872841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_872841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872841 prefixEnd_872841 := by exact prefixLift 872841
  have htrace : WordTrace (prefixWord ++ tailWord_872841) baseStart_872841 baseEnd_872841 := by
    simpa [prefixWord, tailWord_872841, baseEnd_872841] using wordTrace_append hprefix tailTrace_872841
  have hstable : (prefixWord ++ tailWord_872841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872841).length < 2 ^ (prefixWord ++ tailWord_872841).sum := by decide
  have hdescent : baseEnd_872841 < baseStart_872841 := by decide
  rcases family_descends (prefixWord ++ tailWord_872841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872854 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_872854 : Nat := 118140960795 + 872854 * 2 ^ 59
def prefixEnd_872854 : Nat := 4983230072969 + 3 ^ 40 * 872854 * 2
def baseEnd_872854 : Nat := 398394349510785056365177

theorem tailTrace_872854 : CollatzResearch.WordTrace tailWord_872854 prefixEnd_872854 398394349510785056365177 := by
  unfold tailWord_872854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989725048737906527507101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21223733853204336293409077 1989725048737906527507101)
  ·
    refine ⟨746146893276714947815163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1989725048737906527507101 746146893276714947815163)
    ·
      refine ⟨1119220339915072421722745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 746146893276714947815163 1119220339915072421722745)
      ·
        refine ⟨839415254936304316292059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1119220339915072421722745 839415254936304316292059)
        ·
          refine ⟨1259122882404456474438089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839415254936304316292059 1259122882404456474438089)
          ·
            refine ⟨944342161803342355828567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259122882404456474438089 944342161803342355828567)
            ·
              refine ⟨1416513242705013533742851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944342161803342355828567 1416513242705013533742851)
              ·
                refine ⟨2124769864057520300614277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416513242705013533742851 2124769864057520300614277)
                ·
                  refine ⟨398394349510785056365177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124769864057520300614277 398394349510785056365177)
                  ·
                    rfl

theorem cell20_872854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_872854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872854 prefixEnd_872854 := by exact prefixLift 872854
  have htrace : WordTrace (prefixWord ++ tailWord_872854) baseStart_872854 baseEnd_872854 := by
    simpa [prefixWord, tailWord_872854, baseEnd_872854] using wordTrace_append hprefix tailTrace_872854
  have hstable : (prefixWord ++ tailWord_872854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872854).length < 2 ^ (prefixWord ++ tailWord_872854).sum := by decide
  have hdescent : baseEnd_872854 < baseStart_872854 := by decide
  rcases family_descends (prefixWord ++ tailWord_872854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872858 : List Nat := [3, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_872858 : Nat := 118140960795 + 872858 * 2 ^ 59
def prefixEnd_872858 : Nat := 4983230072969 + 3 ^ 40 * 872858 * 2
def baseEnd_872858 : Nat := 398396175219778820231827

theorem tailTrace_872858 : CollatzResearch.WordTrace tailWord_872858 prefixEnd_872858 398396175219778820231827 := by
  unfold tailWord_872858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958936667948003280814807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21223831114528008748839485 7958936667948003280814807)
  ·
    refine ⟨11938405001922004921222211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7958936667948003280814807 11938405001922004921222211)
    ·
      refine ⟨17907607502883007381833317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11938405001922004921222211 17907607502883007381833317)
      ·
        refine ⟨3357676406790563884093747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17907607502883007381833317 3357676406790563884093747)
        ·
          refine ⟨5036514610185845826140621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357676406790563884093747 5036514610185845826140621)
          ·
            refine ⟨1888692978819692184802733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5036514610185845826140621 1888692978819692184802733)
            ·
              refine ⟨708259867057384569301025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1888692978819692184802733 708259867057384569301025)
              ·
                refine ⟨531194900293038426975769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708259867057384569301025 531194900293038426975769)
                ·
                  refine ⟨398396175219778820231827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531194900293038426975769 398396175219778820231827)
                  ·
                    rfl

theorem cell20_872858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_872858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872858 prefixEnd_872858 := by exact prefixLift 872858
  have htrace : WordTrace (prefixWord ++ tailWord_872858) baseStart_872858 baseEnd_872858 := by
    simpa [prefixWord, tailWord_872858, baseEnd_872858] using wordTrace_append hprefix tailTrace_872858
  have hstable : (prefixWord ++ tailWord_872858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872858).length < 2 ^ (prefixWord ++ tailWord_872858).sum := by decide
  have hdescent : baseEnd_872858 < baseStart_872858 := by decide
  rcases family_descends (prefixWord ++ tailWord_872858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872872 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_872872 : Nat := 118140960795 + 872872 * 2 ^ 59
def prefixEnd_872872 : Nat := 4983230072969 + 3 ^ 40 * 872872 * 2
def baseEnd_872872 : Nat := 398402565201256993765103

theorem tailTrace_872872 : CollatzResearch.WordTrace tailWord_872872 prefixEnd_872872 398402565201256993765103 := by
  unfold tailWord_872872
  simp only [CollatzResearch.WordTrace]
  refine ⟨15918128646870646757134435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21224171529160862342845913 15918128646870646757134435)
  ·
    refine ⟨23877192970305970135701653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15918128646870646757134435 23877192970305970135701653)
    ·
      refine ⟨1119243420483092350111015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23877192970305970135701653 1119243420483092350111015)
      ·
        refine ⟨1678865130724638525166523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119243420483092350111015 1678865130724638525166523)
        ·
          refine ⟨2518297696086957787749785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678865130724638525166523 2518297696086957787749785)
          ·
            refine ⟨1888723272065218340812339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518297696086957787749785 1888723272065218340812339)
            ·
              refine ⟨2833084908097827511218509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888723272065218340812339 2833084908097827511218509)
              ·
                refine ⟨1062406840536685316706941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2833084908097827511218509 1062406840536685316706941)
                ·
                  refine ⟨398402565201256993765103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062406840536685316706941 398402565201256993765103)
                  ·
                    rfl

theorem cell20_872872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_872872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872872 prefixEnd_872872 := by exact prefixLift 872872
  have htrace : WordTrace (prefixWord ++ tailWord_872872) baseStart_872872 baseEnd_872872 := by
    simpa [prefixWord, tailWord_872872, baseEnd_872872] using wordTrace_append hprefix tailTrace_872872
  have hstable : (prefixWord ++ tailWord_872872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872872).length < 2 ^ (prefixWord ++ tailWord_872872).sum := by decide
  have hdescent : baseEnd_872872 < baseStart_872872 := by decide
  rcases family_descends (prefixWord ++ tailWord_872872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872917 : List Nat := [1, 3, 2, 3, 1, 3, 1, 4, 2]
def baseStart_872917 : Nat := 118140960795 + 872917 * 2 ^ 59
def prefixEnd_872917 : Nat := 4983230072969 + 3 ^ 40 * 872917 * 2
def baseEnd_872917 : Nat := 398423104427436837264919

theorem tailTrace_872917 : CollatzResearch.WordTrace tailWord_872917 prefixEnd_872917 398423104427436837264919 := by
  unfold tailWord_872917
  simp only [CollatzResearch.WordTrace]
  refine ⟨31837898578578266199657005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21225265719052177466438003 31837898578578266199657005)
  ·
    refine ⟨11939211966966849824871377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31837898578578266199657005 11939211966966849824871377)
    ·
      refine ⟨8954408975225137368653533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11939211966966849824871377 8954408975225137368653533)
      ·
        refine ⟨3357903365709426513245075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8954408975225137368653533 3357903365709426513245075)
        ·
          refine ⟨5036855048564139769867613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357903365709426513245075 5036855048564139769867613)
          ·
            refine ⟨1888820643211552413700355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5036855048564139769867613 1888820643211552413700355)
            ·
              refine ⟨2833230964817328620550533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888820643211552413700355 2833230964817328620550533)
              ·
                refine ⟨531230805903249116353225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2833230964817328620550533 531230805903249116353225)
                ·
                  refine ⟨398423104427436837264919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531230805903249116353225 398423104427436837264919)
                  ·
                    rfl

theorem cell20_872917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_872917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872917 prefixEnd_872917 := by exact prefixLift 872917
  have htrace : WordTrace (prefixWord ++ tailWord_872917) baseStart_872917 baseEnd_872917 := by
    simpa [prefixWord, tailWord_872917, baseEnd_872917] using wordTrace_append hprefix tailTrace_872917
  have hstable : (prefixWord ++ tailWord_872917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872917).length < 2 ^ (prefixWord ++ tailWord_872917).sum := by decide
  have hdescent : baseEnd_872917 < baseStart_872917 := by decide
  rcases family_descends (prefixWord ++ tailWord_872917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872921 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_872921 : Nat := 118140960795 + 872921 * 2 ^ 59
def prefixEnd_872921 : Nat := 4983230072969 + 3 ^ 40 * 872921 * 2
def baseEnd_872921 : Nat := 398424930136430601131569

theorem tailTrace_872921 : CollatzResearch.WordTrace tailWord_872921 prefixEnd_872921 398424930136430601131569 := by
  unfold tailWord_872921
  simp only [CollatzResearch.WordTrace]
  refine ⟨31838044470563774882802617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21225362980375849921868411 31838044470563774882802617)
  ·
    refine ⟨23878533352922831162101963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31838044470563774882802617 23878533352922831162101963)
    ·
      refine ⟨35817800029384246743152945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23878533352922831162101963 35817800029384246743152945)
      ·
        refine ⟨26863350022038185057364709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35817800029384246743152945 26863350022038185057364709)
        ·
          refine ⟨5036878129132159698255883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26863350022038185057364709 5036878129132159698255883)
          ·
            refine ⟨7555317193698239547383825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036878129132159698255883 7555317193698239547383825)
            ·
              refine ⟨5666487895273679660537869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7555317193698239547383825 5666487895273679660537869)
              ·
                refine ⟨2124932960727629872701701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5666487895273679660537869 2124932960727629872701701)
                ·
                  refine ⟨398424930136430601131569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124932960727629872701701 398424930136430601131569)
                  ·
                    rfl

theorem cell20_872921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_872921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872921 prefixEnd_872921 := by exact prefixLift 872921
  have htrace : WordTrace (prefixWord ++ tailWord_872921) baseStart_872921 baseEnd_872921 := by
    simpa [prefixWord, tailWord_872921, baseEnd_872921] using wordTrace_append hprefix tailTrace_872921
  have hstable : (prefixWord ++ tailWord_872921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872921).length < 2 ^ (prefixWord ++ tailWord_872921).sum := by decide
  have hdescent : baseEnd_872921 < baseStart_872921 := by decide
  rcases family_descends (prefixWord ++ tailWord_872921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872938 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_872938 : Nat := 118140960795 + 872938 * 2 ^ 59
def prefixEnd_872938 : Nat := 4983230072969 + 3 ^ 40 * 872938 * 2
def baseEnd_872938 : Nat := 398432689399654097564833

theorem tailTrace_872938 : CollatzResearch.WordTrace tailWord_872938 prefixEnd_872938 398432689399654097564833 := by
  unfold tailWord_872938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7959666127875546696542867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21225776341001457857447645 7959666127875546696542867)
  ·
    refine ⟨11939499191813320044814301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7959666127875546696542867 11939499191813320044814301)
    ·
      refine ⟨4477312196929995016805363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11939499191813320044814301 4477312196929995016805363)
      ·
        refine ⟨6715968295394992525208045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477312196929995016805363 6715968295394992525208045)
        ·
          refine ⟨2518488110773122196953017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6715968295394992525208045 2518488110773122196953017)
          ·
            refine ⟨1888866083079841647714763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518488110773122196953017 1888866083079841647714763)
            ·
              refine ⟨2833299124619762471572145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888866083079841647714763 2833299124619762471572145)
              ·
                refine ⟨2124974343464821853679109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833299124619762471572145 2124974343464821853679109)
                ·
                  refine ⟨398432689399654097564833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124974343464821853679109 398432689399654097564833)
                  ·
                    rfl

theorem cell20_872938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_872938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872938 prefixEnd_872938 := by exact prefixLift 872938
  have htrace : WordTrace (prefixWord ++ tailWord_872938) baseStart_872938 baseEnd_872938 := by
    simpa [prefixWord, tailWord_872938, baseEnd_872938] using wordTrace_append hprefix tailTrace_872938
  have hstable : (prefixWord ++ tailWord_872938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872938).length < 2 ^ (prefixWord ++ tailWord_872938).sum := by decide
  have hdescent : baseEnd_872938 < baseStart_872938 := by decide
  rcases family_descends (prefixWord ++ tailWord_872938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872945 : List Nat := [1, 2, 2, 2, 3, 1, 5, 4]
def baseStart_872945 : Nat := 118140960795 + 872945 * 2 ^ 59
def prefixEnd_872945 : Nat := 4983230072969 + 3 ^ 40 * 872945 * 2
def baseEnd_872945 : Nat := 132811961463464394777157

theorem tailTrace_872945 : CollatzResearch.WordTrace tailWord_872945 prefixEnd_872945 132811961463464394777157 := by
  unfold tailWord_872945
  simp only [CollatzResearch.WordTrace]
  refine ⟨31838919822476826981676289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21225946548317884654450859 31838919822476826981676289)
  ·
    refine ⟨23879189866857620236257217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31838919822476826981676289 23879189866857620236257217)
    ·
      refine ⟨17909392400143215177192913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23879189866857620236257217 17909392400143215177192913)
      ·
        refine ⟨13432044300107411382894685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17909392400143215177192913 13432044300107411382894685)
        ·
          refine ⟨5037016612540279268585507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13432044300107411382894685 5037016612540279268585507)
          ·
            refine ⟨7555524918810418902878261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037016612540279268585507 7555524918810418902878261)
            ·
              refine ⟨708330461138476772144837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7555524918810418902878261 708330461138476772144837)
              ·
                refine ⟨132811961463464394777157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708330461138476772144837 132811961463464394777157)
                ·
                  rfl

theorem cell20_872945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 4].length) (baseStart_872945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872945 prefixEnd_872945 := by exact prefixLift 872945
  have htrace : WordTrace (prefixWord ++ tailWord_872945) baseStart_872945 baseEnd_872945 := by
    simpa [prefixWord, tailWord_872945, baseEnd_872945] using wordTrace_append hprefix tailTrace_872945
  have hstable : (prefixWord ++ tailWord_872945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872945).length < 2 ^ (prefixWord ++ tailWord_872945).sum := by decide
  have hdescent : baseEnd_872945 < baseStart_872945 := by decide
  rcases family_descends (prefixWord ++ tailWord_872945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872962 : List Nat := [3, 4, 1, 2, 2, 1, 7]
def baseStart_872962 : Nat := 118140960795 + 872962 * 2 ^ 59
def prefixEnd_872962 : Nat := 4983230072969 + 3 ^ 40 * 872962 * 2
def baseEnd_872962 : Nat := 44271515961512964529415

theorem tailTrace_872962 : CollatzResearch.WordTrace tailWord_872962 prefixEnd_872962 44271515961512964529415 := by
  unfold tailWord_872962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7959884965853809721261285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21226359908943492590030093 7959884965853809721261285)
  ·
    refine ⟨1492478431097589322736491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7959884965853809721261285 1492478431097589322736491)
    ·
      refine ⟨2238717646646383984104737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492478431097589322736491 2238717646646383984104737)
      ·
        refine ⟨1679038234984787988078553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2238717646646383984104737 1679038234984787988078553)
        ·
          refine ⟨1259278676238590991058915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1679038234984787988078553 1259278676238590991058915)
          ·
            refine ⟨1888918014357886486588373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259278676238590991058915 1888918014357886486588373)
            ·
              refine ⟨44271515961512964529415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1888918014357886486588373 44271515961512964529415)
              ·
                rfl

theorem cell20_872962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 7].length) (baseStart_872962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872962 prefixEnd_872962 := by exact prefixLift 872962
  have htrace : WordTrace (prefixWord ++ tailWord_872962) baseStart_872962 baseEnd_872962 := by
    simpa [prefixWord, tailWord_872962, baseEnd_872962] using wordTrace_append hprefix tailTrace_872962
  have hstable : (prefixWord ++ tailWord_872962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872962).length < 2 ^ (prefixWord ++ tailWord_872962).sum := by decide
  have hdescent : baseEnd_872962 < baseStart_872962 := by decide
  rcases family_descends (prefixWord ++ tailWord_872962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872996 : List Nat := [2, 3, 1, 5, 2, 1, 2, 4]
def baseStart_872996 : Nat := 118140960795 + 872996 * 2 ^ 59
def prefixEnd_872996 : Nat := 4983230072969 + 3 ^ 40 * 872996 * 2
def baseEnd_872996 : Nat := 132819720726687891210421

theorem tailTrace_872996 : CollatzResearch.WordTrace tailWord_872996 prefixEnd_872996 132819720726687891210421 := by
  unfold tailWord_872996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15920389972646031345891421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21227186630194708461188561 15920389972646031345891421)
  ·
    refine ⟨5970146239742261754709283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15920389972646031345891421 5970146239742261754709283)
    ·
      refine ⟨8955219359613392632063925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5970146239742261754709283 8955219359613392632063925)
      ·
        refine ⟨839551814963755559255993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8955219359613392632063925 839551814963755559255993)
        ·
          refine ⟨629663861222816669441995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839551814963755559255993 629663861222816669441995)
          ·
            refine ⟨944495791834225004162993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629663861222816669441995 944495791834225004162993)
            ·
              refine ⟨708371843875668753122245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944495791834225004162993 708371843875668753122245)
              ·
                refine ⟨132819720726687891210421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708371843875668753122245 132819720726687891210421)
                ·
                  rfl

theorem cell20_872996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_872996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872996 prefixEnd_872996 := by exact prefixLift 872996
  have htrace : WordTrace (prefixWord ++ tailWord_872996) baseStart_872996 baseEnd_872996 := by
    simpa [prefixWord, tailWord_872996, baseEnd_872996] using wordTrace_append hprefix tailTrace_872996
  have hstable : (prefixWord ++ tailWord_872996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872996).length < 2 ^ (prefixWord ++ tailWord_872996).sum := by decide
  have hdescent : baseEnd_872996 < baseStart_872996 := by decide
  rcases family_descends (prefixWord ++ tailWord_872996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872997 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_872997 : Nat := 118140960795 + 872997 * 2 ^ 59
def prefixEnd_872997 : Nat := 4983230072969 + 3 ^ 40 * 872997 * 2
def baseEnd_872997 : Nat := 398459618607312114597925

theorem tailTrace_872997 : CollatzResearch.WordTrace tailWord_872997 prefixEnd_872997 398459618607312114597925 := by
  unfold tailWord_872997
  simp only [CollatzResearch.WordTrace]
  refine ⟨31840816418288439862569245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21227210945525626575046163 31840816418288439862569245)
  ·
    refine ⟨11940306156858164948463467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31840816418288439862569245 11940306156858164948463467)
    ·
      refine ⟨17910459235287247422695201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11940306156858164948463467 17910459235287247422695201)
      ·
        refine ⟨13432844426465435567021401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17910459235287247422695201 13432844426465435567021401)
        ·
          refine ⟨10074633319849076675266051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13432844426465435567021401 10074633319849076675266051)
          ·
            refine ⟨15111949979773615012899077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10074633319849076675266051 15111949979773615012899077)
            ·
              refine ⟨2833490621207552814918577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15111949979773615012899077 2833490621207552814918577)
              ·
                refine ⟨2125117965905664611188933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833490621207552814918577 2125117965905664611188933)
                ·
                  refine ⟨398459618607312114597925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2125117965905664611188933 398459618607312114597925)
                  ·
                    rfl

theorem cell20_872997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_872997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_872997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_872997 prefixEnd_872997 := by exact prefixLift 872997
  have htrace : WordTrace (prefixWord ++ tailWord_872997) baseStart_872997 baseEnd_872997 := by
    simpa [prefixWord, tailWord_872997, baseEnd_872997] using wordTrace_append hprefix tailTrace_872997
  have hstable : (prefixWord ++ tailWord_872997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872997).length < 2 ^ (prefixWord ++ tailWord_872997).sum := by decide
  have hdescent : baseEnd_872997 < baseStart_872997 := by decide
  rcases family_descends (prefixWord ++ tailWord_872997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873000 : List Nat := [2, 1, 5, 2, 1, 1, 4, 4]
def baseStart_873000 : Nat := 118140960795 + 873000 * 2 ^ 59
def prefixEnd_873000 : Nat := 4983230072969 + 3 ^ 40 * 873000 * 2
def baseEnd_873000 : Nat := 132820329296352479165971

theorem tailTrace_873000 : CollatzResearch.WordTrace tailWord_873000 prefixEnd_873000 132820329296352479165971 := by
  unfold tailWord_873000
  simp only [CollatzResearch.WordTrace]
  refine ⟨15920462918638785687464227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21227283891518380916618969 15920462918638785687464227)
  ·
    refine ⟨23880694377958178531196341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15920462918638785687464227 23880694377958178531196341)
    ·
      refine ⟨2238815097933579237299657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23880694377958178531196341 2238815097933579237299657)
      ·
        refine ⟨1679111323450184427974743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2238815097933579237299657 1679111323450184427974743)
        ·
          refine ⟨2518666985175276641962115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679111323450184427974743 2518666985175276641962115)
          ·
            refine ⟨3778000477762914962943173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518666985175276641962115 3778000477762914962943173)
            ·
              refine ⟨708375089580546555551845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3778000477762914962943173 708375089580546555551845)
              ·
                refine ⟨132820329296352479165971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708375089580546555551845 132820329296352479165971)
                ·
                  rfl

theorem cell20_873000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_873000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873000 prefixEnd_873000 := by exact prefixLift 873000
  have htrace : WordTrace (prefixWord ++ tailWord_873000) baseStart_873000 baseEnd_873000 := by
    simpa [prefixWord, tailWord_873000, baseEnd_873000] using wordTrace_append hprefix tailTrace_873000
  have hstable : (prefixWord ++ tailWord_873000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873000).length < 2 ^ (prefixWord ++ tailWord_873000).sum := by decide
  have hdescent : baseEnd_873000 < baseStart_873000 := by decide
  rcases family_descends (prefixWord ++ tailWord_873000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873011 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_873011 : Nat := 118140960795 + 873011 * 2 ^ 59
def prefixEnd_873011 : Nat := 4983230072969 + 3 ^ 40 * 873011 * 2
def baseEnd_873011 : Nat := 398466008588790288131201

theorem tailTrace_873011 : CollatzResearch.WordTrace tailWord_873011 prefixEnd_873011 398466008588790288131201 := by
  unfold tailWord_873011
  simp only [CollatzResearch.WordTrace]
  refine ⟨31841327040237720253578887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21227551360158480169052591 31841327040237720253578887)
  ·
    refine ⟨47761990560356580380368331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31841327040237720253578887 47761990560356580380368331)
    ·
      refine ⟨71642985840534870570552497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47761990560356580380368331 71642985840534870570552497)
      ·
        refine ⟨53732239380401152927914373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71642985840534870570552497 53732239380401152927914373)
        ·
          refine ⟨10074794883825216173983945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53732239380401152927914373 10074794883825216173983945)
          ·
            refine ⟨7556096162868912130487959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10074794883825216173983945 7556096162868912130487959)
            ·
              refine ⟨11334144244303368195731939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7556096162868912130487959 11334144244303368195731939)
              ·
                refine ⟨17001216366455052293597909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11334144244303368195731939 17001216366455052293597909)
                ·
                  refine ⟨398466008588790288131201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17001216366455052293597909 398466008588790288131201)
                  ·
                    rfl

theorem cell20_873011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_873011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873011 prefixEnd_873011 := by exact prefixLift 873011
  have htrace : WordTrace (prefixWord ++ tailWord_873011) baseStart_873011 baseEnd_873011 := by
    simpa [prefixWord, tailWord_873011, baseEnd_873011] using wordTrace_append hprefix tailTrace_873011
  have hstable : (prefixWord ++ tailWord_873011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873011).length < 2 ^ (prefixWord ++ tailWord_873011).sum := by decide
  have hdescent : baseEnd_873011 < baseStart_873011 := by decide
  rcases family_descends (prefixWord ++ tailWord_873011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873021 : List Nat := [1, 4, 1, 3, 2, 3, 6]
def baseStart_873021 : Nat := 118140960795 + 873021 * 2 ^ 59
def prefixEnd_873021 : Nat := 4983230072969 + 3 ^ 40 * 873021 * 2
def baseEnd_873021 : Nat := 44274508095697188644203

theorem tailTrace_873021 : CollatzResearch.WordTrace tailWord_873021 prefixEnd_873021 44274508095697188644203 := by
  unfold tailWord_873021
  simp only [CollatzResearch.WordTrace]
  refine ⟨31841691770201491961442917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21227794513467661307628611 31841691770201491961442917)
  ·
    refine ⟨5970317206912779742770547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31841691770201491961442917 5970317206912779742770547)
    ·
      refine ⟨8955475810369169614155821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5970317206912779742770547 8955475810369169614155821)
      ·
        refine ⟨3358303428888438605308433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8955475810369169614155821 3358303428888438605308433)
        ·
          refine ⟨2518727571666328953981325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3358303428888438605308433 2518727571666328953981325)
          ·
            refine ⟨944522839374873357742997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2518727571666328953981325 944522839374873357742997)
            ·
              refine ⟨44274508095697188644203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 944522839374873357742997 44274508095697188644203)
              ·
                rfl

theorem cell20_873021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 6].length) (baseStart_873021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873021 prefixEnd_873021 := by exact prefixLift 873021
  have htrace : WordTrace (prefixWord ++ tailWord_873021) baseStart_873021 baseEnd_873021 := by
    simpa [prefixWord, tailWord_873021, baseEnd_873021] using wordTrace_append hprefix tailTrace_873021
  have hstable : (prefixWord ++ tailWord_873021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873021).length < 2 ^ (prefixWord ++ tailWord_873021).sum := by decide
  have hdescent : baseEnd_873021 < baseStart_873021 := by decide
  rcases family_descends (prefixWord ++ tailWord_873021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873035 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_873035 : Nat := 118140960795 + 873035 * 2 ^ 59
def prefixEnd_873035 : Nat := 4983230072969 + 3 ^ 40 * 873035 * 2
def baseEnd_873035 : Nat := 398476962842752871331103

theorem tailTrace_873035 : CollatzResearch.WordTrace tailWord_873035 prefixEnd_873035 398476962842752871331103 := by
  unfold tailWord_873035
  simp only [CollatzResearch.WordTrace]
  refine ⟨31842202392150772352452559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21228134928100514901635039 31842202392150772352452559)
  ·
    refine ⟨47763303588226158528678839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31842202392150772352452559 47763303588226158528678839)
    ·
      refine ⟨71644955382339237793018259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47763303588226158528678839 71644955382339237793018259)
      ·
        refine ⟨107467433073508856689527389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71644955382339237793018259 107467433073508856689527389)
        ·
          refine ⟨40300287402565821258572771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107467433073508856689527389 40300287402565821258572771)
          ·
            refine ⟨60450431103848731887859157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40300287402565821258572771 60450431103848731887859157)
            ·
              refine ⟨1416806978996454653621699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60450431103848731887859157 1416806978996454653621699)
              ·
                refine ⟨2125210468494681980432549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416806978996454653621699 2125210468494681980432549)
                ·
                  refine ⟨398476962842752871331103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2125210468494681980432549 398476962842752871331103)
                  ·
                    rfl

theorem cell20_873035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_873035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873035 prefixEnd_873035 := by exact prefixLift 873035
  have htrace : WordTrace (prefixWord ++ tailWord_873035) baseStart_873035 baseEnd_873035 := by
    simpa [prefixWord, tailWord_873035, baseEnd_873035] using wordTrace_append hprefix tailTrace_873035
  have hstable : (prefixWord ++ tailWord_873035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873035).length < 2 ^ (prefixWord ++ tailWord_873035).sum := by decide
  have hdescent : baseEnd_873035 < baseStart_873035 := by decide
  rcases family_descends (prefixWord ++ tailWord_873035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873045 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 3]
def baseStart_873045 : Nat := 118140960795 + 873045 * 2 ^ 59
def prefixEnd_873045 : Nat := 4983230072969 + 3 ^ 40 * 873045 * 2
def baseEnd_873045 : Nat := 398481527115237280997729

theorem tailTrace_873045 : CollatzResearch.WordTrace tailWord_873045 prefixEnd_873045 398481527115237280997729 := by
  unfold tailWord_873045
  simp only [CollatzResearch.WordTrace]
  refine ⟨31842567122114544060316589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21228378081409696040211059 31842567122114544060316589)
  ·
    refine ⟨11940962670792954022618721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31842567122114544060316589 11940962670792954022618721)
    ·
      refine ⟨8955722003094715516964041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11940962670792954022618721 8955722003094715516964041)
      ·
        refine ⟨6716791502321036637723031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8955722003094715516964041 6716791502321036637723031)
        ·
          refine ⟨10075187253481554956584547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716791502321036637723031 10075187253481554956584547)
          ·
            refine ⟨15112780880222332434876821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075187253481554956584547 15112780880222332434876821)
            ·
              refine ⟨708411603760421832884851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15112780880222332434876821 708411603760421832884851)
              ·
                refine ⟨1062617405640632749327277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708411603760421832884851 1062617405640632749327277)
                ·
                  refine ⟨398481527115237280997729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062617405640632749327277 398481527115237280997729)
                  ·
                    rfl

theorem cell20_873045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_873045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873045 prefixEnd_873045 := by exact prefixLift 873045
  have htrace : WordTrace (prefixWord ++ tailWord_873045) baseStart_873045 baseEnd_873045 := by
    simpa [prefixWord, tailWord_873045, baseEnd_873045] using wordTrace_append hprefix tailTrace_873045
  have hstable : (prefixWord ++ tailWord_873045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873045).length < 2 ^ (prefixWord ++ tailWord_873045).sum := by decide
  have hdescent : baseEnd_873045 < baseStart_873045 := by decide
  rcases family_descends (prefixWord ++ tailWord_873045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873111 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_873111 : Nat := 118140960795 + 873111 * 2 ^ 59
def prefixEnd_873111 : Nat := 4983230072969 + 3 ^ 40 * 873111 * 2
def baseEnd_873111 : Nat := 398511651313634384797459

theorem tailTrace_873111 : CollatzResearch.WordTrace tailWord_873111 prefixEnd_873111 398511651313634384797459 := by
  unfold tailWord_873111
  simp only [CollatzResearch.WordTrace]
  refine ⟨31844974339875437332219187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21229982893250291554812791 31844974339875437332219187)
  ·
    refine ⟨47767461509813155998328781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31844974339875437332219187 47767461509813155998328781)
    ·
      refine ⟨17912798066179933499373293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47767461509813155998328781 17912798066179933499373293)
      ·
        refine ⟨6717299274817475062264985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17912798066179933499373293 6717299274817475062264985)
        ·
          refine ⟨5037974456113106296698739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6717299274817475062264985 5037974456113106296698739)
          ·
            refine ⟨7556961684169659445048109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037974456113106296698739 7556961684169659445048109)
            ·
              refine ⟨2833860631563622291893041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7556961684169659445048109 2833860631563622291893041)
              ·
                refine ⟨2125395473672716718919781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2833860631563622291893041 2125395473672716718919781)
                ·
                  refine ⟨398511651313634384797459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2125395473672716718919781 398511651313634384797459)
                  ·
                    rfl

theorem cell20_873111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_873111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873111 prefixEnd_873111 := by exact prefixLift 873111
  have htrace : WordTrace (prefixWord ++ tailWord_873111) baseStart_873111 baseEnd_873111 := by
    simpa [prefixWord, tailWord_873111, baseEnd_873111] using wordTrace_append hprefix tailTrace_873111
  have hstable : (prefixWord ++ tailWord_873111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873111).length < 2 ^ (prefixWord ++ tailWord_873111).sum := by decide
  have hdescent : baseEnd_873111 < baseStart_873111 := by decide
  rcases family_descends (prefixWord ++ tailWord_873111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873125 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_873125 : Nat := 118140960795 + 873125 * 2 ^ 59
def prefixEnd_873125 : Nat := 4983230072969 + 3 ^ 40 * 873125 * 2
def baseEnd_873125 : Nat := 398518041295112558330735

theorem tailTrace_873125 : CollatzResearch.WordTrace tailWord_873125 prefixEnd_873125 398518041295112558330735 := by
  unfold tailWord_873125
  simp only [CollatzResearch.WordTrace]
  refine ⟨31845484961824717723228829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21230323307883145148819219 31845484961824717723228829)
  ·
    refine ⟨11942056860684269146210811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31845484961824717723228829 11942056860684269146210811)
    ·
      refine ⟨17913085291026403719316217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11942056860684269146210811 17913085291026403719316217)
      ·
        refine ⟨13434813968269802789487163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17913085291026403719316217 13434813968269802789487163)
        ·
          refine ⟨20152220952404704184230745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13434813968269802789487163 20152220952404704184230745)
          ·
            refine ⟨15114165714303528138173059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20152220952404704184230745 15114165714303528138173059)
            ·
              refine ⟨22671248571455292207259589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15114165714303528138173059 22671248571455292207259589)
              ·
                refine ⟨4250859107147867288861173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22671248571455292207259589 4250859107147867288861173)
                ·
                  refine ⟨398518041295112558330735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4250859107147867288861173 398518041295112558330735)
                  ·
                    rfl

theorem cell20_873125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_873125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873125 prefixEnd_873125 := by exact prefixLift 873125
  have htrace : WordTrace (prefixWord ++ tailWord_873125) baseStart_873125 baseEnd_873125 := by
    simpa [prefixWord, tailWord_873125, baseEnd_873125] using wordTrace_append hprefix tailTrace_873125
  have hstable : (prefixWord ++ tailWord_873125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873125).length < 2 ^ (prefixWord ++ tailWord_873125).sum := by decide
  have hdescent : baseEnd_873125 < baseStart_873125 := by decide
  rcases family_descends (prefixWord ++ tailWord_873125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873149 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_873149 : Nat := 118140960795 + 873149 * 2 ^ 59
def prefixEnd_873149 : Nat := 4983230072969 + 3 ^ 40 * 873149 * 2
def baseEnd_873149 : Nat := 398528995549075141530637

theorem tailTrace_873149 : CollatzResearch.WordTrace tailWord_873149 prefixEnd_873149 398528995549075141530637 := by
  unfold tailWord_873149
  simp only [CollatzResearch.WordTrace]
  refine ⟨31846360313737769822102501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21230906875825179881401667 31846360313737769822102501)
  ·
    refine ⟨5971192558825831841644219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31846360313737769822102501 5971192558825831841644219)
    ·
      refine ⟨8956788838238747762466329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971192558825831841644219 8956788838238747762466329)
      ·
        refine ⟨6717591628679060821849747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8956788838238747762466329 6717591628679060821849747)
        ·
          refine ⟨10076387443018591232774621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717591628679060821849747 10076387443018591232774621)
          ·
            refine ⟨3778645291131971712290483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10076387443018591232774621 3778645291131971712290483)
            ·
              refine ⟨5667967936697957568435725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778645291131971712290483 5667967936697957568435725)
              ·
                refine ⟨2125487976261734088163397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5667967936697957568435725 2125487976261734088163397)
                ·
                  refine ⟨398528995549075141530637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2125487976261734088163397 398528995549075141530637)
                  ·
                    rfl

theorem cell20_873149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_873149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873149 prefixEnd_873149 := by exact prefixLift 873149
  have htrace : WordTrace (prefixWord ++ tailWord_873149) baseStart_873149 baseEnd_873149 := by
    simpa [prefixWord, tailWord_873149, baseEnd_873149] using wordTrace_append hprefix tailTrace_873149
  have hstable : (prefixWord ++ tailWord_873149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873149).length < 2 ^ (prefixWord ++ tailWord_873149).sum := by decide
  have hdescent : baseEnd_873149 < baseStart_873149 := by decide
  rcases family_descends (prefixWord ++ tailWord_873149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873183 : List Nat := [1, 1, 2, 3, 2, 5, 1, 3, 2]
def baseStart_873183 : Nat := 118140960795 + 873183 * 2 ^ 59
def prefixEnd_873183 : Nat := 4983230072969 + 3 ^ 40 * 873183 * 2
def baseEnd_873183 : Nat := 398544514075522134397165

theorem tailTrace_873183 : CollatzResearch.WordTrace tailWord_873183 prefixEnd_873183 398544514075522134397165 := by
  unfold tailWord_873183
  simp only [CollatzResearch.WordTrace]
  refine ⟨31847600395614593628840203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21231733597076395752560135 31847600395614593628840203)
  ·
    refine ⟨47771400593421890443260305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31847600395614593628840203 47771400593421890443260305)
    ·
      refine ⟨35828550445066417832445229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47771400593421890443260305 35828550445066417832445229)
      ·
        refine ⟨13435706416899906687166961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35828550445066417832445229 13435706416899906687166961)
        ·
          refine ⟨10076779812674930015375221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13435706416899906687166961 10076779812674930015375221)
          ·
            refine ⟨944698107438274688941427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10076779812674930015375221 944698107438274688941427)
            ·
              refine ⟨1417047161157412033412141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944698107438274688941427 1417047161157412033412141)
              ·
                refine ⟨531392685434029512529553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417047161157412033412141 531392685434029512529553)
                ·
                  refine ⟨398544514075522134397165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531392685434029512529553 398544514075522134397165)
                  ·
                    rfl

theorem cell20_873183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 2].length) (baseStart_873183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873183 prefixEnd_873183 := by exact prefixLift 873183
  have htrace : WordTrace (prefixWord ++ tailWord_873183) baseStart_873183 baseEnd_873183 := by
    simpa [prefixWord, tailWord_873183, baseEnd_873183] using wordTrace_append hprefix tailTrace_873183
  have hstable : (prefixWord ++ tailWord_873183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873183).length < 2 ^ (prefixWord ++ tailWord_873183).sum := by decide
  have hdescent : baseEnd_873183 < baseStart_873183 := by decide
  rcases family_descends (prefixWord ++ tailWord_873183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873201 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_873201 : Nat := 118140960795 + 873201 * 2 ^ 59
def prefixEnd_873201 : Nat := 4983230072969 + 3 ^ 40 * 873201 * 2
def baseEnd_873201 : Nat := 398552729765994071797091

theorem tailTrace_873201 : CollatzResearch.WordTrace tailWord_873201 prefixEnd_873201 398552729765994071797091 := by
  unfold tailWord_873201
  simp only [CollatzResearch.WordTrace]
  refine ⟨31848256909549382702995457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21232171273032921801996971 31848256909549382702995457)
  ·
    refine ⟨23886192682162037027246593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31848256909549382702995457 23886192682162037027246593)
    ·
      refine ⟨17914644511621527770434945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23886192682162037027246593 17914644511621527770434945)
      ·
        refine ⟨13435983383716145827826209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17914644511621527770434945 13435983383716145827826209)
        ·
          refine ⟨10076987537787109370869657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13435983383716145827826209 10076987537787109370869657)
          ·
            refine ⟨7557740653340332028152243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10076987537787109370869657 7557740653340332028152243)
            ·
              refine ⟨11336610980010498042228365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7557740653340332028152243 11336610980010498042228365)
              ·
                refine ⟨4251229117503936765835637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11336610980010498042228365 4251229117503936765835637)
                ·
                  refine ⟨398552729765994071797091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4251229117503936765835637 398552729765994071797091)
                  ·
                    rfl

theorem cell20_873201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_873201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873201 prefixEnd_873201 := by exact prefixLift 873201
  have htrace : WordTrace (prefixWord ++ tailWord_873201) baseStart_873201 baseEnd_873201 := by
    simpa [prefixWord, tailWord_873201, baseEnd_873201] using wordTrace_append hprefix tailTrace_873201
  have hstable : (prefixWord ++ tailWord_873201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873201).length < 2 ^ (prefixWord ++ tailWord_873201).sum := by decide
  have hdescent : baseEnd_873201 < baseStart_873201 := by decide
  rcases family_descends (prefixWord ++ tailWord_873201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873214 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_873214 : Nat := 118140960795 + 873214 * 2 ^ 59
def prefixEnd_873214 : Nat := 4983230072969 + 3 ^ 40 * 873214 * 2
def baseEnd_873214 : Nat := 398558663320223804363705

theorem tailTrace_873214 : CollatzResearch.WordTrace tailWord_873214 prefixEnd_873214 398558663320223804363705 := by
  unfold tailWord_873214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981091382312785740402337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21232487372334857282145797 3981091382312785740402337)
  ·
    refine ⟨2985818536734589305301753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3981091382312785740402337 2985818536734589305301753)
    ·
      refine ⟨2239363902550941978976315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2985818536734589305301753 2239363902550941978976315)
      ·
        refine ⟨3359045853826412968464473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239363902550941978976315 3359045853826412968464473)
        ·
          refine ⟨2519284390369809726348355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3359045853826412968464473 2519284390369809726348355)
          ·
            refine ⟨3778926585554714589522533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519284390369809726348355 3778926585554714589522533)
            ·
              refine ⟨708548734791508985535475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3778926585554714589522533 708548734791508985535475)
              ·
                refine ⟨1062823102187263478303213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708548734791508985535475 1062823102187263478303213)
                ·
                  refine ⟨398558663320223804363705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062823102187263478303213 398558663320223804363705)
                  ·
                    rfl

theorem cell20_873214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_873214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873214 prefixEnd_873214 := by exact prefixLift 873214
  have htrace : WordTrace (prefixWord ++ tailWord_873214) baseStart_873214 baseEnd_873214 := by
    simpa [prefixWord, tailWord_873214, baseEnd_873214] using wordTrace_append hprefix tailTrace_873214
  have hstable : (prefixWord ++ tailWord_873214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873214).length < 2 ^ (prefixWord ++ tailWord_873214).sum := by decide
  have hdescent : baseEnd_873214 < baseStart_873214 := by decide
  rcases family_descends (prefixWord ++ tailWord_873214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873242 : List Nat := [3, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_873242 : Nat := 118140960795 + 873242 * 2 ^ 59
def prefixEnd_873242 : Nat := 4983230072969 + 3 ^ 40 * 873242 * 2
def baseEnd_873242 : Nat := 398571443283180151430257

theorem tailTrace_873242 : CollatzResearch.WordTrace tailWord_873242 prefixEnd_873242 398571443283180151430257 := by
  unfold tailWord_873242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7962438075600211676309495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21233168201600564470158653 7962438075600211676309495)
  ·
    refine ⟨11943657113400317514464243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7962438075600211676309495 11943657113400317514464243)
    ·
      refine ⟨17915485670100476271696365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11943657113400317514464243 17915485670100476271696365)
      ·
        refine ⟨6718307126287678601886137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17915485670100476271696365 6718307126287678601886137)
        ·
          refine ⟨5038730344715758951414603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6718307126287678601886137 5038730344715758951414603)
          ·
            refine ⟨7558095517073638427121905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038730344715758951414603 7558095517073638427121905)
            ·
              refine ⟨5668571637805228820341429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7558095517073638427121905 5668571637805228820341429)
              ·
                refine ⟨531428591044240201907009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5668571637805228820341429 531428591044240201907009)
                ·
                  refine ⟨398571443283180151430257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531428591044240201907009 398571443283180151430257)
                  ·
                    rfl

theorem cell20_873242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_873242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873242 prefixEnd_873242 := by exact prefixLift 873242
  have htrace : WordTrace (prefixWord ++ tailWord_873242) baseStart_873242 baseEnd_873242 := by
    simpa [prefixWord, tailWord_873242, baseEnd_873242] using wordTrace_append hprefix tailTrace_873242
  have hstable : (prefixWord ++ tailWord_873242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873242).length < 2 ^ (prefixWord ++ tailWord_873242).sum := by decide
  have hdescent : baseEnd_873242 < baseStart_873242 := by decide
  rcases family_descends (prefixWord ++ tailWord_873242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873297 : List Nat := [1, 2, 2, 1, 6, 1, 2, 3, 2]
def baseStart_873297 : Nat := 118140960795 + 873297 * 2 ^ 59
def prefixEnd_873297 : Nat := 4983230072969 + 3 ^ 40 * 873297 * 2
def baseEnd_873297 : Nat := 398596546781844404596699

theorem tailTrace_873297 : CollatzResearch.WordTrace tailWord_873297 prefixEnd_873297 398596546781844404596699 := by
  unfold tailWord_873297
  simp only [CollatzResearch.WordTrace]
  refine ⟨31851758317201591098490145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21234505544801060732326763 31851758317201591098490145)
  ·
    refine ⟨23888818737901193323867609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31851758317201591098490145 23888818737901193323867609)
    ·
      refine ⟨17916614053425894992900707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23888818737901193323867609 17916614053425894992900707)
      ·
        refine ⟨26874921080138842489351061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17916614053425894992900707 26874921080138842489351061)
        ·
          refine ⟨1259761925631508241688331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26874921080138842489351061 1259761925631508241688331)
          ·
            refine ⟨1889642888447262362532497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259761925631508241688331 1889642888447262362532497)
            ·
              refine ⟨1417232166335446771899373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889642888447262362532497 1417232166335446771899373)
              ·
                refine ⟨531462062375792539462265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417232166335446771899373 531462062375792539462265)
                ·
                  refine ⟨398596546781844404596699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531462062375792539462265 398596546781844404596699)
                  ·
                    rfl

theorem cell20_873297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_873297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873297 prefixEnd_873297 := by exact prefixLift 873297
  have htrace : WordTrace (prefixWord ++ tailWord_873297) baseStart_873297 baseEnd_873297 := by
    simpa [prefixWord, tailWord_873297, baseEnd_873297] using wordTrace_append hprefix tailTrace_873297
  have hstable : (prefixWord ++ tailWord_873297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873297).length < 2 ^ (prefixWord ++ tailWord_873297).sum := by decide
  have hdescent : baseEnd_873297 < baseStart_873297 := by decide
  rcases family_descends (prefixWord ++ tailWord_873297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873342 : List Nat := [4, 2, 3, 1, 2, 1, 1, 6]
def baseStart_873342 : Nat := 118140960795 + 873342 * 2 ^ 59
def prefixEnd_873342 : Nat := 4983230072969 + 3 ^ 40 * 873342 * 2
def baseEnd_873342 : Nat := 132872362002674749365505

theorem tailTrace_873342 : CollatzResearch.WordTrace tailWord_873342 prefixEnd_873342 132872362002674749365505 := by
  unfold tailWord_873342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981674950254820472984785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21235599734692375855918853 3981674950254820472984785)
  ·
    refine ⟨2986256212691115354738589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3981674950254820472984785 2986256212691115354738589)
    ·
      refine ⟨1119846079759168258026971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2986256212691115354738589 1119846079759168258026971)
      ·
        refine ⟨1679769119638752387040457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119846079759168258026971 1679769119638752387040457)
        ·
          refine ⟨1259826839729064290280343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1679769119638752387040457 1259826839729064290280343)
          ·
            refine ⟨1889740259593596435420515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259826839729064290280343 1889740259593596435420515)
            ·
              refine ⟨2834610389390394653130773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889740259593596435420515 2834610389390394653130773)
              ·
                refine ⟨132872362002674749365505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2834610389390394653130773 132872362002674749365505)
                ·
                  rfl

theorem cell20_873342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_873342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873342 prefixEnd_873342 := by exact prefixLift 873342
  have htrace : WordTrace (prefixWord ++ tailWord_873342) baseStart_873342 baseEnd_873342 := by
    simpa [prefixWord, tailWord_873342, baseEnd_873342] using wordTrace_append hprefix tailTrace_873342
  have hstable : (prefixWord ++ tailWord_873342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873342).length < 2 ^ (prefixWord ++ tailWord_873342).sum := by decide
  have hdescent : baseEnd_873342 < baseStart_873342 := by decide
  rcases family_descends (prefixWord ++ tailWord_873342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873353 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_873353 : Nat := 118140960795 + 873353 * 2 ^ 59
def prefixEnd_873353 : Nat := 4983230072969 + 3 ^ 40 * 873353 * 2
def baseEnd_873353 : Nat := 398622106707757098729803

theorem tailTrace_873353 : CollatzResearch.WordTrace tailWord_873353 prefixEnd_873353 398622106707757098729803 := by
  unfold tailWord_873353
  simp only [CollatzResearch.WordTrace]
  refine ⟨31853800804998712662528713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21235867203332475108352475 31853800804998712662528713)
  ·
    refine ⟨23890350603749034496896535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31853800804998712662528713 23890350603749034496896535)
    ·
      refine ⟨35835525905623551745344803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23890350603749034496896535 35835525905623551745344803)
      ·
        refine ⟨53753288858435327618017205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35835525905623551745344803 53753288858435327618017205)
        ·
          refine ⟨5039370830478311964189113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53753288858435327618017205 5039370830478311964189113)
          ·
            refine ⟨3779528122858733973141835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5039370830478311964189113 3779528122858733973141835)
            ·
              refine ⟨5669292184288100959712753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779528122858733973141835 5669292184288100959712753)
              ·
                refine ⟨4251969138216075719784565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5669292184288100959712753 4251969138216075719784565)
                ·
                  refine ⟨398622106707757098729803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4251969138216075719784565 398622106707757098729803)
                  ·
                    rfl

theorem cell20_873353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_873353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873353 prefixEnd_873353 := by exact prefixLift 873353
  have htrace : WordTrace (prefixWord ++ tailWord_873353) baseStart_873353 baseEnd_873353 := by
    simpa [prefixWord, tailWord_873353, baseEnd_873353] using wordTrace_append hprefix tailTrace_873353
  have hstable : (prefixWord ++ tailWord_873353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873353).length < 2 ^ (prefixWord ++ tailWord_873353).sum := by decide
  have hdescent : baseEnd_873353 < baseStart_873353 := by decide
  rcases family_descends (prefixWord ++ tailWord_873353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873356 : List Nat := [2, 2, 1, 2, 1, 2, 5, 3, 2]
def baseStart_873356 : Nat := 118140960795 + 873356 * 2 ^ 59
def prefixEnd_873356 : Nat := 4983230072969 + 3 ^ 40 * 873356 * 2
def baseEnd_873356 : Nat := 398623475989502421629791

theorem tailTrace_873356 : CollatzResearch.WordTrace tailWord_873356 prefixEnd_873356 398623475989502421629791 := by
  unfold tailWord_873356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15926955111993922087443961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21235940149325229449925281 15926955111993922087443961)
  ·
    refine ⟨11945216333995441565582971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15926955111993922087443961 11945216333995441565582971)
    ·
      refine ⟨17917824500993162348374457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11945216333995441565582971 17917824500993162348374457)
      ·
        refine ⟨13438368375744871761280843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17917824500993162348374457 13438368375744871761280843)
        ·
          refine ⟨20157552563617307641921265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13438368375744871761280843 20157552563617307641921265)
          ·
            refine ⟨15118164422712980731440949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20157552563617307641921265 15118164422712980731440949)
            ·
              refine ⟨1417327914629341943572589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15118164422712980731440949 1417327914629341943572589)
              ·
                refine ⟨531497967986003228839721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417327914629341943572589 531497967986003228839721)
                ·
                  refine ⟨398623475989502421629791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531497967986003228839721 398623475989502421629791)
                  ·
                    rfl

theorem cell20_873356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_873356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873356 prefixEnd_873356 := by exact prefixLift 873356
  have htrace : WordTrace (prefixWord ++ tailWord_873356) baseStart_873356 baseEnd_873356 := by
    simpa [prefixWord, tailWord_873356, baseEnd_873356] using wordTrace_append hprefix tailTrace_873356
  have hstable : (prefixWord ++ tailWord_873356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873356).length < 2 ^ (prefixWord ++ tailWord_873356).sum := by decide
  have hdescent : baseEnd_873356 < baseStart_873356 := by decide
  rcases family_descends (prefixWord ++ tailWord_873356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873366 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_873366 : Nat := 118140960795 + 873366 * 2 ^ 59
def prefixEnd_873366 : Nat := 4983230072969 + 3 ^ 40 * 873366 * 2
def baseEnd_873366 : Nat := 398628040261986831296417

theorem tailTrace_873366 : CollatzResearch.WordTrace tailWord_873366 prefixEnd_873366 398628040261986831296417 := by
  unfold tailWord_873366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990892184621975992671997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21236183302634410588501301 1990892184621975992671997)
  ·
    refine ⟨746584569233240997251999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1990892184621975992671997 746584569233240997251999)
    ·
      refine ⟨1119876853849861495877999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 746584569233240997251999 1119876853849861495877999)
      ·
        refine ⟨1679815280774792243816999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119876853849861495877999 1679815280774792243816999)
        ·
          refine ⟨2519722921162188365725499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679815280774792243816999 2519722921162188365725499)
          ·
            refine ⟨3779584381743282548588249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519722921162188365725499 3779584381743282548588249)
            ·
              refine ⟨2834688286307461911441187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3779584381743282548588249 2834688286307461911441187)
              ·
                refine ⟨4252032429461192867161781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834688286307461911441187 4252032429461192867161781)
                ·
                  refine ⟨398628040261986831296417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4252032429461192867161781 398628040261986831296417)
                  ·
                    rfl

theorem cell20_873366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_873366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873366 prefixEnd_873366 := by exact prefixLift 873366
  have htrace : WordTrace (prefixWord ++ tailWord_873366) baseStart_873366 baseEnd_873366 := by
    simpa [prefixWord, tailWord_873366, baseEnd_873366] using wordTrace_append hprefix tailTrace_873366
  have hstable : (prefixWord ++ tailWord_873366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873366).length < 2 ^ (prefixWord ++ tailWord_873366).sum := by decide
  have hdescent : baseEnd_873366 < baseStart_873366 := by decide
  rcases family_descends (prefixWord ++ tailWord_873366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873373 : List Nat := [1, 4, 2, 1, 2, 1, 5, 2, 2]
def baseStart_873373 : Nat := 118140960795 + 873373 * 2 ^ 59
def prefixEnd_873373 : Nat := 4983230072969 + 3 ^ 40 * 873373 * 2
def baseEnd_873373 : Nat := 398631235252725918063055

theorem tailTrace_873373 : CollatzResearch.WordTrace tailWord_873373 prefixEnd_873373 398631235252725918063055 := by
  unfold tailWord_873373
  simp only [CollatzResearch.WordTrace]
  refine ⟨31854530264926256078256773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21236353509950837385504515 31854530264926256078256773)
  ·
    refine ⟨5972724424673673014673145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31854530264926256078256773 5972724424673673014673145)
    ·
      refine ⟨4479543318505254761004859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5972724424673673014673145 4479543318505254761004859)
      ·
        refine ⟨6719314977757882141507289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4479543318505254761004859 6719314977757882141507289)
        ·
          refine ⟨5039486233318411606130467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6719314977757882141507289 5039486233318411606130467)
          ·
            refine ⟨7559229349977617409195701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039486233318411606130467 7559229349977617409195701)
            ·
              refine ⟨708677751560401632112097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7559229349977617409195701 708677751560401632112097)
              ·
                refine ⟨531508313670301224084073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708677751560401632112097 531508313670301224084073)
                ·
                  refine ⟨398631235252725918063055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531508313670301224084073 398631235252725918063055)
                  ·
                    rfl

theorem cell20_873373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_873373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873373 prefixEnd_873373 := by exact prefixLift 873373
  have htrace : WordTrace (prefixWord ++ tailWord_873373) baseStart_873373 baseEnd_873373 := by
    simpa [prefixWord, tailWord_873373, baseEnd_873373] using wordTrace_append hprefix tailTrace_873373
  have hstable : (prefixWord ++ tailWord_873373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873373).length < 2 ^ (prefixWord ++ tailWord_873373).sum := by decide
  have hdescent : baseEnd_873373 < baseStart_873373 := by decide
  rcases family_descends (prefixWord ++ tailWord_873373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873383 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 3]
def baseStart_873383 : Nat := 118140960795 + 873383 * 2 ^ 59
def prefixEnd_873383 : Nat := 4983230072969 + 3 ^ 40 * 873383 * 2
def baseEnd_873383 : Nat := 398635799525210327729681

theorem tailTrace_873383 : CollatzResearch.WordTrace tailWord_873383 prefixEnd_873383 398635799525210327729681 := by
  unfold tailWord_873383
  simp only [CollatzResearch.WordTrace]
  refine ⟨31854894994890027786120803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21236596663260018524080535 31854894994890027786120803)
  ·
    refine ⟨47782342492335041679181205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31854894994890027786120803 47782342492335041679181205)
    ·
      refine ⟨2239797304328205078711619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47782342492335041679181205 2239797304328205078711619)
      ·
        refine ⟨3359695956492307618067429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239797304328205078711619 3359695956492307618067429)
        ·
          refine ⟨629942991842307678387643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3359695956492307618067429 629942991842307678387643)
          ·
            refine ⟨944914487763461517581465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629942991842307678387643 944914487763461517581465)
            ·
              refine ⟨708685865822596138186099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944914487763461517581465 708685865822596138186099)
              ·
                refine ⟨1063028798733894207279149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708685865822596138186099 1063028798733894207279149)
                ·
                  refine ⟨398635799525210327729681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063028798733894207279149 398635799525210327729681)
                  ·
                    rfl

theorem cell20_873383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 3].length) (baseStart_873383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873383 prefixEnd_873383 := by exact prefixLift 873383
  have htrace : WordTrace (prefixWord ++ tailWord_873383) baseStart_873383 baseEnd_873383 := by
    simpa [prefixWord, tailWord_873383, baseEnd_873383] using wordTrace_append hprefix tailTrace_873383
  have hstable : (prefixWord ++ tailWord_873383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873383).length < 2 ^ (prefixWord ++ tailWord_873383).sum := by decide
  have hdescent : baseEnd_873383 < baseStart_873383 := by decide
  rcases family_descends (prefixWord ++ tailWord_873383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873414 : List Nat := [6, 1, 3, 1, 2, 7]
def baseStart_873414 : Nat := 118140960795 + 873414 * 2 ^ 59
def prefixEnd_873414 : Nat := 4983230072969 + 3 ^ 40 * 873414 * 2
def baseEnd_873414 : Nat := 14764812917404148062823

theorem tailTrace_873414 : CollatzResearch.WordTrace tailWord_873414 prefixEnd_873414 14764812917404148062823 := by
  unfold tailWord_873414
  simp only [CollatzResearch.WordTrace]
  refine ⟨995500801805553752515603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21237350438518480053666197 995500801805553752515603)
  ·
    refine ⟨1493251202708330628773405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995500801805553752515603 1493251202708330628773405)
    ·
      refine ⟨559969201015623985790027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1493251202708330628773405 559969201015623985790027)
      ·
        refine ⟨839953801523435978685041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559969201015623985790027 839953801523435978685041)
        ·
          refine ⟨629965351142576984013781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839953801523435978685041 629965351142576984013781)
          ·
            refine ⟨14764812917404148062823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 629965351142576984013781 14764812917404148062823)
            ·
              rfl

theorem cell20_873414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 7].length) (baseStart_873414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873414 prefixEnd_873414 := by exact prefixLift 873414
  have htrace : WordTrace (prefixWord ++ tailWord_873414) baseStart_873414 baseEnd_873414 := by
    simpa [prefixWord, tailWord_873414, baseEnd_873414] using wordTrace_append hprefix tailTrace_873414
  have hstable : (prefixWord ++ tailWord_873414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873414).length < 2 ^ (prefixWord ++ tailWord_873414).sum := by decide
  have hdescent : baseEnd_873414 < baseStart_873414 := by decide
  rcases family_descends (prefixWord ++ tailWord_873414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873428 : List Nat := [2, 4, 1, 2, 1, 4, 2, 2, 2]
def baseStart_873428 : Nat := 118140960795 + 873428 * 2 ^ 59
def prefixEnd_873428 : Nat := 4983230072969 + 3 ^ 40 * 873428 * 2
def baseEnd_873428 : Nat := 398656338751390171229497

theorem tailTrace_873428 : CollatzResearch.WordTrace tailWord_873428 prefixEnd_873428 398656338751390171229497 := by
  unfold tailWord_873428
  simp only [CollatzResearch.WordTrace]
  refine ⟨15928268139863500235754469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21237690853151333647672625 15928268139863500235754469)
  ·
    refine ⟨2986550276224406294203963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15928268139863500235754469 2986550276224406294203963)
    ·
      refine ⟨4479825414336609441305945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2986550276224406294203963 4479825414336609441305945)
      ·
        refine ⟨3359869060752457080979459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4479825414336609441305945 3359869060752457080979459)
        ·
          refine ⟨5039803591128685621469189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359869060752457080979459 5039803591128685621469189)
          ·
            refine ⟨944963173336628554025473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5039803591128685621469189 944963173336628554025473)
            ·
              refine ⟨708722380002471415519105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944963173336628554025473 708722380002471415519105)
              ·
                refine ⟨531541785001853561639329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708722380002471415519105 531541785001853561639329)
                ·
                  refine ⟨398656338751390171229497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531541785001853561639329 398656338751390171229497)
                  ·
                    rfl

theorem cell20_873428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_873428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873428 prefixEnd_873428 := by exact prefixLift 873428
  have htrace : WordTrace (prefixWord ++ tailWord_873428) baseStart_873428 baseEnd_873428 := by
    simpa [prefixWord, tailWord_873428, baseEnd_873428] using wordTrace_append hprefix tailTrace_873428
  have hstable : (prefixWord ++ tailWord_873428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873428).length < 2 ^ (prefixWord ++ tailWord_873428).sum := by decide
  have hdescent : baseEnd_873428 < baseStart_873428 := by decide
  rcases family_descends (prefixWord ++ tailWord_873428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873432 : List Nat := [2, 1, 2, 2, 2, 4, 1, 4, 2]
def baseStart_873432 : Nat := 118140960795 + 873432 * 2 ^ 59
def prefixEnd_873432 : Nat := 4983230072969 + 3 ^ 40 * 873432 * 2
def baseEnd_873432 : Nat := 398658164460383935096147

theorem tailTrace_873432 : CollatzResearch.WordTrace tailWord_873432 prefixEnd_873432 398658164460383935096147 := by
  unfold tailWord_873432
  simp only [CollatzResearch.WordTrace]
  refine ⟨15928341085856254577327275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21237788114475006103103033 15928341085856254577327275)
  ·
    refine ⟨23892511628784381865990913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15928341085856254577327275 23892511628784381865990913)
    ·
      refine ⟨17919383721588286399493185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23892511628784381865990913 17919383721588286399493185)
      ·
        refine ⟨13439537791191214799619889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17919383721588286399493185 13439537791191214799619889)
        ·
          refine ⟨10079653343393411099714917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13439537791191214799619889 10079653343393411099714917)
          ·
            refine ⟨1889935001886264581196547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10079653343393411099714917 1889935001886264581196547)
            ·
              refine ⟨2834902502829396871794821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889935001886264581196547 2834902502829396871794821)
              ·
                refine ⟨531544219280511913461529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2834902502829396871794821 531544219280511913461529)
                ·
                  refine ⟨398658164460383935096147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531544219280511913461529 398658164460383935096147)
                  ·
                    rfl

theorem cell20_873432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_873432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873432 prefixEnd_873432 := by exact prefixLift 873432
  have htrace : WordTrace (prefixWord ++ tailWord_873432) baseStart_873432 baseEnd_873432 := by
    simpa [prefixWord, tailWord_873432, baseEnd_873432] using wordTrace_append hprefix tailTrace_873432
  have hstable : (prefixWord ++ tailWord_873432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873432).length < 2 ^ (prefixWord ++ tailWord_873432).sum := by decide
  have hdescent : baseEnd_873432 < baseStart_873432 := by decide
  rcases family_descends (prefixWord ++ tailWord_873432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873439 : List Nat := [1, 1, 2, 3, 5, 2, 1, 5]
def baseStart_873439 : Nat := 118140960795 + 873439 * 2 ^ 59
def prefixEnd_873439 : Nat := 4983230072969 + 3 ^ 40 * 873439 * 2
def baseEnd_873439 : Nat := 132887119817041007287595

theorem tailTrace_873439 : CollatzResearch.WordTrace tailWord_873439 prefixEnd_873439 132887119817041007287595 := by
  unfold tailWord_873439
  simp only [CollatzResearch.WordTrace]
  refine ⟨31856937482687149350159371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21237958321791432900106247 31856937482687149350159371)
  ·
    refine ⟨47785406224030724025239057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31856937482687149350159371 47785406224030724025239057)
    ·
      refine ⟨35839054668023043018929293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47785406224030724025239057 35839054668023043018929293)
      ·
        refine ⟨13439645500508641132098485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35839054668023043018929293 13439645500508641132098485)
        ·
          refine ⟨1259966765672685106134233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13439645500508641132098485 1259966765672685106134233)
          ·
            refine ⟨944975074254513829600675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259966765672685106134233 944975074254513829600675)
            ·
              refine ⟨1417462611381770744401013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944975074254513829600675 1417462611381770744401013)
              ·
                refine ⟨132887119817041007287595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1417462611381770744401013 132887119817041007287595)
                ·
                  rfl

theorem cell20_873439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_873439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873439 prefixEnd_873439 := by exact prefixLift 873439
  have htrace : WordTrace (prefixWord ++ tailWord_873439) baseStart_873439 baseEnd_873439 := by
    simpa [prefixWord, tailWord_873439, baseEnd_873439] using wordTrace_append hprefix tailTrace_873439
  have hstable : (prefixWord ++ tailWord_873439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873439).length < 2 ^ (prefixWord ++ tailWord_873439).sum := by decide
  have hdescent : baseEnd_873439 < baseStart_873439 := by decide
  rcases family_descends (prefixWord ++ tailWord_873439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873484 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_873484 : Nat := 118140960795 + 873484 * 2 ^ 59
def prefixEnd_873484 : Nat := 4983230072969 + 3 ^ 40 * 873484 * 2
def baseEnd_873484 : Nat := 398681898677302865362601

theorem tailTrace_873484 : CollatzResearch.WordTrace tailWord_873484 prefixEnd_873484 398681898677302865362601 := by
  unfold tailWord_873484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929289383762061017773753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21239052511682748023698337 15929289383762061017773753)
  ·
    refine ⟨11946967037821545763330315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15929289383762061017773753 11946967037821545763330315)
    ·
      refine ⟨17920450556732318644995473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11946967037821545763330315 17920450556732318644995473)
      ·
        refine ⟨13440337917549238983746605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17920450556732318644995473 13440337917549238983746605)
        ·
          refine ⟨5040126719080964618904977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13440337917549238983746605 5040126719080964618904977)
          ·
            refine ⟨3780095039310723464178733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5040126719080964618904977 3780095039310723464178733)
            ·
              refine ⟨1417535639741521299067025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3780095039310723464178733 1417535639741521299067025)
              ·
                refine ⟨1063151729806140974300269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417535639741521299067025 1063151729806140974300269)
                ·
                  refine ⟨398681898677302865362601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063151729806140974300269 398681898677302865362601)
                  ·
                    rfl

theorem cell20_873484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_873484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873484 prefixEnd_873484 := by exact prefixLift 873484
  have htrace : WordTrace (prefixWord ++ tailWord_873484) baseStart_873484 baseEnd_873484 := by
    simpa [prefixWord, tailWord_873484, baseEnd_873484] using wordTrace_append hprefix tailTrace_873484
  have hstable : (prefixWord ++ tailWord_873484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873484).length < 2 ^ (prefixWord ++ tailWord_873484).sum := by decide
  have hdescent : baseEnd_873484 < baseStart_873484 := by decide
  rcases family_descends (prefixWord ++ tailWord_873484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873543 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_873543 : Nat := 118140960795 + 873543 * 2 ^ 59
def prefixEnd_873543 : Nat := 4983230072969 + 3 ^ 40 * 873543 * 2
def baseEnd_873543 : Nat := 398708827884960882395693

theorem tailTrace_873543 : CollatzResearch.WordTrace tailWord_873543 prefixEnd_873543 398708827884960882395693 := by
  unfold tailWord_873543
  simp only [CollatzResearch.WordTrace]
  refine ⟨31860730674310375111945283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21240487116206916741296855 31860730674310375111945283)
  ·
    refine ⟨47791096011465562667917925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31860730674310375111945283 47791096011465562667917925)
    ·
      refine ⟨8960830502149793000234611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47791096011465562667917925 8960830502149793000234611)
      ·
        refine ⟨13441245753224689500351917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8960830502149793000234611 13441245753224689500351917)
        ·
          refine ⟨5040467157459258562631969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13441245753224689500351917 5040467157459258562631969)
          ·
            refine ⟨3780350368094443921973977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5040467157459258562631969 3780350368094443921973977)
            ·
              refine ⟨2835262776070832941480483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3780350368094443921973977 2835262776070832941480483)
              ·
                refine ⟨4252894164106249412220725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835262776070832941480483 4252894164106249412220725)
                ·
                  refine ⟨398708827884960882395693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4252894164106249412220725 398708827884960882395693)
                  ·
                    rfl

theorem cell20_873543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_873543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873543 prefixEnd_873543 := by exact prefixLift 873543
  have htrace : WordTrace (prefixWord ++ tailWord_873543) baseStart_873543 baseEnd_873543 := by
    simpa [prefixWord, tailWord_873543, baseEnd_873543] using wordTrace_append hprefix tailTrace_873543
  have hstable : (prefixWord ++ tailWord_873543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873543).length < 2 ^ (prefixWord ++ tailWord_873543).sum := by decide
  have hdescent : baseEnd_873543 < baseStart_873543 := by decide
  rcases family_descends (prefixWord ++ tailWord_873543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873601 : List Nat := [1, 2, 4, 2, 2, 1, 4, 2, 2]
def baseStart_873601 : Nat := 118140960795 + 873601 * 2 ^ 59
def prefixEnd_873601 : Nat := 4983230072969 + 3 ^ 40 * 873601 * 2
def baseEnd_873601 : Nat := 398735300665370458462123

theorem tailTrace_873601 : CollatzResearch.WordTrace tailWord_873601 prefixEnd_873601 398735300665370458462123 := by
  unfold tailWord_873601
  simp only [CollatzResearch.WordTrace]
  refine ⟨31862846108100251017556657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21241897405400167345037771 31862846108100251017556657)
  ·
    refine ⟨23897134581075188263167493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31862846108100251017556657 23897134581075188263167493)
    ·
      refine ⟨4480712733951597799343905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23897134581075188263167493 4480712733951597799343905)
      ·
        refine ⟨3360534550463698349507929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4480712733951597799343905 3360534550463698349507929)
        ·
          refine ⟨2520400912847773762130947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360534550463698349507929 2520400912847773762130947)
          ·
            refine ⟨3780601369271660643196421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520400912847773762130947 3780601369271660643196421)
            ·
              refine ⟨708862756738436370599329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3780601369271660643196421 708862756738436370599329)
              ·
                refine ⟨531647067553827277949497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708862756738436370599329 531647067553827277949497)
                ·
                  refine ⟨398735300665370458462123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531647067553827277949497 398735300665370458462123)
                  ·
                    rfl

theorem cell20_873601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_873601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873601 prefixEnd_873601 := by exact prefixLift 873601
  have htrace : WordTrace (prefixWord ++ tailWord_873601) baseStart_873601 baseEnd_873601 := by
    simpa [prefixWord, tailWord_873601, baseEnd_873601] using wordTrace_append hprefix tailTrace_873601
  have hstable : (prefixWord ++ tailWord_873601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873601).length < 2 ^ (prefixWord ++ tailWord_873601).sum := by decide
  have hdescent : baseEnd_873601 < baseStart_873601 := by decide
  rcases family_descends (prefixWord ++ tailWord_873601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873608 : List Nat := [2, 1, 3, 4, 3, 1, 1, 5]
def baseStart_873608 : Nat := 118140960795 + 873608 * 2 ^ 59
def prefixEnd_873608 : Nat := 4983230072969 + 3 ^ 40 * 873608 * 2
def baseEnd_873608 : Nat := 132912831885369848409587

theorem tailTrace_873608 : CollatzResearch.WordTrace tailWord_873608 prefixEnd_873608 132912831885369848409587 := by
  unfold tailWord_873608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931550709537445606530739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21242067612716594142040985 15931550709537445606530739)
  ·
    refine ⟨23897326064306168409796109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15931550709537445606530739 23897326064306168409796109)
    ·
      refine ⟨8961497274114813153673541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23897326064306168409796109 8961497274114813153673541)
      ·
        refine ⟨1680280738896527466313789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8961497274114813153673541 1680280738896527466313789)
        ·
          refine ⟨630105277086197799867671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1680280738896527466313789 630105277086197799867671)
          ·
            refine ⟨945157915629296699801507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630105277086197799867671 945157915629296699801507)
            ·
              refine ⟨1417736873443945049702261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945157915629296699801507 1417736873443945049702261)
              ·
                refine ⟨132912831885369848409587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1417736873443945049702261 132912831885369848409587)
                ·
                  rfl

theorem cell20_873608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_873608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873608 prefixEnd_873608 := by exact prefixLift 873608
  have htrace : WordTrace (prefixWord ++ tailWord_873608) baseStart_873608 baseEnd_873608 := by
    simpa [prefixWord, tailWord_873608, baseEnd_873608] using wordTrace_append hprefix tailTrace_873608
  have hstable : (prefixWord ++ tailWord_873608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873608).length < 2 ^ (prefixWord ++ tailWord_873608).sum := by decide
  have hdescent : baseEnd_873608 < baseStart_873608 := by decide
  rcases family_descends (prefixWord ++ tailWord_873608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873619 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 3]
def baseStart_873619 : Nat := 118140960795 + 873619 * 2 ^ 59
def prefixEnd_873619 : Nat := 4983230072969 + 3 ^ 40 * 873619 * 2
def baseEnd_873619 : Nat := 398743516355842395862049

theorem tailTrace_873619 : CollatzResearch.WordTrace tailWord_873619 prefixEnd_873619 398743516355842395862049 := by
  unfold tailWord_873619
  simp only [CollatzResearch.WordTrace]
  refine ⟨31863502622035040091711911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21242335081356693394474607 31863502622035040091711911)
  ·
    refine ⟨47795253933052560137567867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31863502622035040091711911 47795253933052560137567867)
    ·
      refine ⟨71692880899578840206351801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47795253933052560137567867 71692880899578840206351801)
      ·
        refine ⟨53769660674684130154763851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71692880899578840206351801 53769660674684130154763851)
        ·
          refine ⟨80654491012026195232145777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53769660674684130154763851 80654491012026195232145777)
          ·
            refine ⟨60490868259019646424109333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80654491012026195232145777 60490868259019646424109333)
            ·
              refine ⟨2835509449641545926130125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60490868259019646424109333 2835509449641545926130125)
              ·
                refine ⟨1063316043615579722298797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2835509449641545926130125 1063316043615579722298797)
                ·
                  refine ⟨398743516355842395862049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063316043615579722298797 398743516355842395862049)
                  ·
                    rfl

theorem cell20_873619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_873619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873619 prefixEnd_873619 := by exact prefixLift 873619
  have htrace : WordTrace (prefixWord ++ tailWord_873619) baseStart_873619 baseEnd_873619 := by
    simpa [prefixWord, tailWord_873619, baseEnd_873619] using wordTrace_append hprefix tailTrace_873619
  have hstable : (prefixWord ++ tailWord_873619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873619).length < 2 ^ (prefixWord ++ tailWord_873619).sum := by decide
  have hdescent : baseEnd_873619 < baseStart_873619 := by decide
  rcases family_descends (prefixWord ++ tailWord_873619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873639 : List Nat := [1, 1, 6, 2, 1, 2, 2, 3, 2]
def baseStart_873639 : Nat := 118140960795 + 873639 * 2 ^ 59
def prefixEnd_873639 : Nat := 4983230072969 + 3 ^ 40 * 873639 * 2
def baseEnd_873639 : Nat := 398752644900811215195301

theorem tailTrace_873639 : CollatzResearch.WordTrace tailWord_873639 prefixEnd_873639 398752644900811215195301 := by
  unfold tailWord_873639
  simp only [CollatzResearch.WordTrace]
  refine ⟨31864232081962583507439971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21242821387975055671626647 31864232081962583507439971)
  ·
    refine ⟨47796348122943875261159957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31864232081962583507439971 47796348122943875261159957)
    ·
      refine ⟨2240453818262994152866873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47796348122943875261159957 2240453818262994152866873)
      ·
        refine ⟨1680340363697245614650155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2240453818262994152866873 1680340363697245614650155)
        ·
          refine ⟨2520510545545868421975233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680340363697245614650155 2520510545545868421975233)
          ·
            refine ⟨1890382909159401316481425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2520510545545868421975233 1890382909159401316481425)
            ·
              refine ⟨1417787181869550987361069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1890382909159401316481425 1417787181869550987361069)
              ·
                refine ⟨531670193201081620260401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1417787181869550987361069 531670193201081620260401)
                ·
                  refine ⟨398752644900811215195301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531670193201081620260401 398752644900811215195301)
                  ·
                    rfl

theorem cell20_873639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 2].length) (baseStart_873639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873639 prefixEnd_873639 := by exact prefixLift 873639
  have htrace : WordTrace (prefixWord ++ tailWord_873639) baseStart_873639 baseEnd_873639 := by
    simpa [prefixWord, tailWord_873639, baseEnd_873639] using wordTrace_append hprefix tailTrace_873639
  have hstable : (prefixWord ++ tailWord_873639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873639).length < 2 ^ (prefixWord ++ tailWord_873639).sum := by decide
  have hdescent : baseEnd_873639 < baseStart_873639 := by decide
  rcases family_descends (prefixWord ++ tailWord_873639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873657 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_873657 : Nat := 118140960795 + 873657 * 2 ^ 59
def prefixEnd_873657 : Nat := 4983230072969 + 3 ^ 40 * 873657 * 2
def baseEnd_873657 : Nat := 398760860591283152595227

theorem tailTrace_873657 : CollatzResearch.WordTrace tailWord_873657 prefixEnd_873657 398760860591283152595227 := by
  unfold tailWord_873657
  simp only [CollatzResearch.WordTrace]
  refine ⟨31864888595897372581595225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21243259063931581721063483 31864888595897372581595225)
  ·
    refine ⟨23898666446923029436196419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31864888595897372581595225 23898666446923029436196419)
    ·
      refine ⟨35847999670384544154294629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23898666446923029436196419 35847999670384544154294629)
      ·
        refine ⟨6721499938197102028930243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35847999670384544154294629 6721499938197102028930243)
        ·
          refine ⟨10082249907295653043395365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721499938197102028930243 10082249907295653043395365)
          ·
            refine ⟨1890421857617934945636631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10082249907295653043395365 1890421857617934945636631)
            ·
              refine ⟨2835632786426902418454947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890421857617934945636631 2835632786426902418454947)
              ·
                refine ⟨4253449179640353627682421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835632786426902418454947 4253449179640353627682421)
                ·
                  refine ⟨398760860591283152595227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4253449179640353627682421 398760860591283152595227)
                  ·
                    rfl

theorem cell20_873657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_873657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873657 prefixEnd_873657 := by exact prefixLift 873657
  have htrace : WordTrace (prefixWord ++ tailWord_873657) baseStart_873657 baseEnd_873657 := by
    simpa [prefixWord, tailWord_873657, baseEnd_873657] using wordTrace_append hprefix tailTrace_873657
  have hstable : (prefixWord ++ tailWord_873657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873657).length < 2 ^ (prefixWord ++ tailWord_873657).sum := by decide
  have hdescent : baseEnd_873657 < baseStart_873657 := by decide
  rcases family_descends (prefixWord ++ tailWord_873657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873660 : List Nat := [2, 2, 2, 3, 2, 1, 2, 4, 2]
def baseStart_873660 : Nat := 118140960795 + 873660 * 2 ^ 59
def prefixEnd_873660 : Nat := 4983230072969 + 3 ^ 40 * 873660 * 2
def baseEnd_873660 : Nat := 398762229873028475495215

theorem tailTrace_873660 : CollatzResearch.WordTrace tailWord_873660 prefixEnd_873660 398762229873028475495215 := by
  unfold tailWord_873660
  simp only [CollatzResearch.WordTrace]
  refine ⟨15932499007443252046977217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21243332009924336062636289 15932499007443252046977217)
  ·
    refine ⟨11949374255582439035232913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15932499007443252046977217 11949374255582439035232913)
    ·
      refine ⟨8962030691686829276424685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11949374255582439035232913 8962030691686829276424685)
      ·
        refine ⟨3360761509382560978659257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8962030691686829276424685 3360761509382560978659257)
        ·
          refine ⟨2520571132036920733994443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360761509382560978659257 2520571132036920733994443)
          ·
            refine ⟨3780856698055381100991665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520571132036920733994443 3780856698055381100991665)
            ·
              refine ⟨2835642523541535825743749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3780856698055381100991665 2835642523541535825743749)
              ·
                refine ⟨531682973164037967326953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2835642523541535825743749 531682973164037967326953)
                ·
                  refine ⟨398762229873028475495215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531682973164037967326953 398762229873028475495215)
                  ·
                    rfl

theorem cell20_873660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_873660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873660 prefixEnd_873660 := by exact prefixLift 873660
  have htrace : WordTrace (prefixWord ++ tailWord_873660) baseStart_873660 baseEnd_873660 := by
    simpa [prefixWord, tailWord_873660, baseEnd_873660] using wordTrace_append hprefix tailTrace_873660
  have hstable : (prefixWord ++ tailWord_873660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873660).length < 2 ^ (prefixWord ++ tailWord_873660).sum := by decide
  have hdescent : baseEnd_873660 < baseStart_873660 := by decide
  rcases family_descends (prefixWord ++ tailWord_873660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873688 : List Nat := [2, 1, 2, 2, 5, 1, 1, 6]
def baseStart_873688 : Nat := 118140960795 + 873688 * 2 ^ 59
def prefixEnd_873688 : Nat := 4983230072969 + 3 ^ 40 * 873688 * 2
def baseEnd_873688 : Nat := 132925003278661607520589

theorem tailTrace_873688 : CollatzResearch.WordTrace tailWord_873688 prefixEnd_873688 132925003278661607520589 := by
  unfold tailWord_873688
  simp only [CollatzResearch.WordTrace]
  refine ⟨15933009629392532437986859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21244012839190043250649145 15933009629392532437986859)
  ·
    refine ⟨23899514444088798656980289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15933009629392532437986859 23899514444088798656980289)
    ·
      refine ⟨17924635833066598992735217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23899514444088798656980289 17924635833066598992735217)
      ·
        refine ⟨13443476874799949244551413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17924635833066598992735217 13443476874799949244551413)
        ·
          refine ⟨1260325957012495241676695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13443476874799949244551413 1260325957012495241676695)
          ·
            refine ⟨1890488935518742862515043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260325957012495241676695 1890488935518742862515043)
            ·
              refine ⟨2835733403278114293772565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890488935518742862515043 2835733403278114293772565)
              ·
                refine ⟨132925003278661607520589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2835733403278114293772565 132925003278661607520589)
                ·
                  rfl

theorem cell20_873688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_873688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873688 prefixEnd_873688 := by exact prefixLift 873688
  have htrace : WordTrace (prefixWord ++ tailWord_873688) baseStart_873688 baseEnd_873688 := by
    simpa [prefixWord, tailWord_873688, baseEnd_873688] using wordTrace_append hprefix tailTrace_873688
  have hstable : (prefixWord ++ tailWord_873688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873688).length < 2 ^ (prefixWord ++ tailWord_873688).sum := by decide
  have hdescent : baseEnd_873688 < baseStart_873688 := by decide
  rcases family_descends (prefixWord ++ tailWord_873688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873726 : List Nat := [4, 2, 2, 1, 1, 2, 1, 7]
def baseStart_873726 : Nat := 118140960795 + 873726 * 2 ^ 59
def prefixEnd_873726 : Nat := 4983230072969 + 3 ^ 40 * 873726 * 2
def baseEnd_873726 : Nat := 132930784690475193098315

theorem tailTrace_873726 : CollatzResearch.WordTrace tailWord_873726 prefixEnd_873726 132930784690475193098315 := by
  unfold tailWord_873726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3983425654080924670732129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21244936821764931577238021 3983425654080924670732129)
  ·
    refine ⟨2987569240560693503049097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3983425654080924670732129 2987569240560693503049097)
    ·
      refine ⟨2240676930420520127286823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2987569240560693503049097 2240676930420520127286823)
      ·
        refine ⟨3361015395630780190930235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2240676930420520127286823 3361015395630780190930235)
        ·
          refine ⟨5041523093446170286395353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361015395630780190930235 5041523093446170286395353)
          ·
            refine ⟨3781142320084627714796515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5041523093446170286395353 3781142320084627714796515)
            ·
              refine ⟨5671713480126941572194773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781142320084627714796515 5671713480126941572194773)
              ·
                refine ⟨132930784690475193098315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5671713480126941572194773 132930784690475193098315)
                ·
                  rfl

theorem cell20_873726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_873726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873726 prefixEnd_873726 := by exact prefixLift 873726
  have htrace : WordTrace (prefixWord ++ tailWord_873726) baseStart_873726 baseEnd_873726 := by
    simpa [prefixWord, tailWord_873726, baseEnd_873726] using wordTrace_append hprefix tailTrace_873726
  have hstable : (prefixWord ++ tailWord_873726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873726).length < 2 ^ (prefixWord ++ tailWord_873726).sum := by decide
  have hdescent : baseEnd_873726 < baseStart_873726 := by decide
  rcases family_descends (prefixWord ++ tailWord_873726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873729 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 3]
def baseStart_873729 : Nat := 118140960795 + 873729 * 2 ^ 59
def prefixEnd_873729 : Nat := 4983230072969 + 3 ^ 40 * 873729 * 2
def baseEnd_873729 : Nat := 398793723353170902194933

theorem tailTrace_873729 : CollatzResearch.WordTrace tailWord_873729 prefixEnd_873729 398793723353170902194933 := by
  unfold tailWord_873729
  simp only [CollatzResearch.WordTrace]
  refine ⟨31867514651636528878216241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21245009767757685918810827 31867514651636528878216241)
  ·
    refine ⟨23900635988727396658662181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31867514651636528878216241 23900635988727396658662181)
    ·
      refine ⟨4481369247886386873499159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23900635988727396658662181 4481369247886386873499159)
      ·
        refine ⟨6722053871829580310248739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481369247886386873499159 6722053871829580310248739)
        ·
          refine ⟨10083080807744370465373109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722053871829580310248739 10083080807744370465373109)
          ·
            refine ⟨945288825726034731128729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10083080807744370465373109 945288825726034731128729)
            ·
              refine ⟨708966619294526048346547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945288825726034731128729 708966619294526048346547)
              ·
                refine ⟨1063449928941789072519821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708966619294526048346547 1063449928941789072519821)
                ·
                  refine ⟨398793723353170902194933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063449928941789072519821 398793723353170902194933)
                  ·
                    rfl

theorem cell20_873729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_873729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873729 prefixEnd_873729 := by exact prefixLift 873729
  have htrace : WordTrace (prefixWord ++ tailWord_873729) baseStart_873729 baseEnd_873729 := by
    simpa [prefixWord, tailWord_873729, baseEnd_873729] using wordTrace_append hprefix tailTrace_873729
  have hstable : (prefixWord ++ tailWord_873729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873729).length < 2 ^ (prefixWord ++ tailWord_873729).sum := by decide
  have hdescent : baseEnd_873729 < baseStart_873729 := by decide
  rcases family_descends (prefixWord ++ tailWord_873729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873733 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 3]
def baseStart_873733 : Nat := 118140960795 + 873733 * 2 ^ 59
def prefixEnd_873733 : Nat := 4983230072969 + 3 ^ 40 * 873733 * 2
def baseEnd_873733 : Nat := 398795549062164666061583

theorem tailTrace_873733 : CollatzResearch.WordTrace tailWord_873733 prefixEnd_873733 398795549062164666061583 := by
  unfold tailWord_873733
  simp only [CollatzResearch.WordTrace]
  refine ⟨31867660543622037561361853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21245107029081358374241235 31867660543622037561361853)
  ·
    refine ⟨11950372703858264085510695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31867660543622037561361853 11950372703858264085510695)
    ·
      refine ⟨17925559055787396128266043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11950372703858264085510695 17925559055787396128266043)
      ·
        refine ⟨26888338583681094192399065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17925559055787396128266043 26888338583681094192399065)
        ·
          refine ⟨20166253937760820644299299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26888338583681094192399065 20166253937760820644299299)
          ·
            refine ⟨30249380906641230966448949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20166253937760820644299299 30249380906641230966448949)
            ·
              refine ⟨2835879459997615403104589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30249380906641230966448949 2835879459997615403104589)
              ·
                refine ⟨1063454797499105776164221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2835879459997615403104589 1063454797499105776164221)
                ·
                  refine ⟨398795549062164666061583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063454797499105776164221 398795549062164666061583)
                  ·
                    rfl

theorem cell20_873733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_873733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873733 prefixEnd_873733 := by exact prefixLift 873733
  have htrace : WordTrace (prefixWord ++ tailWord_873733) baseStart_873733 baseEnd_873733 := by
    simpa [prefixWord, tailWord_873733, baseEnd_873733] using wordTrace_append hprefix tailTrace_873733
  have hstable : (prefixWord ++ tailWord_873733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873733).length < 2 ^ (prefixWord ++ tailWord_873733).sum := by decide
  have hdescent : baseEnd_873733 < baseStart_873733 := by decide
  rcases family_descends (prefixWord ++ tailWord_873733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873770 : List Nat := [3, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_873770 : Nat := 118140960795 + 873770 * 2 ^ 59
def prefixEnd_873770 : Nat := 4983230072969 + 3 ^ 40 * 873770 * 2
def baseEnd_873770 : Nat := 398812436870356981828099

theorem tailTrace_873770 : CollatzResearch.WordTrace tailWord_873770 prefixEnd_873770 398812436870356981828099 := by
  unfold tailWord_873770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967252511121998220114691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21246006696325328586972509 7967252511121998220114691)
  ·
    refine ⟨11950878766682997330172037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7967252511121998220114691 11950878766682997330172037)
    ·
      refine ⟨2240789768753061999407257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11950878766682997330172037 2240789768753061999407257)
      ·
        refine ⟨1680592326564796499555443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2240789768753061999407257 1680592326564796499555443)
        ·
          refine ⟨2520888489847194749333165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680592326564796499555443 2520888489847194749333165)
          ·
            refine ⟨945333183692698030999937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2520888489847194749333165 945333183692698030999937)
            ·
              refine ⟨708999887769523523249953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945333183692698030999937 708999887769523523249953)
              ·
                refine ⟨531749915827142642437465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708999887769523523249953 531749915827142642437465)
                ·
                  refine ⟨398812436870356981828099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531749915827142642437465 398812436870356981828099)
                  ·
                    rfl

theorem cell20_873770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_873770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873770 prefixEnd_873770 := by exact prefixLift 873770
  have htrace : WordTrace (prefixWord ++ tailWord_873770) baseStart_873770 baseEnd_873770 := by
    simpa [prefixWord, tailWord_873770, baseEnd_873770] using wordTrace_append hprefix tailTrace_873770
  have hstable : (prefixWord ++ tailWord_873770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873770).length < 2 ^ (prefixWord ++ tailWord_873770).sum := by decide
  have hdescent : baseEnd_873770 < baseStart_873770 := by decide
  rcases family_descends (prefixWord ++ tailWord_873770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873812 : List Nat := [2, 4, 1, 1, 2, 1, 4, 3, 2]
def baseStart_873812 : Nat := 118140960795 + 873812 * 2 ^ 59
def prefixEnd_873812 : Nat := 4983230072969 + 3 ^ 40 * 873812 * 2
def baseEnd_873812 : Nat := 398831606814791502427927

theorem tailTrace_873812 : CollatzResearch.WordTrace tailWord_873812 prefixEnd_873812 398831606814791502427927 := by
  unfold tailWord_873812
  simp only [CollatzResearch.WordTrace]
  refine ⟨15935270955167917026743845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21247027940223889368991793 15935270955167917026743845)
  ·
    refine ⟨2987863304093984442514471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15935270955167917026743845 2987863304093984442514471)
    ·
      refine ⟨4481794956140976663771707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987863304093984442514471 4481794956140976663771707)
      ·
        refine ⟨6722692434211464995657561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481794956140976663771707 6722692434211464995657561)
        ·
          refine ⟨5042019325658598746743171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6722692434211464995657561 5042019325658598746743171)
          ·
            refine ⟨7563028988487898120114757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042019325658598746743171 7563028988487898120114757)
            ·
              refine ⟨1418067935341480897521517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7563028988487898120114757 1418067935341480897521517)
              ·
                refine ⟨531775475753055336570569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1418067935341480897521517 531775475753055336570569)
                ·
                  refine ⟨398831606814791502427927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531775475753055336570569 398831606814791502427927)
                  ·
                    rfl

theorem cell20_873812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_873812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873812 prefixEnd_873812 := by exact prefixLift 873812
  have htrace : WordTrace (prefixWord ++ tailWord_873812) baseStart_873812 baseEnd_873812 := by
    simpa [prefixWord, tailWord_873812, baseEnd_873812] using wordTrace_append hprefix tailTrace_873812
  have hstable : (prefixWord ++ tailWord_873812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873812).length < 2 ^ (prefixWord ++ tailWord_873812).sum := by decide
  have hdescent : baseEnd_873812 < baseStart_873812 := by decide
  rcases family_descends (prefixWord ++ tailWord_873812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873868 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_873868 : Nat := 118140960795 + 873868 * 2 ^ 59
def prefixEnd_873868 : Nat := 4983230072969 + 3 ^ 40 * 873868 * 2
def baseEnd_873868 : Nat := 398857166740704196561031

theorem tailTrace_873868 : CollatzResearch.WordTrace tailWord_873868 prefixEnd_873868 398857166740704196561031 := by
  unfold tailWord_873868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936292199066477808763129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21248389598755303745017505 15936292199066477808763129)
  ·
    refine ⟨11952219149299858356572347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15936292199066477808763129 11952219149299858356572347)
    ·
      refine ⟨17928328723949787534858521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11952219149299858356572347 17928328723949787534858521)
      ·
        refine ⟨13446246542962340651143891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17928328723949787534858521 13446246542962340651143891)
        ·
          refine ⟨20169369814443510976715837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13446246542962340651143891 20169369814443510976715837)
          ·
            refine ⟨7563513680416316616268439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20169369814443510976715837 7563513680416316616268439)
            ·
              refine ⟨11345270520624474924402659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7563513680416316616268439 11345270520624474924402659)
              ·
                refine ⟨17017905780936712386603989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11345270520624474924402659 17017905780936712386603989)
                ·
                  refine ⟨398857166740704196561031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17017905780936712386603989 398857166740704196561031)
                  ·
                    rfl

theorem cell20_873868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_873868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873868 prefixEnd_873868 := by exact prefixLift 873868
  have htrace : WordTrace (prefixWord ++ tailWord_873868) baseStart_873868 baseEnd_873868 := by
    simpa [prefixWord, tailWord_873868, baseEnd_873868] using wordTrace_append hprefix tailTrace_873868
  have hstable : (prefixWord ++ tailWord_873868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873868).length < 2 ^ (prefixWord ++ tailWord_873868).sum := by decide
  have hdescent : baseEnd_873868 < baseStart_873868 := by decide
  rcases family_descends (prefixWord ++ tailWord_873868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873874 : List Nat := [3, 2, 3, 3, 2, 1, 6]
def baseStart_873874 : Nat := 118140960795 + 873874 * 2 ^ 59
def prefixEnd_873874 : Nat := 4983230072969 + 3 ^ 40 * 873874 * 2
def baseEnd_873874 : Nat := 44317767256021649151223

theorem tailTrace_873874 : CollatzResearch.WordTrace tailWord_873874 prefixEnd_873874 44317767256021649151223 := by
  unfold tailWord_873874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7968200809027804660561169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21248535490740812428163117 7968200809027804660561169)
  ·
    refine ⟨5976150606770853495420877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7968200809027804660561169 5976150606770853495420877)
    ·
      refine ⟨2241056477539070060782829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5976150606770853495420877 2241056477539070060782829)
      ·
        refine ⟨840396179077151272793561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2241056477539070060782829 840396179077151272793561)
        ·
          refine ⟨630297134307863454595171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 840396179077151272793561 630297134307863454595171)
          ·
            refine ⟨945445701461795181892757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630297134307863454595171 945445701461795181892757)
            ·
              refine ⟨44317767256021649151223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 945445701461795181892757 44317767256021649151223)
              ·
                rfl

theorem cell20_873874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 6].length) (baseStart_873874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873874 prefixEnd_873874 := by exact prefixLift 873874
  have htrace : WordTrace (prefixWord ++ tailWord_873874) baseStart_873874 baseEnd_873874 := by
    simpa [prefixWord, tailWord_873874, baseEnd_873874] using wordTrace_append hprefix tailTrace_873874
  have hstable : (prefixWord ++ tailWord_873874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873874).length < 2 ^ (prefixWord ++ tailWord_873874).sum := by decide
  have hdescent : baseEnd_873874 < baseStart_873874 := by decide
  rcases family_descends (prefixWord ++ tailWord_873874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873884 : List Nat := [2, 2, 3, 4, 1, 1, 3, 2, 2]
def baseStart_873884 : Nat := 118140960795 + 873884 * 2 ^ 59
def prefixEnd_873884 : Nat := 4983230072969 + 3 ^ 40 * 873884 * 2
def baseEnd_873884 : Nat := 398864469576679252027633

theorem tailTrace_873884 : CollatzResearch.WordTrace tailWord_873884 prefixEnd_873884 398864469576679252027633 := by
  unfold tailWord_873884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936583983037495175054353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21248778644049993566739137 15936583983037495175054353)
  ·
    refine ⟨11952437987278121381290765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15936583983037495175054353 11952437987278121381290765)
    ·
      refine ⟨4482164245229295517984037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11952437987278121381290765 4482164245229295517984037)
      ·
        refine ⟨840405795980492909622007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4482164245229295517984037 840405795980492909622007)
        ·
          refine ⟨1260608693970739364433011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840405795980492909622007 1260608693970739364433011)
          ·
            refine ⟨1890913040956109046649517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260608693970739364433011 1890913040956109046649517)
            ·
              refine ⟨709092390358540892493569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1890913040956109046649517 709092390358540892493569)
              ·
                refine ⟨531819292768905669370177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709092390358540892493569 531819292768905669370177)
                ·
                  refine ⟨398864469576679252027633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531819292768905669370177 398864469576679252027633)
                  ·
                    rfl

theorem cell20_873884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_873884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873884 prefixEnd_873884 := by exact prefixLift 873884
  have htrace : WordTrace (prefixWord ++ tailWord_873884) baseStart_873884 baseEnd_873884 := by
    simpa [prefixWord, tailWord_873884, baseEnd_873884] using wordTrace_append hprefix tailTrace_873884
  have hstable : (prefixWord ++ tailWord_873884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873884).length < 2 ^ (prefixWord ++ tailWord_873884).sum := by decide
  have hdescent : baseEnd_873884 < baseStart_873884 := by decide
  rcases family_descends (prefixWord ++ tailWord_873884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873885 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_873885 : Nat := 118140960795 + 873885 * 2 ^ 59
def prefixEnd_873885 : Nat := 4983230072969 + 3 ^ 40 * 873885 * 2
def baseEnd_873885 : Nat := 398864926003927692994295

theorem tailTrace_873885 : CollatzResearch.WordTrace tailWord_873885 prefixEnd_873885 398864926003927692994295 := by
  unfold tailWord_873885
  simp only [CollatzResearch.WordTrace]
  refine ⟨31873204439071367520895109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21248802959380911680596739 31873204439071367520895109)
  ·
    refine ⟨5976225832325881410167833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31873204439071367520895109 5976225832325881410167833)
    ·
      refine ⟨4482169374244411057625875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5976225832325881410167833 4482169374244411057625875)
      ·
        refine ⟨6723254061366616586438813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482169374244411057625875 6723254061366616586438813)
        ·
          refine ⟨2521220273012481219914555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6723254061366616586438813 2521220273012481219914555)
          ·
            refine ⟨3781830409518721829871833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521220273012481219914555 3781830409518721829871833)
            ·
              refine ⟨2836372807139041372403875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3781830409518721829871833 2836372807139041372403875)
              ·
                refine ⟨4254559210708562058605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2836372807139041372403875 4254559210708562058605813)
                ·
                  refine ⟨398864926003927692994295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4254559210708562058605813 398864926003927692994295)
                  ·
                    rfl

theorem cell20_873885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_873885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873885 prefixEnd_873885 := by exact prefixLift 873885
  have htrace : WordTrace (prefixWord ++ tailWord_873885) baseStart_873885 baseEnd_873885 := by
    simpa [prefixWord, tailWord_873885, baseEnd_873885] using wordTrace_append hprefix tailTrace_873885
  have hstable : (prefixWord ++ tailWord_873885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873885).length < 2 ^ (prefixWord ++ tailWord_873885).sum := by decide
  have hdescent : baseEnd_873885 < baseStart_873885 := by decide
  rcases family_descends (prefixWord ++ tailWord_873885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873888 : List Nat := [2, 1, 1, 4, 1, 2, 5, 2, 2]
def baseStart_873888 : Nat := 118140960795 + 873888 * 2 ^ 59
def prefixEnd_873888 : Nat := 4983230072969 + 3 ^ 40 * 873888 * 2
def baseEnd_873888 : Nat := 398866295285673015894283

theorem tailTrace_873888 : CollatzResearch.WordTrace tailWord_873888 prefixEnd_873888 398866295285673015894283 := by
  unfold tailWord_873888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936656929030249516627159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21248875905373666022169545 15936656929030249516627159)
  ·
    refine ⟨23904985393545374274940739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15936656929030249516627159 23904985393545374274940739)
    ·
      refine ⟨35857478090318061412411109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23904985393545374274940739 35857478090318061412411109)
      ·
        refine ⟨6723277141934636514827083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35857478090318061412411109 6723277141934636514827083)
        ·
          refine ⟨10084915712901954772240625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723277141934636514827083 10084915712901954772240625)
          ·
            refine ⟨7563686784676466079180469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10084915712901954772240625 7563686784676466079180469)
            ·
              refine ⟨709095636063418694923169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7563686784676466079180469 709095636063418694923169)
              ·
                refine ⟨531821727047564021192377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709095636063418694923169 531821727047564021192377)
                ·
                  refine ⟨398866295285673015894283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531821727047564021192377 398866295285673015894283)
                  ·
                    rfl

theorem cell20_873888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_873888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873888 prefixEnd_873888 := by exact prefixLift 873888
  have htrace : WordTrace (prefixWord ++ tailWord_873888) baseStart_873888 baseEnd_873888 := by
    simpa [prefixWord, tailWord_873888, baseEnd_873888] using wordTrace_append hprefix tailTrace_873888
  have hstable : (prefixWord ++ tailWord_873888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873888).length < 2 ^ (prefixWord ++ tailWord_873888).sum := by decide
  have hdescent : baseEnd_873888 < baseStart_873888 := by decide
  rcases family_descends (prefixWord ++ tailWord_873888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873906 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_873906 : Nat := 118140960795 + 873906 * 2 ^ 59
def prefixEnd_873906 : Nat := 4983230072969 + 3 ^ 40 * 873906 * 2
def baseEnd_873906 : Nat := 398874510976144953294209

theorem tailTrace_873906 : CollatzResearch.WordTrace tailWord_873906 prefixEnd_873906 398874510976144953294209 := by
  unfold tailWord_873906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7968492592998822026852393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21249313581330192071606381 7968492592998822026852393)
  ·
    refine ⟨5976369444749116520139295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7968492592998822026852393 5976369444749116520139295)
    ·
      refine ⟨8964554167123674780208943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5976369444749116520139295 8964554167123674780208943)
      ·
        refine ⟨13446831250685512170313415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8964554167123674780208943 13446831250685512170313415)
        ·
          refine ⟨20170246876028268255470123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13446831250685512170313415 20170246876028268255470123)
          ·
            refine ⟨30255370314042402383205185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20170246876028268255470123 30255370314042402383205185)
            ·
              refine ⟨22691527735531801787403889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30255370314042402383205185 22691527735531801787403889)
              ·
                refine ⟨17018645801648851340552917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22691527735531801787403889 17018645801648851340552917)
                ·
                  refine ⟨398874510976144953294209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17018645801648851340552917 398874510976144953294209)
                  ·
                    rfl

theorem cell20_873906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_873906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873906 prefixEnd_873906 := by exact prefixLift 873906
  have htrace : WordTrace (prefixWord ++ tailWord_873906) baseStart_873906 baseEnd_873906 := by
    simpa [prefixWord, tailWord_873906, baseEnd_873906] using wordTrace_append hprefix tailTrace_873906
  have hstable : (prefixWord ++ tailWord_873906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873906).length < 2 ^ (prefixWord ++ tailWord_873906).sum := by decide
  have hdescent : baseEnd_873906 < baseStart_873906 := by decide
  rcases family_descends (prefixWord ++ tailWord_873906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873944 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_873944 : Nat := 118140960795 + 873944 * 2 ^ 59
def prefixEnd_873944 : Nat := 4983230072969 + 3 ^ 40 * 873944 * 2
def baseEnd_873944 : Nat := 398891855211585710027387

theorem tailTrace_873944 : CollatzResearch.WordTrace tailWord_873944 prefixEnd_873944 398891855211585710027387 := by
  unfold tailWord_873944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15937678172928810298646443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21250237563905080398195257 15937678172928810298646443)
  ·
    refine ⟨23906517259393215447969665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15937678172928810298646443 23906517259393215447969665)
    ·
      refine ⟨17929887944544911585977249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23906517259393215447969665 17929887944544911585977249)
      ·
        refine ⟨13447415958408683689482937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17929887944544911585977249 13447415958408683689482937)
        ·
          refine ⟨10085561968806512767112203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13447415958408683689482937 10085561968806512767112203)
          ·
            refine ⟨15128342953209769150668305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10085561968806512767112203 15128342953209769150668305)
            ·
              refine ⟨11346257214907326863001229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15128342953209769150668305 11346257214907326863001229)
              ·
                refine ⟨4254846455590247573625461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11346257214907326863001229 4254846455590247573625461)
                ·
                  refine ⟨398891855211585710027387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4254846455590247573625461 398891855211585710027387)
                  ·
                    rfl

theorem cell20_873944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_873944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873944 prefixEnd_873944 := by exact prefixLift 873944
  have htrace : WordTrace (prefixWord ++ tailWord_873944) baseStart_873944 baseEnd_873944 := by
    simpa [prefixWord, tailWord_873944, baseEnd_873944] using wordTrace_append hprefix tailTrace_873944
  have hstable : (prefixWord ++ tailWord_873944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873944).length < 2 ^ (prefixWord ++ tailWord_873944).sum := by decide
  have hdescent : baseEnd_873944 < baseStart_873944 := by decide
  rcases family_descends (prefixWord ++ tailWord_873944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873968 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_873968 : Nat := 118140960795 + 873968 * 2 ^ 59
def prefixEnd_873968 : Nat := 4983230072969 + 3 ^ 40 * 873968 * 2
def baseEnd_873968 : Nat := 398902809465548293227289

theorem tailTrace_873968 : CollatzResearch.WordTrace tailWord_873968 prefixEnd_873968 398902809465548293227289 := by
  unfold tailWord_873968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15938115848885336348083279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21250821131847115130777705 15938115848885336348083279)
  ·
    refine ⟨23907173773328004522124919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15938115848885336348083279 23907173773328004522124919)
    ·
      refine ⟨35860760659992006783187379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23907173773328004522124919 35860760659992006783187379)
      ·
        refine ⟨53791140989988010174781069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35860760659992006783187379 53791140989988010174781069)
        ·
          refine ⟨20171677871245503815542901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53791140989988010174781069 20171677871245503815542901)
          ·
            refine ⟨1891094800429265982707147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20171677871245503815542901 1891094800429265982707147)
            ·
              refine ⟨2836642200643898974060721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891094800429265982707147 2836642200643898974060721)
              ·
                refine ⟨2127481650482924230545541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836642200643898974060721 2127481650482924230545541)
                ·
                  refine ⟨398902809465548293227289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2127481650482924230545541 398902809465548293227289)
                  ·
                    rfl

theorem cell20_873968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_873968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873968 prefixEnd_873968 := by exact prefixLift 873968
  have htrace : WordTrace (prefixWord ++ tailWord_873968) baseStart_873968 baseEnd_873968 := by
    simpa [prefixWord, tailWord_873968, baseEnd_873968] using wordTrace_append hprefix tailTrace_873968
  have hstable : (prefixWord ++ tailWord_873968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873968).length < 2 ^ (prefixWord ++ tailWord_873968).sum := by decide
  have hdescent : baseEnd_873968 < baseStart_873968 := by decide
  rcases family_descends (prefixWord ++ tailWord_873968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873989 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_873989 : Nat := 118140960795 + 873989 * 2 ^ 59
def prefixEnd_873989 : Nat := 4983230072969 + 3 ^ 40 * 873989 * 2
def baseEnd_873989 : Nat := 398912394437765553527203

theorem tailTrace_873989 : CollatzResearch.WordTrace tailWord_873989 prefixEnd_873989 398912394437765553527203 := by
  unfold tailWord_873989
  simp only [CollatzResearch.WordTrace]
  refine ⟨31876997630694593282681021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21251331753796395521787347 31876997630694593282681021)
  ·
    refine ⟨11953874111510472481005383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31876997630694593282681021 11953874111510472481005383)
    ·
      refine ⟨17930811167265708721508075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11953874111510472481005383 17930811167265708721508075)
      ·
        refine ⟨26896216750898563082262113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17930811167265708721508075 26896216750898563082262113)
        ·
          refine ⟨20172162563173922311696585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26896216750898563082262113 20172162563173922311696585)
          ·
            refine ⟨15129121922380441733772439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20172162563173922311696585 15129121922380441733772439)
            ·
              refine ⟨22693682883570662600658659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15129121922380441733772439 22693682883570662600658659)
              ·
                refine ⟨34040524325355993900987989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22693682883570662600658659 34040524325355993900987989)
                ·
                  refine ⟨398912394437765553527203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34040524325355993900987989 398912394437765553527203)
                  ·
                    rfl

theorem cell20_873989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_873989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873989 prefixEnd_873989 := by exact prefixLift 873989
  have htrace : WordTrace (prefixWord ++ tailWord_873989) baseStart_873989 baseEnd_873989 := by
    simpa [prefixWord, tailWord_873989, baseEnd_873989] using wordTrace_append hprefix tailTrace_873989
  have hstable : (prefixWord ++ tailWord_873989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873989).length < 2 ^ (prefixWord ++ tailWord_873989).sum := by decide
  have hdescent : baseEnd_873989 < baseStart_873989 := by decide
  rcases family_descends (prefixWord ++ tailWord_873989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873995 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 3]
def baseStart_873995 : Nat := 118140960795 + 873995 * 2 ^ 59
def prefixEnd_873995 : Nat := 4983230072969 + 3 ^ 40 * 873995 * 2
def baseEnd_873995 : Nat := 398915133001256199327179

theorem tailTrace_873995 : CollatzResearch.WordTrace tailWord_873995 prefixEnd_873995 398915133001256199327179 := by
  unfold tailWord_873995
  simp only [CollatzResearch.WordTrace]
  refine ⟨31877216468672856307399439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21251477645781904204932959 31877216468672856307399439)
  ·
    refine ⟨47815824703009284461099159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31877216468672856307399439 47815824703009284461099159)
    ·
      refine ⟨71723737054513926691648739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47815824703009284461099159 71723737054513926691648739)
      ·
        refine ⟨107585605581770890037473109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71723737054513926691648739 107585605581770890037473109)
        ·
          refine ⟨630384407705688808813319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 107585605581770890037473109 630384407705688808813319)
          ·
            refine ⟨945576611558533213219979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630384407705688808813319 945576611558533213219979)
            ·
              refine ⟨1418364917337799819829969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945576611558533213219979 1418364917337799819829969)
              ·
                refine ⟨1063773688003349864872477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418364917337799819829969 1063773688003349864872477)
                ·
                  refine ⟨398915133001256199327179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063773688003349864872477 398915133001256199327179)
                  ·
                    rfl

theorem cell20_873995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 3].length) (baseStart_873995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_873995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_873995 prefixEnd_873995 := by exact prefixLift 873995
  have htrace : WordTrace (prefixWord ++ tailWord_873995) baseStart_873995 baseEnd_873995 := by
    simpa [prefixWord, tailWord_873995, baseEnd_873995] using wordTrace_append hprefix tailTrace_873995
  have hstable : (prefixWord ++ tailWord_873995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873995).length < 2 ^ (prefixWord ++ tailWord_873995).sum := by decide
  have hdescent : baseEnd_873995 < baseStart_873995 := by decide
  rcases family_descends (prefixWord ++ tailWord_873995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874013 : List Nat := [1, 4, 2, 2, 1, 1, 2, 7]
def baseStart_874013 : Nat := 118140960795 + 874013 * 2 ^ 59
def prefixEnd_874013 : Nat := 4983230072969 + 3 ^ 40 * 874013 * 2
def baseEnd_874013 : Nat := 132974449563909378909035

theorem tailTrace_874013 : CollatzResearch.WordTrace tailWord_874013 prefixEnd_874013 132974449563909378909035 := by
  unfold tailWord_874013
  simp only [CollatzResearch.WordTrace]
  refine ⟨31877872982607645381554693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21251915321738430254369795 31877872982607645381554693)
  ·
    refine ⟨5977101184238933509041505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31877872982607645381554693 5977101184238933509041505)
    ·
      refine ⟨4482825888179200131781129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5977101184238933509041505 4482825888179200131781129)
      ·
        refine ⟨3362119416134400098835847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4482825888179200131781129 3362119416134400098835847)
        ·
          refine ⟨5043179124201600148253771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362119416134400098835847 5043179124201600148253771)
          ·
            refine ⟨7564768686302400222380657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043179124201600148253771 7564768686302400222380657)
            ·
              refine ⟨5673576514726800166785493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7564768686302400222380657 5673576514726800166785493)
              ·
                refine ⟨132974449563909378909035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5673576514726800166785493 132974449563909378909035)
                ·
                  rfl

theorem cell20_874013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_874013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874013 prefixEnd_874013 := by exact prefixLift 874013
  have htrace : WordTrace (prefixWord ++ tailWord_874013) baseStart_874013 baseEnd_874013 := by
    simpa [prefixWord, tailWord_874013, baseEnd_874013] using wordTrace_append hprefix tailTrace_874013
  have hstable : (prefixWord ++ tailWord_874013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874013).length < 2 ^ (prefixWord ++ tailWord_874013).sum := by decide
  have hdescent : baseEnd_874013 < baseStart_874013 := by decide
  rcases family_descends (prefixWord ++ tailWord_874013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874030 : List Nat := [4, 1, 3, 1, 2, 2, 1, 6]
def baseStart_874030 : Nat := 118140960795 + 874030 * 2 ^ 59
def prefixEnd_874030 : Nat := 4983230072969 + 3 ^ 40 * 874030 * 2
def baseEnd_874030 : Nat := 132977035984983877720123

theorem tailTrace_874030 : CollatzResearch.WordTrace tailWord_874030 prefixEnd_874030 132977035984983877720123 := by
  unfold tailWord_874030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984811627943257160615443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21252328682364038189949029 3984811627943257160615443)
  ·
    refine ⟨5977217441914885740923165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3984811627943257160615443 5977217441914885740923165)
    ·
      refine ⟨2241456540718082152846187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5977217441914885740923165 2241456540718082152846187)
      ·
        refine ⟨3362184811077123229269281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241456540718082152846187 3362184811077123229269281)
        ·
          refine ⟨2521638608307842421951961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3362184811077123229269281 2521638608307842421951961)
          ·
            refine ⟨1891228956230881816463971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2521638608307842421951961 1891228956230881816463971)
            ·
              refine ⟨2836843434346322724695957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891228956230881816463971 2836843434346322724695957)
              ·
                refine ⟨132977035984983877720123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2836843434346322724695957 132977035984983877720123)
                ·
                  rfl

theorem cell20_874030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_874030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874030 prefixEnd_874030 := by exact prefixLift 874030
  have htrace : WordTrace (prefixWord ++ tailWord_874030) baseStart_874030 baseEnd_874030 := by
    simpa [prefixWord, tailWord_874030, baseEnd_874030] using wordTrace_append hprefix tailTrace_874030
  have hstable : (prefixWord ++ tailWord_874030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874030).length < 2 ^ (prefixWord ++ tailWord_874030).sum := by decide
  have hdescent : baseEnd_874030 < baseStart_874030 := by decide
  rcases family_descends (prefixWord ++ tailWord_874030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874040 : List Nat := [2, 1, 2, 1, 4, 4, 1, 3, 2]
def baseStart_874040 : Nat := 118140960795 + 874040 * 2 ^ 59
def prefixEnd_874040 : Nat := 4983230072969 + 3 ^ 40 * 874040 * 2
def baseEnd_874040 : Nat := 398935672227436042826995

theorem tailTrace_874040 : CollatzResearch.WordTrace tailWord_874040 prefixEnd_874040 398935672227436042826995 := by
  unfold tailWord_874040
  simp only [CollatzResearch.WordTrace]
  refine ⟨15939428876754914496393787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21252571835673219328525049 15939428876754914496393787)
  ·
    refine ⟨23909143315132371744590681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15939428876754914496393787 23909143315132371744590681)
    ·
      refine ⟨17931857486349278808443011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23909143315132371744590681 17931857486349278808443011)
      ·
        refine ⟨26897786229523918212664517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17931857486349278808443011 26897786229523918212664517)
        ·
          refine ⟨5043334918035734664874597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26897786229523918212664517 5043334918035734664874597)
          ·
            refine ⟨945625297131700249663987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5043334918035734664874597 945625297131700249663987)
            ·
              refine ⟨1418437945697550374495981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945625297131700249663987 1418437945697550374495981)
              ·
                refine ⟨531914229636581390435993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1418437945697550374495981 531914229636581390435993)
                ·
                  refine ⟨398935672227436042826995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531914229636581390435993 398935672227436042826995)
                  ·
                    rfl

theorem cell20_874040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_874040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874040 prefixEnd_874040 := by exact prefixLift 874040
  have htrace : WordTrace (prefixWord ++ tailWord_874040) baseStart_874040 baseEnd_874040 := by
    simpa [prefixWord, tailWord_874040, baseEnd_874040] using wordTrace_append hprefix tailTrace_874040
  have hstable : (prefixWord ++ tailWord_874040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874040).length < 2 ^ (prefixWord ++ tailWord_874040).sum := by decide
  have hdescent : baseEnd_874040 < baseStart_874040 := by decide
  rcases family_descends (prefixWord ++ tailWord_874040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874058 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_874058 : Nat := 118140960795 + 874058 * 2 ^ 59
def prefixEnd_874058 : Nat := 4983230072969 + 3 ^ 40 * 874058 * 2
def baseEnd_874058 : Nat := 398943887917907980226921

theorem tailTrace_874058 : CollatzResearch.WordTrace tailWord_874058 prefixEnd_874058 398943887917907980226921 := by
  unfold tailWord_874058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7969878566861154516735707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21253009511629745377961885 7969878566861154516735707)
  ·
    refine ⟨11954817850291731775103561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7969878566861154516735707 11954817850291731775103561)
    ·
      refine ⟨8966113387718798831327671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11954817850291731775103561 8966113387718798831327671)
      ·
        refine ⟨13449170081578198246991507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8966113387718798831327671 13449170081578198246991507)
        ·
          refine ⟨20173755122367297370487261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13449170081578198246991507 20173755122367297370487261)
          ·
            refine ⟨7565158170887736513932723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20173755122367297370487261 7565158170887736513932723)
            ·
              refine ⟨11347737256331604770899085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7565158170887736513932723 11347737256331604770899085)
              ·
                refine ⟨4255401471124351789087157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11347737256331604770899085 4255401471124351789087157)
                ·
                  refine ⟨398943887917907980226921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4255401471124351789087157 398943887917907980226921)
                  ·
                    rfl

theorem cell20_874058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_874058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874058 prefixEnd_874058 := by exact prefixLift 874058
  have htrace : WordTrace (prefixWord ++ tailWord_874058) baseStart_874058 baseEnd_874058 := by
    simpa [prefixWord, tailWord_874058, baseEnd_874058] using wordTrace_append hprefix tailTrace_874058
  have hstable : (prefixWord ++ tailWord_874058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874058).length < 2 ^ (prefixWord ++ tailWord_874058).sum := by decide
  have hdescent : baseEnd_874058 < baseStart_874058 := by decide
  rcases family_descends (prefixWord ++ tailWord_874058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874113 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 3]
def baseStart_874113 : Nat := 118140960795 + 874113 * 2 ^ 59
def prefixEnd_874113 : Nat := 4983230072969 + 3 ^ 40 * 874113 * 2
def baseEnd_874113 : Nat := 398968991416572233393363

theorem tailTrace_874113 : CollatzResearch.WordTrace tailWord_874113 prefixEnd_874113 398968991416572233393363 := by
  unfold tailWord_874113
  simp only [CollatzResearch.WordTrace]
  refine ⟨31881520282245362460194993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21254346854830241640129995 31881520282245362460194993)
  ·
    refine ⟨23911140211684021845146245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31881520282245362460194993 23911140211684021845146245)
    ·
      refine ⟨4483338789690754095964921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23911140211684021845146245 4483338789690754095964921)
      ·
        refine ⟨3362504092268065571973691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4483338789690754095964921 3362504092268065571973691)
        ·
          refine ⟨5043756138402098357960537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362504092268065571973691 5043756138402098357960537)
          ·
            refine ⟨3782817103801573768470403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5043756138402098357960537 3782817103801573768470403)
            ·
              refine ⟨5674225655702360652705605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782817103801573768470403 5674225655702360652705605)
              ·
                refine ⟨1063917310444192622382301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5674225655702360652705605 1063917310444192622382301)
                ·
                  refine ⟨398968991416572233393363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063917310444192622382301 398968991416572233393363)
                  ·
                    rfl

theorem cell20_874113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_874113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874113 prefixEnd_874113 := by exact prefixLift 874113
  have htrace : WordTrace (prefixWord ++ tailWord_874113) baseStart_874113 baseEnd_874113 := by
    simpa [prefixWord, tailWord_874113, baseEnd_874113] using wordTrace_append hprefix tailTrace_874113
  have hstable : (prefixWord ++ tailWord_874113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874113).length < 2 ^ (prefixWord ++ tailWord_874113).sum := by decide
  have hdescent : baseEnd_874113 < baseStart_874113 := by decide
  rcases family_descends (prefixWord ++ tailWord_874113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874116 : List Nat := [2, 3, 2, 1, 4, 1, 1, 4, 2]
def baseStart_874116 : Nat := 118140960795 + 874116 * 2 ^ 59
def prefixEnd_874116 : Nat := 4983230072969 + 3 ^ 40 * 874116 * 2
def baseEnd_874116 : Nat := 398970360698317556293351

theorem tailTrace_874116 : CollatzResearch.WordTrace tailWord_874116 prefixEnd_874116 398970360698317556293351 := by
  unfold tailWord_874116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15940814850617246986277101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21254419800822995981702801 15940814850617246986277101)
  ·
    refine ⟨5977805568981467619853913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15940814850617246986277101 5977805568981467619853913)
    ·
      refine ⟨4483354176736100714890435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5977805568981467619853913 4483354176736100714890435)
      ·
        refine ⟨6725031265104151072335653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4483354176736100714890435 6725031265104151072335653)
        ·
          refine ⟨1260943362207028326062935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6725031265104151072335653 1260943362207028326062935)
          ·
            refine ⟨1891415043310542489094403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260943362207028326062935 1891415043310542489094403)
            ·
              refine ⟨2837122564965813733641605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891415043310542489094403 2837122564965813733641605)
              ·
                refine ⟨531960480931090075057801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2837122564965813733641605 531960480931090075057801)
                ·
                  refine ⟨398970360698317556293351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531960480931090075057801 398970360698317556293351)
                  ·
                    rfl

theorem cell20_874116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_874116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874116 prefixEnd_874116 := by exact prefixLift 874116
  have htrace : WordTrace (prefixWord ++ tailWord_874116) baseStart_874116 baseEnd_874116 := by
    simpa [prefixWord, tailWord_874116, baseEnd_874116] using wordTrace_append hprefix tailTrace_874116
  have hstable : (prefixWord ++ tailWord_874116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874116).length < 2 ^ (prefixWord ++ tailWord_874116).sum := by decide
  have hdescent : baseEnd_874116 < baseStart_874116 := by decide
  rcases family_descends (prefixWord ++ tailWord_874116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874144 : List Nat := [2, 1, 1, 4, 3, 2, 3, 4]
def baseStart_874144 : Nat := 118140960795 + 874144 * 2 ^ 59
def prefixEnd_874144 : Nat := 4983230072969 + 3 ^ 40 * 874144 * 2
def baseEnd_874144 : Nat := 132994380220424634453301

theorem tailTrace_874144 : CollatzResearch.WordTrace tailWord_874144 prefixEnd_874144 132994380220424634453301 := by
  unfold tailWord_874144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15941325472566527377286743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21255100630088703169715657 15941325472566527377286743)
  ·
    refine ⟨23911988208849791065930115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15941325472566527377286743 23911988208849791065930115)
    ·
      refine ⟨35867982313274686598895173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23911988208849791065930115 35867982313274686598895173)
      ·
        refine ⟨6725246683739003737292845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35867982313274686598895173 6725246683739003737292845)
        ·
          refine ⟨2521967506402126401484817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6725246683739003737292845 2521967506402126401484817)
          ·
            refine ⟨1891475629801594801113613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2521967506402126401484817 1891475629801594801113613)
            ·
              refine ⟨709303361175598050417605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1891475629801594801113613 709303361175598050417605)
              ·
                refine ⟨132994380220424634453301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709303361175598050417605 132994380220424634453301)
                ·
                  rfl

theorem cell20_874144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_874144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874144 prefixEnd_874144 := by exact prefixLift 874144
  have htrace : WordTrace (prefixWord ++ tailWord_874144) baseStart_874144 baseEnd_874144 := by
    simpa [prefixWord, tailWord_874144, baseEnd_874144] using wordTrace_append hprefix tailTrace_874144
  have hstable : (prefixWord ++ tailWord_874144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874144).length < 2 ^ (prefixWord ++ tailWord_874144).sum := by decide
  have hdescent : baseEnd_874144 < baseStart_874144 := by decide
  rcases family_descends (prefixWord ++ tailWord_874144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874209 : List Nat := [1, 2, 3, 1, 6, 1, 1, 3, 2]
def baseStart_874209 : Nat := 118140960795 + 874209 * 2 ^ 59
def prefixEnd_874209 : Nat := 4983230072969 + 3 ^ 40 * 874209 * 2
def baseEnd_874209 : Nat := 399012808432422566192971

theorem tailTrace_874209 : CollatzResearch.WordTrace tailWord_874209 prefixEnd_874209 399012808432422566192971 := by
  unfold tailWord_874209
  simp only [CollatzResearch.WordTrace]
  refine ⟨31885021689897570855689681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21256681126598380570459787 31885021689897570855689681)
  ·
    refine ⟨23913766267423178141767261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31885021689897570855689681 23913766267423178141767261)
    ·
      refine ⟨8967662350283691803162723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23913766267423178141767261 8967662350283691803162723)
      ·
        refine ⟨13451493525425537704744085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8967662350283691803162723 13451493525425537704744085)
        ·
          refine ⟨630538759004322079909879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13451493525425537704744085 630538759004322079909879)
          ·
            refine ⟨945808138506483119864819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630538759004322079909879 945808138506483119864819)
            ·
              refine ⟨1418712207759724679797229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945808138506483119864819 1418712207759724679797229)
              ·
                refine ⟨532017077909896754923961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1418712207759724679797229 532017077909896754923961)
                ·
                  refine ⟨399012808432422566192971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532017077909896754923961 399012808432422566192971)
                  ·
                    rfl

theorem cell20_874209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_874209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874209 prefixEnd_874209 := by exact prefixLift 874209
  have htrace : WordTrace (prefixWord ++ tailWord_874209) baseStart_874209 baseEnd_874209 := by
    simpa [prefixWord, tailWord_874209, baseEnd_874209] using wordTrace_append hprefix tailTrace_874209
  have hstable : (prefixWord ++ tailWord_874209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874209).length < 2 ^ (prefixWord ++ tailWord_874209).sum := by decide
  have hdescent : baseEnd_874209 < baseStart_874209 := by decide
  rcases family_descends (prefixWord ++ tailWord_874209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874244 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_874244 : Nat := 118140960795 + 874244 * 2 ^ 59
def prefixEnd_874244 : Nat := 4983230072969 + 3 ^ 40 * 874244 * 2
def baseEnd_874244 : Nat := 399028783386118000026161

theorem tailTrace_874244 : CollatzResearch.WordTrace tailWord_874244 prefixEnd_874244 399028783386118000026161 := by
  unfold tailWord_874244
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943149122385385916606893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21257532163180514555475857 15943149122385385916606893)
  ·
    refine ⟨5978680920894519718727585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15943149122385385916606893 5978680920894519718727585)
    ·
      refine ⟨4484010690670889789045689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5978680920894519718727585 4484010690670889789045689)
      ·
        refine ⟨3363008018003167341784267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4484010690670889789045689 3363008018003167341784267)
        ·
          refine ⟨5044512027004751012676401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3363008018003167341784267 5044512027004751012676401)
          ·
            refine ⟨3783384020253563259507301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5044512027004751012676401 3783384020253563259507301)
            ·
              refine ⟨709384503797543111157619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3783384020253563259507301 709384503797543111157619)
              ·
                refine ⟨1064076755696314666736429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709384503797543111157619 1064076755696314666736429)
                ·
                  refine ⟨399028783386118000026161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064076755696314666736429 399028783386118000026161)
                  ·
                    rfl

theorem cell20_874244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_874244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874244 prefixEnd_874244 := by exact prefixLift 874244
  have htrace : WordTrace (prefixWord ++ tailWord_874244) baseStart_874244 baseEnd_874244 := by
    simpa [prefixWord, tailWord_874244, baseEnd_874244] using wordTrace_append hprefix tailTrace_874244
  have hstable : (prefixWord ++ tailWord_874244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874244).length < 2 ^ (prefixWord ++ tailWord_874244).sum := by decide
  have hdescent : baseEnd_874244 < baseStart_874244 := by decide
  rcases family_descends (prefixWord ++ tailWord_874244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874258 : List Nat := [3, 2, 4, 1, 1, 1, 2, 6]
def baseStart_874258 : Nat := 118140960795 + 874258 * 2 ^ 59
def prefixEnd_874258 : Nat := 4983230072969 + 3 ^ 40 * 874258 * 2
def baseEnd_874258 : Nat := 133011724455865391186479

theorem tailTrace_874258 : CollatzResearch.WordTrace tailWord_874258 prefixEnd_874258 133011724455865391186479 := by
  unfold tailWord_874258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7971702216680013056055857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21257872577813368149482285 7971702216680013056055857)
  ·
    refine ⟨5978776662510009792041893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7971702216680013056055857 5978776662510009792041893)
    ·
      refine ⟨1121020624220626836007855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5978776662510009792041893 1121020624220626836007855)
      ·
        refine ⟨1681530936330940254011783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121020624220626836007855 1681530936330940254011783)
        ·
          refine ⟨2522296404496410381017675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681530936330940254011783 2522296404496410381017675)
          ·
            refine ⟨3783444606744615571526513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522296404496410381017675 3783444606744615571526513)
            ·
              refine ⟨2837583455058461678644885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3783444606744615571526513 2837583455058461678644885)
              ·
                refine ⟨133011724455865391186479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2837583455058461678644885 133011724455865391186479)
                ·
                  rfl

theorem cell20_874258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_874258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874258 prefixEnd_874258 := by exact prefixLift 874258
  have htrace : WordTrace (prefixWord ++ tailWord_874258) baseStart_874258 baseEnd_874258 := by
    simpa [prefixWord, tailWord_874258, baseEnd_874258] using wordTrace_append hprefix tailTrace_874258
  have hstable : (prefixWord ++ tailWord_874258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874258).length < 2 ^ (prefixWord ++ tailWord_874258).sum := by decide
  have hdescent : baseEnd_874258 < baseStart_874258 := by decide
  rcases family_descends (prefixWord ++ tailWord_874258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874289 : List Nat := [1, 2, 2, 3, 2, 3, 1, 4, 2]
def baseStart_874289 : Nat := 118140960795 + 874289 * 2 ^ 59
def prefixEnd_874289 : Nat := 4983230072969 + 3 ^ 40 * 874289 * 2
def baseEnd_874289 : Nat := 399049322612297843525977

theorem tailTrace_874289 : CollatzResearch.WordTrace tailWord_874289 prefixEnd_874289 399049322612297843525977 := by
  unfold tailWord_874289
  simp only [CollatzResearch.WordTrace]
  refine ⟨31887939529607744518601921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21258626353071829679067947 31887939529607744518601921)
  ·
    refine ⟨23915954647205808388951441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31887939529607744518601921 23915954647205808388951441)
    ·
      refine ⟨17936965985404356291713581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23915954647205808388951441 17936965985404356291713581)
      ·
        refine ⟨6726362244526633609392593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17936965985404356291713581 6726362244526633609392593)
        ·
          refine ⟨5044771683394975207044445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6726362244526633609392593 5044771683394975207044445)
          ·
            refine ⟨1891789381273115702641667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5044771683394975207044445 1891789381273115702641667)
            ·
              refine ⟨2837684071909673553962501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891789381273115702641667 2837684071909673553962501)
              ·
                refine ⟨532065763483063791367969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2837684071909673553962501 532065763483063791367969)
                ·
                  refine ⟨399049322612297843525977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532065763483063791367969 399049322612297843525977)
                  ·
                    rfl

theorem cell20_874289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_874289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874289 prefixEnd_874289 := by exact prefixLift 874289
  have htrace : WordTrace (prefixWord ++ tailWord_874289) baseStart_874289 baseEnd_874289 := by
    simpa [prefixWord, tailWord_874289, baseEnd_874289] using wordTrace_append hprefix tailTrace_874289
  have hstable : (prefixWord ++ tailWord_874289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874289).length < 2 ^ (prefixWord ++ tailWord_874289).sum := by decide
  have hdescent : baseEnd_874289 < baseStart_874289 := by decide
  rcases family_descends (prefixWord ++ tailWord_874289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874348 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_874348 : Nat := 118140960795 + 874348 * 2 ^ 59
def prefixEnd_874348 : Nat := 4983230072969 + 3 ^ 40 * 874348 * 2
def baseEnd_874348 : Nat := 399076251819955860559069

theorem tailTrace_874348 : CollatzResearch.WordTrace tailWord_874348 prefixEnd_874348 399076251819955860559069 := by
  unfold tailWord_874348
  simp only [CollatzResearch.WordTrace]
  refine ⟨15945045718196998797499849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21260060957595998396666465 15945045718196998797499849)
  ·
    refine ⟨11958784288647749098124887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15945045718196998797499849 11958784288647749098124887)
    ·
      refine ⟨17938176432971623647187331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11958784288647749098124887 17938176432971623647187331)
      ·
        refine ⟨26907264649457435470780997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17938176432971623647187331 26907264649457435470780997)
        ·
          refine ⟨5045112121773269150771437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26907264649457435470780997 5045112121773269150771437)
          ·
            refine ⟨1891917045664975931539289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5045112121773269150771437 1891917045664975931539289)
            ·
              refine ⟨1418937784248731948654467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891917045664975931539289 1418937784248731948654467)
              ·
                refine ⟨2128406676373097922981701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418937784248731948654467 2128406676373097922981701)
                ·
                  refine ⟨399076251819955860559069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128406676373097922981701 399076251819955860559069)
                  ·
                    rfl

theorem cell20_874348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_874348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874348 prefixEnd_874348 := by exact prefixLift 874348
  have htrace : WordTrace (prefixWord ++ tailWord_874348) baseStart_874348 baseEnd_874348 := by
    simpa [prefixWord, tailWord_874348, baseEnd_874348] using wordTrace_append hprefix tailTrace_874348
  have hstable : (prefixWord ++ tailWord_874348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874348).length < 2 ^ (prefixWord ++ tailWord_874348).sum := by decide
  have hdescent : baseEnd_874348 < baseStart_874348 := by decide
  rcases family_descends (prefixWord ++ tailWord_874348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874362 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_874362 : Nat := 118140960795 + 874362 * 2 ^ 59
def prefixEnd_874362 : Nat := 4983230072969 + 3 ^ 40 * 874362 * 2
def baseEnd_874362 : Nat := 399082641801434034092345

theorem tailTrace_874362 : CollatzResearch.WordTrace tailWord_874362 prefixEnd_874362 399082641801434034092345 := by
  unfold tailWord_874362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7972650514585819496502335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21260401372228851990672893 7972650514585819496502335)
  ·
    refine ⟨11958975771878729244753503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7972650514585819496502335 11958975771878729244753503)
    ·
      refine ⟨17938463657818093867130255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11958975771878729244753503 17938463657818093867130255)
      ·
        refine ⟨26907695486727140800695383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17938463657818093867130255 26907695486727140800695383)
        ·
          refine ⟨40361543230090711201043075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26907695486727140800695383 40361543230090711201043075)
          ·
            refine ⟨60542314845136066801564613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40361543230090711201043075 60542314845136066801564613)
            ·
              refine ⟨11351684033463012525293365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60542314845136066801564613 11351684033463012525293365)
              ·
                refine ⟨1064220378137157424246253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11351684033463012525293365 1064220378137157424246253)
                ·
                  refine ⟨399082641801434034092345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064220378137157424246253 399082641801434034092345)
                  ·
                    rfl

theorem cell20_874362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_874362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874362 prefixEnd_874362 := by exact prefixLift 874362
  have htrace : WordTrace (prefixWord ++ tailWord_874362) baseStart_874362 baseEnd_874362 := by
    simpa [prefixWord, tailWord_874362, baseEnd_874362] using wordTrace_append hprefix tailTrace_874362
  have hstable : (prefixWord ++ tailWord_874362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874362).length < 2 ^ (prefixWord ++ tailWord_874362).sum := by decide
  have hdescent : baseEnd_874362 < baseStart_874362 := by decide
  rcases family_descends (prefixWord ++ tailWord_874362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874400 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_874400 : Nat := 118140960795 + 874400 * 2 ^ 59
def prefixEnd_874400 : Nat := 4983230072969 + 3 ^ 40 * 874400 * 2
def baseEnd_874400 : Nat := 399099986036874790825523

theorem tailTrace_874400 : CollatzResearch.WordTrace tailWord_874400 prefixEnd_874400 399099986036874790825523 := by
  unfold tailWord_874400
  simp only [CollatzResearch.WordTrace]
  refine ⟨15945994016102805237946327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21261325354803740317261769 15945994016102805237946327)
  ·
    refine ⟨23918991024154207856919491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15945994016102805237946327 23918991024154207856919491)
    ·
      refine ⟨35878486536231311785379237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23918991024154207856919491 35878486536231311785379237)
      ·
        refine ⟨6727216225543370959758607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35878486536231311785379237 6727216225543370959758607)
        ·
          refine ⟨10090824338315056439637911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6727216225543370959758607 10090824338315056439637911)
          ·
            refine ⟨15136236507472584659456867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10090824338315056439637911 15136236507472584659456867)
            ·
              refine ⟨22704354761208876989185301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15136236507472584659456867 22704354761208876989185301)
              ·
                refine ⟨1064266629431666108868061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22704354761208876989185301 1064266629431666108868061)
                ·
                  refine ⟨399099986036874790825523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064266629431666108868061 399099986036874790825523)
                  ·
                    rfl

theorem cell20_874400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_874400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874400 prefixEnd_874400 := by exact prefixLift 874400
  have htrace : WordTrace (prefixWord ++ tailWord_874400) baseStart_874400 baseEnd_874400 := by
    simpa [prefixWord, tailWord_874400, baseEnd_874400] using wordTrace_append hprefix tailTrace_874400
  have hstable : (prefixWord ++ tailWord_874400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874400).length < 2 ^ (prefixWord ++ tailWord_874400).sum := by decide
  have hdescent : baseEnd_874400 < baseStart_874400 := by decide
  rcases family_descends (prefixWord ++ tailWord_874400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874417 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 3]
def baseStart_874417 : Nat := 118140960795 + 874417 * 2 ^ 59
def prefixEnd_874417 : Nat := 4983230072969 + 3 ^ 40 * 874417 * 2
def baseEnd_874417 : Nat := 399107745300098287258787

theorem tailTrace_874417 : CollatzResearch.WordTrace tailWord_874417 prefixEnd_874417 399107745300098287258787 := by
  unfold tailWord_874417
  simp only [CollatzResearch.WordTrace]
  refine ⟨31892608073144022379261505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21261738715429348252841003 31892608073144022379261505)
  ·
    refine ⟨23919456054858016784446129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31892608073144022379261505 23919456054858016784446129)
    ·
      refine ⟨17939592041143512588334597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23919456054858016784446129 17939592041143512588334597)
      ·
        refine ⟨3363673507714408610312737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17939592041143512588334597 3363673507714408610312737)
        ·
          refine ⟨2522755130785806457734553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3363673507714408610312737 2522755130785806457734553)
          ·
            refine ⟨1892066348089354843300915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2522755130785806457734553 1892066348089354843300915)
            ·
              refine ⟨2838099522134032264951373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892066348089354843300915 2838099522134032264951373)
              ·
                refine ⟨1064287320800262099356765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2838099522134032264951373 1064287320800262099356765)
                ·
                  refine ⟨399107745300098287258787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064287320800262099356765 399107745300098287258787)
                  ·
                    rfl

theorem cell20_874417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_874417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874417 prefixEnd_874417 := by exact prefixLift 874417
  have htrace : WordTrace (prefixWord ++ tailWord_874417) baseStart_874417 baseEnd_874417 := by
    simpa [prefixWord, tailWord_874417, baseEnd_874417] using wordTrace_append hprefix tailTrace_874417
  have hstable : (prefixWord ++ tailWord_874417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874417).length < 2 ^ (prefixWord ++ tailWord_874417).sum := by decide
  have hdescent : baseEnd_874417 < baseStart_874417 := by decide
  rcases family_descends (prefixWord ++ tailWord_874417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874454 : List Nat := [5, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_874454 : Nat := 118140960795 + 874454 * 2 ^ 59
def prefixEnd_874454 : Nat := 4983230072969 + 3 ^ 40 * 874454 * 2
def baseEnd_874454 : Nat := 399124633108290603025303

theorem tailTrace_874454 : CollatzResearch.WordTrace tailWord_874454 prefixEnd_874454 399124633108290603025303 := by
  unfold tailWord_874454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993372348375623606147401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21262638382673318465572277 1993372348375623606147401)
  ·
    refine ⟨1495029261281717704610551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1993372348375623606147401 1495029261281717704610551)
    ·
      refine ⟨2242543891922576556915827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495029261281717704610551 2242543891922576556915827)
      ·
        refine ⟨3363815837883864835373741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242543891922576556915827 3363815837883864835373741)
        ·
          refine ⟨1261430939206449313265153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3363815837883864835373741 1261430939206449313265153)
          ·
            refine ⟨946073204404836984948865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261430939206449313265153 946073204404836984948865)
            ·
              refine ⟨709554903303627738711649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946073204404836984948865 709554903303627738711649)
              ·
                refine ⟨532166177477720804033737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709554903303627738711649 532166177477720804033737)
                ·
                  refine ⟨399124633108290603025303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532166177477720804033737 399124633108290603025303)
                  ·
                    rfl

theorem cell20_874454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_874454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874454 prefixEnd_874454 := by exact prefixLift 874454
  have htrace : WordTrace (prefixWord ++ tailWord_874454) baseStart_874454 baseEnd_874454 := by
    simpa [prefixWord, tailWord_874454, baseEnd_874454] using wordTrace_append hprefix tailTrace_874454
  have hstable : (prefixWord ++ tailWord_874454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874454).length < 2 ^ (prefixWord ++ tailWord_874454).sum := by decide
  have hdescent : baseEnd_874454 < baseStart_874454 := by decide
  rcases family_descends (prefixWord ++ tailWord_874454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874502 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_874502 : Nat := 118140960795 + 874502 * 2 ^ 59
def prefixEnd_874502 : Nat := 4983230072969 + 3 ^ 40 * 874502 * 2
def baseEnd_874502 : Nat := 399146541616215769425107

theorem tailTrace_874502 : CollatzResearch.WordTrace tailWord_874502 prefixEnd_874502 399146541616215769425107 := by
  unfold tailWord_874502
  simp only [CollatzResearch.WordTrace]
  refine ⟨996740883682377559253305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21263805518557387930737173 996740883682377559253305)
  ·
    refine ⟨747555662761783169439979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 996740883682377559253305 747555662761783169439979)
    ·
      refine ⟨1121333494142674754159969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747555662761783169439979 1121333494142674754159969)
      ·
        refine ⟨841000120607006065619977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1121333494142674754159969 841000120607006065619977)
        ·
          refine ⟨630750090455254549214983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841000120607006065619977 630750090455254549214983)
          ·
            refine ⟨946125135682881823822475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630750090455254549214983 946125135682881823822475)
            ·
              refine ⟨1419187703524322735733713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946125135682881823822475 1419187703524322735733713)
              ·
                refine ⟨1064390777643242051800285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419187703524322735733713 1064390777643242051800285)
                ·
                  refine ⟨399146541616215769425107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064390777643242051800285 399146541616215769425107)
                  ·
                    rfl

theorem cell20_874502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_874502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874502 prefixEnd_874502 := by exact prefixLift 874502
  have htrace : WordTrace (prefixWord ++ tailWord_874502) baseStart_874502 baseEnd_874502 := by
    simpa [prefixWord, tailWord_874502, baseEnd_874502] using wordTrace_append hprefix tailTrace_874502
  have hstable : (prefixWord ++ tailWord_874502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874502).length < 2 ^ (prefixWord ++ tailWord_874502).sum := by decide
  have hdescent : baseEnd_874502 < baseStart_874502 := by decide
  rcases family_descends (prefixWord ++ tailWord_874502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874531 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 3]
def baseStart_874531 : Nat := 118140960795 + 874531 * 2 ^ 59
def prefixEnd_874531 : Nat := 4983230072969 + 3 ^ 40 * 874531 * 2
def baseEnd_874531 : Nat := 399159778006420557458321

theorem tailTrace_874531 : CollatzResearch.WordTrace tailWord_874531 prefixEnd_874531 399159778006420557458321 := by
  unfold tailWord_874531
  simp only [CollatzResearch.WordTrace]
  refine ⟨31896765994731019848911447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21264510663154013232607631 31896765994731019848911447)
  ·
    refine ⟨47845148992096529773367171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31896765994731019848911447 47845148992096529773367171)
    ·
      refine ⟨71767723488144794660050757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47845148992096529773367171 71767723488144794660050757)
      ·
        refine ⟨13456448154027148998759517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71767723488144794660050757 13456448154027148998759517)
        ·
          refine ⟨5046168057760180874534819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13456448154027148998759517 5046168057760180874534819)
          ·
            refine ⟨7569252086640271311802229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046168057760180874534819 7569252086640271311802229)
            ·
              refine ⟨709617383122525435481459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7569252086640271311802229 709617383122525435481459)
              ·
                refine ⟨1064426074683788153222189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709617383122525435481459 1064426074683788153222189)
                ·
                  refine ⟨399159778006420557458321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064426074683788153222189 399159778006420557458321)
                  ·
                    rfl

theorem cell20_874531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 3].length) (baseStart_874531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874531 prefixEnd_874531 := by exact prefixLift 874531
  have htrace : WordTrace (prefixWord ++ tailWord_874531) baseStart_874531 baseEnd_874531 := by
    simpa [prefixWord, tailWord_874531, baseEnd_874531] using wordTrace_append hprefix tailTrace_874531
  have hstable : (prefixWord ++ tailWord_874531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874531).length < 2 ^ (prefixWord ++ tailWord_874531).sum := by decide
  have hdescent : baseEnd_874531 < baseStart_874531 := by decide
  rcases family_descends (prefixWord ++ tailWord_874531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874538 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_874538 : Nat := 118140960795 + 874538 * 2 ^ 59
def prefixEnd_874538 : Nat := 4983230072969 + 3 ^ 40 * 874538 * 2
def baseEnd_874538 : Nat := 399162972997159644224959

theorem tailTrace_874538 : CollatzResearch.WordTrace tailWord_874538 prefixEnd_874538 399162972997159644224959 := by
  unfold tailWord_874538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7974255326426415011104067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21264680870470440029610845 7974255326426415011104067)
  ·
    refine ⟨11961382989639622516656101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7974255326426415011104067 11961382989639622516656101)
    ·
      refine ⟨2242759310557429221873019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11961382989639622516656101 2242759310557429221873019)
      ·
        refine ⟨3364138965836143832809529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242759310557429221873019 3364138965836143832809529)
        ·
          refine ⟨2523104224377107874607147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3364138965836143832809529 2523104224377107874607147)
          ·
            refine ⟨3784656336565661811910721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523104224377107874607147 3784656336565661811910721)
            ·
              refine ⟨2838492252424246358933041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3784656336565661811910721 2838492252424246358933041)
              ·
                refine ⟨2128869189318184769199781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2838492252424246358933041 2128869189318184769199781)
                ·
                  refine ⟨399162972997159644224959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128869189318184769199781 399162972997159644224959)
                  ·
                    rfl

theorem cell20_874538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_874538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874538 prefixEnd_874538 := by exact prefixLift 874538
  have htrace : WordTrace (prefixWord ++ tailWord_874538) baseStart_874538 baseEnd_874538 := by
    simpa [prefixWord, tailWord_874538, baseEnd_874538] using wordTrace_append hprefix tailTrace_874538
  have hstable : (prefixWord ++ tailWord_874538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874538).length < 2 ^ (prefixWord ++ tailWord_874538).sum := by decide
  have hdescent : baseEnd_874538 < baseStart_874538 := by decide
  rcases family_descends (prefixWord ++ tailWord_874538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874545 : List Nat := [1, 2, 2, 3, 1, 3, 4, 4]
def baseStart_874545 : Nat := 118140960795 + 874545 * 2 ^ 59
def prefixEnd_874545 : Nat := 4983230072969 + 3 ^ 40 * 874545 * 2
def baseEnd_874545 : Nat := 133055389329299576997199

theorem tailTrace_874545 : CollatzResearch.WordTrace tailWord_874545 prefixEnd_874545 133055389329299576997199 := by
  unfold tailWord_874545
  simp only [CollatzResearch.WordTrace]
  refine ⟨31897276616680300239921089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21264851077786866826614059 31897276616680300239921089)
  ·
    refine ⟨23922957462510225179940817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31897276616680300239921089 23922957462510225179940817)
    ·
      refine ⟨17942218096882668884955613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23922957462510225179940817 17942218096882668884955613)
      ·
        refine ⟨6728331786331000831858355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17942218096882668884955613 6728331786331000831858355)
        ·
          refine ⟨10092497679496501247787533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728331786331000831858355 10092497679496501247787533)
          ·
            refine ⟨3784686629811187967920325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10092497679496501247787533 3784686629811187967920325)
            ·
              refine ⟨709628743089597743985061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3784686629811187967920325 709628743089597743985061)
              ·
                refine ⟨133055389329299576997199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709628743089597743985061 133055389329299576997199)
                ·
                  rfl

theorem cell20_874545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 4].length) (baseStart_874545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874545 prefixEnd_874545 := by exact prefixLift 874545
  have htrace : WordTrace (prefixWord ++ tailWord_874545) baseStart_874545 baseEnd_874545 := by
    simpa [prefixWord, tailWord_874545, baseEnd_874545] using wordTrace_append hprefix tailTrace_874545
  have hstable : (prefixWord ++ tailWord_874545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874545).length < 2 ^ (prefixWord ++ tailWord_874545).sum := by decide
  have hdescent : baseEnd_874545 < baseStart_874545 := by decide
  rcases family_descends (prefixWord ++ tailWord_874545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874582 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_874582 : Nat := 118140960795 + 874582 * 2 ^ 59
def prefixEnd_874582 : Nat := 4983230072969 + 3 ^ 40 * 874582 * 2
def baseEnd_874582 : Nat := 399183055796091046758113

theorem tailTrace_874582 : CollatzResearch.WordTrace tailWord_874582 prefixEnd_874582 399183055796091046758113 := by
  unfold tailWord_874582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993664132346640972438625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21265750745030837039345333 1993664132346640972438625)
  ·
    refine ⟨1495248099259980729328969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1993664132346640972438625 1495248099259980729328969)
    ·
      refine ⟨1121436074444985546996727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1495248099259980729328969 1121436074444985546996727)
      ·
        refine ⟨1682154111667478320495091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121436074444985546996727 1682154111667478320495091)
        ·
          refine ⟨2523231167501217480742637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682154111667478320495091 2523231167501217480742637)
          ·
            refine ⟨946211687812956555278489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2523231167501217480742637 946211687812956555278489)
            ·
              refine ⟨709658765859717416458867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946211687812956555278489 709658765859717416458867)
              ·
                refine ⟨1064488148789576124688301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709658765859717416458867 1064488148789576124688301)
                ·
                  refine ⟨399183055796091046758113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064488148789576124688301 399183055796091046758113)
                  ·
                    rfl

theorem cell20_874582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_874582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874582 prefixEnd_874582 := by exact prefixLift 874582
  have htrace : WordTrace (prefixWord ++ tailWord_874582) baseStart_874582 baseEnd_874582 := by
    simpa [prefixWord, tailWord_874582, baseEnd_874582] using wordTrace_append hprefix tailTrace_874582
  have hstable : (prefixWord ++ tailWord_874582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874582).length < 2 ^ (prefixWord ++ tailWord_874582).sum := by decide
  have hdescent : baseEnd_874582 < baseStart_874582 := by decide
  rcases family_descends (prefixWord ++ tailWord_874582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874604 : List Nat := [2, 2, 1, 1, 3, 3, 2, 6]
def baseStart_874604 : Nat := 118140960795 + 874604 * 2 ^ 59
def prefixEnd_874604 : Nat := 4983230072969 + 3 ^ 40 * 874604 * 2
def baseEnd_874604 : Nat := 133064365731852249341563

theorem tailTrace_874604 : CollatzResearch.WordTrace tailWord_874604 prefixEnd_874604 133064365731852249341563 := by
  unfold tailWord_874604
  simp only [CollatzResearch.WordTrace]
  refine ⟨15949714261733276658159433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21266285682311035544212577 15949714261733276658159433)
  ·
    refine ⟨11962285696299957493619575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15949714261733276658159433 11962285696299957493619575)
    ·
      refine ⟨17943428544449936240429363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11962285696299957493619575 17943428544449936240429363)
      ·
        refine ⟨26915142816674904360644045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17943428544449936240429363 26915142816674904360644045)
        ·
          refine ⟨10093178556253089135241517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26915142816674904360644045 10093178556253089135241517)
          ·
            refine ⟨3784941958594908425715569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10093178556253089135241517 3784941958594908425715569)
            ·
              refine ⟨2838706468946181319286677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3784941958594908425715569 2838706468946181319286677)
              ·
                refine ⟨133064365731852249341563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2838706468946181319286677 133064365731852249341563)
                ·
                  rfl

theorem cell20_874604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_874604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874604 prefixEnd_874604 := by exact prefixLift 874604
  have htrace : WordTrace (prefixWord ++ tailWord_874604) baseStart_874604 baseEnd_874604 := by
    simpa [prefixWord, tailWord_874604, baseEnd_874604] using wordTrace_append hprefix tailTrace_874604
  have hstable : (prefixWord ++ tailWord_874604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874604).length < 2 ^ (prefixWord ++ tailWord_874604).sum := by decide
  have hdescent : baseEnd_874604 < baseStart_874604 := by decide
  rcases family_descends (prefixWord ++ tailWord_874604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874631 : List Nat := [1, 1, 4, 2, 1, 1, 6, 2, 2]
def baseStart_874631 : Nat := 118140960795 + 874631 * 2 ^ 59
def prefixEnd_874631 : Nat := 4983230072969 + 3 ^ 40 * 874631 * 2
def baseEnd_874631 : Nat := 399205420731264654124579

theorem tailTrace_874631 : CollatzResearch.WordTrace tailWord_874631 prefixEnd_874631 399205420731264654124579 := by
  unfold tailWord_874631
  simp only [CollatzResearch.WordTrace]
  refine ⟨31900413294368736927551747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21266942196245824618367831 31900413294368736927551747)
  ·
    refine ⟨47850619941553105391327621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31900413294368736927551747 47850619941553105391327621)
    ·
      refine ⟨8971991239041207260873929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47850619941553105391327621 8971991239041207260873929)
      ·
        refine ⟨6728993429280905445655447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8971991239041207260873929 6728993429280905445655447)
        ·
          refine ⟨10093490143921358168483171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728993429280905445655447 10093490143921358168483171)
          ·
            refine ⟨15140235215882037252724757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10093490143921358168483171 15140235215882037252724757)
            ·
              refine ⟨709698525744470496221473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15140235215882037252724757 709698525744470496221473)
              ·
                refine ⟨532273894308352872166105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709698525744470496221473 532273894308352872166105)
                ·
                  refine ⟨399205420731264654124579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532273894308352872166105 399205420731264654124579)
                  ·
                    rfl

theorem cell20_874631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 2].length) (baseStart_874631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874631 prefixEnd_874631 := by exact prefixLift 874631
  have htrace : WordTrace (prefixWord ++ tailWord_874631) baseStart_874631 baseEnd_874631 := by
    simpa [prefixWord, tailWord_874631, baseEnd_874631] using wordTrace_append hprefix tailTrace_874631
  have hstable : (prefixWord ++ tailWord_874631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874631).length < 2 ^ (prefixWord ++ tailWord_874631).sum := by decide
  have hdescent : baseEnd_874631 < baseStart_874631 := by decide
  rcases family_descends (prefixWord ++ tailWord_874631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874638 : List Nat := [4, 1, 1, 3, 3, 2, 1, 5]
def baseStart_874638 : Nat := 118140960795 + 874638 * 2 ^ 59
def prefixEnd_874638 : Nat := 4983230072969 + 3 ^ 40 * 874638 * 2
def baseEnd_874638 : Nat := 133069538574001246963739

theorem tailTrace_874638 : CollatzResearch.WordTrace tailWord_874638 prefixEnd_874638 133069538574001246963739 := by
  unfold tailWord_874638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987583575667922140382071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21267112403562251415371045 3987583575667922140382071)
  ·
    refine ⟨5981375363501883210573107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3987583575667922140382071 5981375363501883210573107)
    ·
      refine ⟨8972063045252824815859661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5981375363501883210573107 8972063045252824815859661)
      ·
        refine ⟨3364523641969809305947373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8972063045252824815859661 3364523641969809305947373)
        ·
          refine ⟨1261696365738678489730265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3364523641969809305947373 1261696365738678489730265)
          ·
            refine ⟨946272274304008867297699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261696365738678489730265 946272274304008867297699)
            ·
              refine ⟨1419408411456013300946549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946272274304008867297699 1419408411456013300946549)
              ·
                refine ⟨133069538574001246963739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1419408411456013300946549 133069538574001246963739)
                ·
                  rfl

theorem cell20_874638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_874638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874638 prefixEnd_874638 := by exact prefixLift 874638
  have htrace : WordTrace (prefixWord ++ tailWord_874638) baseStart_874638 baseEnd_874638 := by
    simpa [prefixWord, tailWord_874638, baseEnd_874638] using wordTrace_append hprefix tailTrace_874638
  have hstable : (prefixWord ++ tailWord_874638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874638).length < 2 ^ (prefixWord ++ tailWord_874638).sum := by decide
  have hdescent : baseEnd_874638 < baseStart_874638 := by decide
  rcases family_descends (prefixWord ++ tailWord_874638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874669 : List Nat := [1, 5, 2, 1, 2, 1, 1, 5, 2]
def baseStart_874669 : Nat := 118140960795 + 874669 * 2 ^ 59
def prefixEnd_874669 : Nat := 4983230072969 + 3 ^ 40 * 874669 * 2
def baseEnd_874669 : Nat := 399222764966705410857757

theorem tailTrace_874669 : CollatzResearch.WordTrace tailWord_874669 prefixEnd_874669 399222764966705410857757 := by
  unfold tailWord_874669
  simp only [CollatzResearch.WordTrace]
  refine ⟨31901799268231069417435061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21267866178820712944956707 31901799268231069417435061)
  ·
    refine ⟨2990793681396662757884537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31901799268231069417435061 2990793681396662757884537)
    ·
      refine ⟨2243095261047497068413403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2990793681396662757884537 2243095261047497068413403)
      ·
        refine ⟨3364642891571245602620105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243095261047497068413403 3364642891571245602620105)
        ·
          refine ⟨2523482168678434201965079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3364642891571245602620105 2523482168678434201965079)
          ·
            refine ⟨3785223253017651302947619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523482168678434201965079 3785223253017651302947619)
            ·
              refine ⟨5677834879526476954421429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785223253017651302947619 5677834879526476954421429)
              ·
                refine ⟨532297019955607214477009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5677834879526476954421429 532297019955607214477009)
                ·
                  refine ⟨399222764966705410857757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532297019955607214477009 399222764966705410857757)
                  ·
                    rfl

theorem cell20_874669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_874669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874669 prefixEnd_874669 := by exact prefixLift 874669
  have htrace : WordTrace (prefixWord ++ tailWord_874669) baseStart_874669 baseEnd_874669 := by
    simpa [prefixWord, tailWord_874669, baseEnd_874669] using wordTrace_append hprefix tailTrace_874669
  have hstable : (prefixWord ++ tailWord_874669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874669).length < 2 ^ (prefixWord ++ tailWord_874669).sum := by decide
  have hdescent : baseEnd_874669 < baseStart_874669 := by decide
  rcases family_descends (prefixWord ++ tailWord_874669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874742 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_874742 : Nat := 118140960795 + 874742 * 2 ^ 59
def prefixEnd_874742 : Nat := 4983230072969 + 3 ^ 40 * 874742 * 2
def baseEnd_874742 : Nat := 399256084155841601424125

theorem tailTrace_874742 : CollatzResearch.WordTrace tailWord_874742 prefixEnd_874742 399256084155841601424125 := by
  unfold tailWord_874742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994028862310412680302655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21269641197977735256561653 1994028862310412680302655)
  ·
    refine ⟨2991043293465619020453983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1994028862310412680302655 2991043293465619020453983)
    ·
      refine ⟨4486564940198428530680975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991043293465619020453983 4486564940198428530680975)
      ·
        refine ⟨6729847410297642796021463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486564940198428530680975 6729847410297642796021463)
        ·
          refine ⟨10094771115446464194032195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6729847410297642796021463 10094771115446464194032195)
          ·
            refine ⟨15142156673169696291048293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10094771115446464194032195 15142156673169696291048293)
            ·
              refine ⟨2839154376219318054571555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15142156673169696291048293 2839154376219318054571555)
              ·
                refine ⟨4258731564328977081857333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839154376219318054571555 4258731564328977081857333)
                ·
                  refine ⟨399256084155841601424125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4258731564328977081857333 399256084155841601424125)
                  ·
                    rfl

theorem cell20_874742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_874742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874742 prefixEnd_874742 := by exact prefixLift 874742
  have htrace : WordTrace (prefixWord ++ tailWord_874742) baseStart_874742 baseEnd_874742 := by
    simpa [prefixWord, tailWord_874742, baseEnd_874742] using wordTrace_append hprefix tailTrace_874742
  have hstable : (prefixWord ++ tailWord_874742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874742).length < 2 ^ (prefixWord ++ tailWord_874742).sum := by decide
  have hdescent : baseEnd_874742 < baseStart_874742 := by decide
  rcases family_descends (prefixWord ++ tailWord_874742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874794 : List Nat := [3, 1, 4, 2, 10]
def baseStart_874794 : Nat := 118140960795 + 874794 * 2 ^ 59
def prefixEnd_874794 : Nat := 4983230072969 + 3 ^ 40 * 874794 * 2
def baseEnd_874794 : Nat := 4929380473737784341859

theorem tailTrace_874794 : CollatzResearch.WordTrace tailWord_874794 prefixEnd_874794 4929380473737784341859 := by
  unfold tailWord_874794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976589598194553941433859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21270905595185477177156957 7976589598194553941433859)
  ·
    refine ⟨11964884397291830912150789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7976589598194553941433859 11964884397291830912150789)
    ·
      refine ⟨2243415824492218296028273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11964884397291830912150789 2243415824492218296028273)
      ·
        refine ⟨1682561868369163722021205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2243415824492218296028273 1682561868369163722021205)
        ·
          refine ⟨4929380473737784341859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1682561868369163722021205 4929380473737784341859)
          ·
            rfl

theorem cell20_874794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 10].length) (baseStart_874794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874794 prefixEnd_874794 := by exact prefixLift 874794
  have htrace : WordTrace (prefixWord ++ tailWord_874794) baseStart_874794 baseEnd_874794 := by
    simpa [prefixWord, tailWord_874794, baseEnd_874794] using wordTrace_append hprefix tailTrace_874794
  have hstable : (prefixWord ++ tailWord_874794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874794).length < 2 ^ (prefixWord ++ tailWord_874794).sum := by decide
  have hdescent : baseEnd_874794 < baseStart_874794 := by decide
  rcases family_descends (prefixWord ++ tailWord_874794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874839 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_874839 : Nat := 118140960795 + 874839 * 2 ^ 59
def prefixEnd_874839 : Nat := 4983230072969 + 3 ^ 40 * 874839 * 2
def baseEnd_874839 : Nat := 399300357598940375190395

theorem tailTrace_874839 : CollatzResearch.WordTrace tailWord_874839 prefixEnd_874839 399300357598940375190395 := by
  unfold tailWord_874839
  simp only [CollatzResearch.WordTrace]
  refine ⟨31907999677615188451123571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21271999785076792300749047 31907999677615188451123571)
  ·
    refine ⟨47861999516422782676685357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31907999677615188451123571 47861999516422782676685357)
    ·
      refine ⟨17948249818658543503757009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47861999516422782676685357 17948249818658543503757009)
      ·
        refine ⟨13461187363993907627817757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17948249818658543503757009 13461187363993907627817757)
        ·
          refine ⟨5047945261497715360431659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13461187363993907627817757 5047945261497715360431659)
          ·
            refine ⟨7571917892246573040647489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047945261497715360431659 7571917892246573040647489)
            ·
              refine ⟨5678938419184929780485617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7571917892246573040647489 5678938419184929780485617)
              ·
                refine ⟨4259203814388697335364213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678938419184929780485617 4259203814388697335364213)
                ·
                  refine ⟨399300357598940375190395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4259203814388697335364213 399300357598940375190395)
                  ·
                    rfl

theorem cell20_874839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_874839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874839 prefixEnd_874839 := by exact prefixLift 874839
  have htrace : WordTrace (prefixWord ++ tailWord_874839) baseStart_874839 baseEnd_874839 := by
    simpa [prefixWord, tailWord_874839, baseEnd_874839] using wordTrace_append hprefix tailTrace_874839
  have hstable : (prefixWord ++ tailWord_874839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874839).length < 2 ^ (prefixWord ++ tailWord_874839).sum := by decide
  have hdescent : baseEnd_874839 < baseStart_874839 := by decide
  rcases family_descends (prefixWord ++ tailWord_874839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874856 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_874856 : Nat := 118140960795 + 874856 * 2 ^ 59
def prefixEnd_874856 : Nat := 4983230072969 + 3 ^ 40 * 874856 * 2
def baseEnd_874856 : Nat := 399308116862163871623659

theorem tailTrace_874856 : CollatzResearch.WordTrace tailWord_874856 prefixEnd_874856 399308116862163871623659 := by
  unfold tailWord_874856
  simp only [CollatzResearch.WordTrace]
  refine ⟨15954309859276800177246211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21272413145702400236328281 15954309859276800177246211)
  ·
    refine ⟨23931464788915200265869317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15954309859276800177246211 23931464788915200265869317)
    ·
      refine ⟨4487149647921600049850497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23931464788915200265869317 4487149647921600049850497)
      ·
        refine ⟨3365362235941200037387873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4487149647921600049850497 3365362235941200037387873)
        ·
          refine ⟨2524021676955900028040905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3365362235941200037387873 2524021676955900028040905)
          ·
            refine ⟨1893016257716925021030679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2524021676955900028040905 1893016257716925021030679)
            ·
              refine ⟨2839524386575387531546019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893016257716925021030679 2839524386575387531546019)
              ·
                refine ⟨4259286579863081297319029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839524386575387531546019 4259286579863081297319029)
                ·
                  refine ⟨399308116862163871623659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4259286579863081297319029 399308116862163871623659)
                  ·
                    rfl

theorem cell20_874856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_874856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874856 prefixEnd_874856 := by exact prefixLift 874856
  have htrace : WordTrace (prefixWord ++ tailWord_874856) baseStart_874856 baseEnd_874856 := by
    simpa [prefixWord, tailWord_874856, baseEnd_874856] using wordTrace_append hprefix tailTrace_874856
  have hstable : (prefixWord ++ tailWord_874856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874856).length < 2 ^ (prefixWord ++ tailWord_874856).sum := by decide
  have hdescent : baseEnd_874856 < baseStart_874856 := by decide
  rcases family_descends (prefixWord ++ tailWord_874856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874894 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_874894 : Nat := 118140960795 + 874894 * 2 ^ 59
def prefixEnd_874894 : Nat := 4983230072969 + 3 ^ 40 * 874894 * 2
def baseEnd_874894 : Nat := 399325461097604628356837

theorem tailTrace_874894 : CollatzResearch.WordTrace tailWord_874894 prefixEnd_874894 399325461097604628356837 := by
  unfold tailWord_874894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988750711551991605546967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21273337128277288562917157 3988750711551991605546967)
  ·
    refine ⟨5983126067327987408320451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3988750711551991605546967 5983126067327987408320451)
    ·
      refine ⟨8974689100991981112480677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5983126067327987408320451 8974689100991981112480677)
      ·
        refine ⟨1682754206435996458590127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8974689100991981112480677 1682754206435996458590127)
        ·
          refine ⟨2524131309653994687885191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682754206435996458590127 2524131309653994687885191)
          ·
            refine ⟨3786196964480992031827787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524131309653994687885191 3786196964480992031827787)
            ·
              refine ⟨5679295446721488047741681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786196964480992031827787 5679295446721488047741681)
              ·
                refine ⟨4259471585041116035806261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5679295446721488047741681 4259471585041116035806261)
                ·
                  refine ⟨399325461097604628356837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4259471585041116035806261 399325461097604628356837)
                  ·
                    rfl

theorem cell20_874894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_874894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874894 prefixEnd_874894 := by exact prefixLift 874894
  have htrace : WordTrace (prefixWord ++ tailWord_874894) baseStart_874894 baseEnd_874894 := by
    simpa [prefixWord, tailWord_874894, baseEnd_874894] using wordTrace_append hprefix tailTrace_874894
  have hstable : (prefixWord ++ tailWord_874894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874894).length < 2 ^ (prefixWord ++ tailWord_874894).sum := by decide
  have hdescent : baseEnd_874894 < baseStart_874894 := by decide
  rcases family_descends (prefixWord ++ tailWord_874894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874915 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_874915 : Nat := 118140960795 + 874915 * 2 ^ 59
def prefixEnd_874915 : Nat := 4983230072969 + 3 ^ 40 * 874915 * 2
def baseEnd_874915 : Nat := 399335046069821888656751

theorem tailTrace_874915 : CollatzResearch.WordTrace tailWord_874915 prefixEnd_874915 399335046069821888656751 := by
  unfold tailWord_874915
  simp only [CollatzResearch.WordTrace]
  refine ⟨31910771625339853430890199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21273847750226568953926799 31910771625339853430890199)
  ·
    refine ⟨47866157438009780146335299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31910771625339853430890199 47866157438009780146335299)
    ·
      refine ⟨71799236157014670219502949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47866157438009780146335299 71799236157014670219502949)
      ·
        refine ⟨13462356779440250666156803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71799236157014670219502949 13462356779440250666156803)
        ·
          refine ⟨20193535169160375999235205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13462356779440250666156803 20193535169160375999235205)
          ·
            refine ⟨3786287844217570499856601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20193535169160375999235205 3786287844217570499856601)
            ·
              refine ⟨2839715883163177874892451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3786287844217570499856601 2839715883163177874892451)
              ·
                refine ⟨4259573824744766812338677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839715883163177874892451 4259573824744766812338677)
                ·
                  refine ⟨399335046069821888656751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4259573824744766812338677 399335046069821888656751)
                  ·
                    rfl

theorem cell20_874915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_874915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874915 prefixEnd_874915 := by exact prefixLift 874915
  have htrace : WordTrace (prefixWord ++ tailWord_874915) baseStart_874915 baseEnd_874915 := by
    simpa [prefixWord, tailWord_874915, baseEnd_874915] using wordTrace_append hprefix tailTrace_874915
  have hstable : (prefixWord ++ tailWord_874915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874915).length < 2 ^ (prefixWord ++ tailWord_874915).sum := by decide
  have hdescent : baseEnd_874915 < baseStart_874915 := by decide
  rcases family_descends (prefixWord ++ tailWord_874915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874970 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_874970 : Nat := 118140960795 + 874970 * 2 ^ 59
def prefixEnd_874970 : Nat := 4983230072969 + 3 ^ 40 * 874970 * 2
def baseEnd_874970 : Nat := 399360149568486141823193

theorem tailTrace_874970 : CollatzResearch.WordTrace tailWord_874970 prefixEnd_874970 399360149568486141823193 := by
  unfold tailWord_874970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7978194410035149456035591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21275185093427065216094909 7978194410035149456035591)
  ·
    refine ⟨11967291615052724184053387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7978194410035149456035591 11967291615052724184053387)
    ·
      refine ⟨17950937422579086276080081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11967291615052724184053387 17950937422579086276080081)
      ·
        refine ⟨13463203066934314707060061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17950937422579086276080081 13463203066934314707060061)
        ·
          refine ⟨5048701150100368015147523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13463203066934314707060061 5048701150100368015147523)
          ·
            refine ⟨7573051725150552022721285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048701150100368015147523 7573051725150552022721285)
            ·
              refine ⟨1419947198465728504260241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7573051725150552022721285 1419947198465728504260241)
              ·
                refine ⟨1064960398849296378195181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419947198465728504260241 1064960398849296378195181)
                ·
                  refine ⟨399360149568486141823193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064960398849296378195181 399360149568486141823193)
                  ·
                    rfl

theorem cell20_874970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_874970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874970 prefixEnd_874970 := by exact prefixLift 874970
  have htrace : WordTrace (prefixWord ++ tailWord_874970) baseStart_874970 baseEnd_874970 := by
    simpa [prefixWord, tailWord_874970, baseEnd_874970] using wordTrace_append hprefix tailTrace_874970
  have hstable : (prefixWord ++ tailWord_874970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874970).length < 2 ^ (prefixWord ++ tailWord_874970).sum := by decide
  have hdescent : baseEnd_874970 < baseStart_874970 := by decide
  rcases family_descends (prefixWord ++ tailWord_874970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874984 : List Nat := [2, 1, 4, 1, 1, 3, 3, 5]
def baseStart_874984 : Nat := 118140960795 + 874984 * 2 ^ 59
def prefixEnd_874984 : Nat := 4983230072969 + 3 ^ 40 * 874984 * 2
def baseEnd_874984 : Nat := 133122179849988105118823

theorem tailTrace_874984 : CollatzResearch.WordTrace tailWord_874984 prefixEnd_874984 133122179849988105118823 := by
  unfold tailWord_874984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15956644131044939107576003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21275525508059918810101337 15956644131044939107576003)
  ·
    refine ⟨23934966196567408661364005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15956644131044939107576003 23934966196567408661364005)
    ·
      refine ⟨4487806161856389124005751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23934966196567408661364005 4487806161856389124005751)
      ·
        refine ⟨6731709242784583686008627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4487806161856389124005751 6731709242784583686008627)
        ·
          refine ⟨10097563864176875529012941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6731709242784583686008627 10097563864176875529012941)
          ·
            refine ⟨3786586449066328323379853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10097563864176875529012941 3786586449066328323379853)
            ·
              refine ⟨1419969918399873121267445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3786586449066328323379853 1419969918399873121267445)
              ·
                refine ⟨133122179849988105118823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1419969918399873121267445 133122179849988105118823)
                ·
                  rfl

theorem cell20_874984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_874984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874984 prefixEnd_874984 := by exact prefixLift 874984
  have htrace : WordTrace (prefixWord ++ tailWord_874984) baseStart_874984 baseEnd_874984 := by
    simpa [prefixWord, tailWord_874984, baseEnd_874984] using wordTrace_append hprefix tailTrace_874984
  have hstable : (prefixWord ++ tailWord_874984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874984).length < 2 ^ (prefixWord ++ tailWord_874984).sum := by decide
  have hdescent : baseEnd_874984 < baseStart_874984 := by decide
  rcases family_descends (prefixWord ++ tailWord_874984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874994 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_874994 : Nat := 118140960795 + 874994 * 2 ^ 59
def prefixEnd_874994 : Nat := 4983230072969 + 3 ^ 40 * 874994 * 2
def baseEnd_874994 : Nat := 399371103822448725023095

theorem tailTrace_874994 : CollatzResearch.WordTrace tailWord_874994 prefixEnd_874994 399371103822448725023095 := by
  unfold tailWord_874994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7978413248013412480754009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21275768661369099948677357 7978413248013412480754009)
  ·
    refine ⟨5983809936010059360565507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7978413248013412480754009 5983809936010059360565507)
    ·
      refine ⟨8975714904015089040848261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5983809936010059360565507 8975714904015089040848261)
      ·
        refine ⟨1682946544502829195159049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8975714904015089040848261 1682946544502829195159049)
        ·
          refine ⟨1262209908377121896369287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1682946544502829195159049 1262209908377121896369287)
          ·
            refine ⟨1893314862565682844553931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262209908377121896369287 1893314862565682844553931)
            ·
              refine ⟨2839972293848524266830897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893314862565682844553931 2839972293848524266830897)
              ·
                refine ⟨2129979220386393200123173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2839972293848524266830897 2129979220386393200123173)
                ·
                  refine ⟨399371103822448725023095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2129979220386393200123173 399371103822448725023095)
                  ·
                    rfl

theorem cell20_874994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_874994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_874994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_874994 prefixEnd_874994 := by exact prefixLift 874994
  have htrace : WordTrace (prefixWord ++ tailWord_874994) baseStart_874994 baseEnd_874994 := by
    simpa [prefixWord, tailWord_874994, baseEnd_874994] using wordTrace_append hprefix tailTrace_874994
  have hstable : (prefixWord ++ tailWord_874994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874994).length < 2 ^ (prefixWord ++ tailWord_874994).sum := by decide
  have hdescent : baseEnd_874994 < baseStart_874994 := by decide
  rcases family_descends (prefixWord ++ tailWord_874994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875021 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 3]
def baseStart_875021 : Nat := 118140960795 + 875021 * 2 ^ 59
def prefixEnd_875021 : Nat := 4983230072969 + 3 ^ 40 * 875021 * 2
def baseEnd_875021 : Nat := 399383427358156631122985

theorem tailTrace_875021 : CollatzResearch.WordTrace tailWord_875021 prefixEnd_875021 399383427358156631122985 := by
  unfold tailWord_875021
  simp only [CollatzResearch.WordTrace]
  refine ⟨31914637762955833534248917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21276425175303889022832611 31914637762955833534248917)
  ·
    refine ⟨747999322569277348458959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31914637762955833534248917 747999322569277348458959)
    ·
      refine ⟨1121998983853916022688439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747999322569277348458959 1121998983853916022688439)
      ·
        refine ⟨1682998475780874034032659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121998983853916022688439 1682998475780874034032659)
        ·
          refine ⟨2524497713671311051048989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682998475780874034032659 2524497713671311051048989)
          ·
            refine ⟨946686642626741644143371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2524497713671311051048989 946686642626741644143371)
            ·
              refine ⟨1420029963940112466215057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946686642626741644143371 1420029963940112466215057)
              ·
                refine ⟨1065022472955084349661293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420029963940112466215057 1065022472955084349661293)
                ·
                  refine ⟨399383427358156631122985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065022472955084349661293 399383427358156631122985)
                  ·
                    rfl

theorem cell20_875021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_875021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875021 prefixEnd_875021 := by exact prefixLift 875021
  have htrace : WordTrace (prefixWord ++ tailWord_875021) baseStart_875021 baseEnd_875021 := by
    simpa [prefixWord, tailWord_875021, baseEnd_875021] using wordTrace_append hprefix tailTrace_875021
  have hstable : (prefixWord ++ tailWord_875021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875021).length < 2 ^ (prefixWord ++ tailWord_875021).sum := by decide
  have hdescent : baseEnd_875021 < baseStart_875021 := by decide
  rcases family_descends (prefixWord ++ tailWord_875021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875022 : List Nat := [4, 1, 1, 2, 3, 2, 7]
def baseStart_875022 : Nat := 118140960795 + 875022 * 2 ^ 59
def prefixEnd_875022 : Nat := 4983230072969 + 3 ^ 40 * 875022 * 2
def baseEnd_875022 : Nat := 44375987087267230232183

theorem tailTrace_875022 : CollatzResearch.WordTrace tailWord_875022 prefixEnd_875022 44375987087267230232183 := by
  unfold tailWord_875022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989334279494026338129415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21276449490634807136690213 3989334279494026338129415)
  ·
    refine ⟨5984001419241039507194123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3989334279494026338129415 5984001419241039507194123)
    ·
      refine ⟨8976002128861559260791185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5984001419241039507194123 8976002128861559260791185)
      ·
        refine ⟨6732001596646169445593389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8976002128861559260791185 6732001596646169445593389)
        ·
          refine ⟨2524500598742313542097521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6732001596646169445593389 2524500598742313542097521)
          ·
            refine ⟨1893375449056735156573141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2524500598742313542097521 1893375449056735156573141)
            ·
              refine ⟨44375987087267230232183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1893375449056735156573141 44375987087267230232183)
              ·
                rfl

theorem cell20_875022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 7].length) (baseStart_875022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875022 prefixEnd_875022 := by exact prefixLift 875022
  have htrace : WordTrace (prefixWord ++ tailWord_875022) baseStart_875022 baseEnd_875022 := by
    simpa [prefixWord, tailWord_875022, baseEnd_875022] using wordTrace_append hprefix tailTrace_875022
  have hstable : (prefixWord ++ tailWord_875022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875022).length < 2 ^ (prefixWord ++ tailWord_875022).sum := by decide
  have hdescent : baseEnd_875022 < baseStart_875022 := by decide
  rcases family_descends (prefixWord ++ tailWord_875022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875029 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_875029 : Nat := 118140960795 + 875029 * 2 ^ 59
def prefixEnd_875029 : Nat := 4983230072969 + 3 ^ 40 * 875029 * 2
def baseEnd_875029 : Nat := 399387078776144158856285

theorem tailTrace_875029 : CollatzResearch.WordTrace tailWord_875029 prefixEnd_875029 399387078776144158856285 := by
  unfold tailWord_875029
  simp only [CollatzResearch.WordTrace]
  refine ⟨31914929546926850900540141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21276619697951233933693427 31914929546926850900540141)
  ·
    refine ⟨11968098580097569087702553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31914929546926850900540141 11968098580097569087702553)
    ·
      refine ⟨8976073935073176815776915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11968098580097569087702553 8976073935073176815776915)
      ·
        refine ⟨13464110902609765223665373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8976073935073176815776915 13464110902609765223665373)
        ·
          refine ⟨5049041588478661958874515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13464110902609765223665373 5049041588478661958874515)
          ·
            refine ⟨7573562382717992938311773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049041588478661958874515 7573562382717992938311773)
            ·
              refine ⟨2840085893519247351866915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7573562382717992938311773 2840085893519247351866915)
              ·
                refine ⟨4260128840278871027800373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840085893519247351866915 4260128840278871027800373)
                ·
                  refine ⟨399387078776144158856285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4260128840278871027800373 399387078776144158856285)
                  ·
                    rfl

theorem cell20_875029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_875029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875029 prefixEnd_875029 := by exact prefixLift 875029
  have htrace : WordTrace (prefixWord ++ tailWord_875029) baseStart_875029 baseEnd_875029 := by
    simpa [prefixWord, tailWord_875029, baseEnd_875029] using wordTrace_append hprefix tailTrace_875029
  have hstable : (prefixWord ++ tailWord_875029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875029).length < 2 ^ (prefixWord ++ tailWord_875029).sum := by decide
  have hdescent : baseEnd_875029 < baseStart_875029 := by decide
  rcases family_descends (prefixWord ++ tailWord_875029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875032 : List Nat := [2, 1, 2, 3, 3, 1, 2, 4, 2]
def baseStart_875032 : Nat := 118140960795 + 875032 * 2 ^ 59
def prefixEnd_875032 : Nat := 4983230072969 + 3 ^ 40 * 875032 * 2
def baseEnd_875032 : Nat := 399388448057889481756273

theorem tailTrace_875032 : CollatzResearch.WordTrace tailWord_875032 prefixEnd_875032 399388448057889481756273 := by
  unfold tailWord_875032
  simp only [CollatzResearch.WordTrace]
  refine ⟨15957519482957991206449675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21276692643943988275266233 15957519482957991206449675)
  ·
    refine ⟨23936279224436986809674513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15957519482957991206449675 23936279224436986809674513)
    ·
      refine ⟨17952209418327740107255885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23936279224436986809674513 17952209418327740107255885)
      ·
        refine ⟨6732078531872902540220957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17952209418327740107255885 6732078531872902540220957)
        ·
          refine ⟨2524529449452338452582859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6732078531872902540220957 2524529449452338452582859)
          ·
            refine ⟨3786794174178507678874289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524529449452338452582859 3786794174178507678874289)
            ·
              refine ⟨2840095630633880759155717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3786794174178507678874289 2840095630633880759155717)
              ·
                refine ⟨532517930743852642341697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2840095630633880759155717 532517930743852642341697)
                ·
                  refine ⟨399388448057889481756273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532517930743852642341697 399388448057889481756273)
                  ·
                    rfl

theorem cell20_875032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_875032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875032 prefixEnd_875032 := by exact prefixLift 875032
  have htrace : WordTrace (prefixWord ++ tailWord_875032) baseStart_875032 baseEnd_875032 := by
    simpa [prefixWord, tailWord_875032, baseEnd_875032] using wordTrace_append hprefix tailTrace_875032
  have hstable : (prefixWord ++ tailWord_875032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875032).length < 2 ^ (prefixWord ++ tailWord_875032).sum := by decide
  have hdescent : baseEnd_875032 < baseStart_875032 := by decide
  rcases family_descends (prefixWord ++ tailWord_875032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875119 : List Nat := [1, 1, 2, 1, 3, 2, 4, 6]
def baseStart_875119 : Nat := 118140960795 + 875119 * 2 ^ 59
def prefixEnd_875119 : Nat := 4983230072969 + 3 ^ 40 * 875119 * 2
def baseEnd_875119 : Nat := 133142719076167948618639

theorem tailTrace_875119 : CollatzResearch.WordTrace tailWord_875119 prefixEnd_875119 133142719076167948618639 := by
  unfold tailWord_875119
  simp only [CollatzResearch.WordTrace]
  refine ⟨31918212116600796271316411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21278808077733864180877607 31918212116600796271316411)
  ·
    refine ⟨47877318174901194406974617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31918212116600796271316411 47877318174901194406974617)
    ·
      refine ⟨35907988631175895805230963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47877318174901194406974617 35907988631175895805230963)
      ·
        refine ⟨53861982946763843707846445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35907988631175895805230963 53861982946763843707846445)
        ·
          refine ⟨20198243605036441390442417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53861982946763843707846445 20198243605036441390442417)
          ·
            refine ⟨15148682703777331042831813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20198243605036441390442417 15148682703777331042831813)
            ·
              refine ⟨2840378006958249570530965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15148682703777331042831813 2840378006958249570530965)
              ·
                refine ⟨133142719076167948618639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2840378006958249570530965 133142719076167948618639)
                ·
                  rfl

theorem cell20_875119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_875119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875119 prefixEnd_875119 := by exact prefixLift 875119
  have htrace : WordTrace (prefixWord ++ tailWord_875119) baseStart_875119 baseEnd_875119 := by
    simpa [prefixWord, tailWord_875119, baseEnd_875119] using wordTrace_append hprefix tailTrace_875119
  have hstable : (prefixWord ++ tailWord_875119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875119).length < 2 ^ (prefixWord ++ tailWord_875119).sum := by decide
  have hdescent : baseEnd_875119 < baseStart_875119 := by decide
  rcases family_descends (prefixWord ++ tailWord_875119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875201 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 4]
def baseStart_875201 : Nat := 118140960795 + 875201 * 2 ^ 59
def prefixEnd_875201 : Nat := 4983230072969 + 3 ^ 40 * 875201 * 2
def baseEnd_875201 : Nat := 399465584262876005122249

theorem tailTrace_875201 : CollatzResearch.WordTrace tailWord_875201 prefixEnd_875201 399465584262876005122249 := by
  unfold tailWord_875201
  simp only [CollatzResearch.WordTrace]
  refine ⟨31921202902303724275801457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21280801934869149517200971 31921202902303724275801457)
  ·
    refine ⟨23940902176727793206851093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31921202902303724275801457 23940902176727793206851093)
    ·
      refine ⟨1122229789534115306571145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23940902176727793206851093 1122229789534115306571145)
      ·
        refine ⟨841672342150586479928359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1122229789534115306571145 841672342150586479928359)
        ·
          refine ⟨1262508513225879719892539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841672342150586479928359 1262508513225879719892539)
          ·
            refine ⟨1893762769838819579838809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262508513225879719892539 1893762769838819579838809)
            ·
              refine ⟨1420322077379114684879107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1893762769838819579838809 1420322077379114684879107)
              ·
                refine ⟨2130483116068672027318661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420322077379114684879107 2130483116068672027318661)
                ·
                  refine ⟨399465584262876005122249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130483116068672027318661 399465584262876005122249)
                  ·
                    rfl

theorem cell20_875201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_875201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875201 prefixEnd_875201 := by exact prefixLift 875201
  have htrace : WordTrace (prefixWord ++ tailWord_875201) baseStart_875201 baseEnd_875201 := by
    simpa [prefixWord, tailWord_875201, baseEnd_875201] using wordTrace_append hprefix tailTrace_875201
  have hstable : (prefixWord ++ tailWord_875201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875201).length < 2 ^ (prefixWord ++ tailWord_875201).sum := by decide
  have hdescent : baseEnd_875201 < baseStart_875201 := by decide
  rcases family_descends (prefixWord ++ tailWord_875201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875226 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_875226 : Nat := 118140960795 + 875226 * 2 ^ 59
def prefixEnd_875226 : Nat := 4983230072969 + 3 ^ 40 * 875226 * 2
def baseEnd_875226 : Nat := 399476994944087029288813

theorem tailTrace_875226 : CollatzResearch.WordTrace tailWord_875226 prefixEnd_875226 399476994944087029288813 := by
  unfold tailWord_875226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7980528681803288386365383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21281409818142102363641021 7980528681803288386365383)
  ·
    refine ⟨11970793022704932579548075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7980528681803288386365383 11970793022704932579548075)
    ·
      refine ⟨17956189534057398869322113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11970793022704932579548075 17956189534057398869322113)
      ·
        refine ⟨13467142150543049151991585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17956189534057398869322113 13467142150543049151991585)
        ·
          refine ⟨10100356612907286863993689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13467142150543049151991585 10100356612907286863993689)
          ·
            refine ⟨7575267459680465147995267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10100356612907286863993689 7575267459680465147995267)
            ·
              refine ⟨11362901189520697721992901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575267459680465147995267 11362901189520697721992901)
              ·
                refine ⟨2130543973035130822873669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11362901189520697721992901 2130543973035130822873669)
                ·
                  refine ⟨399476994944087029288813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130543973035130822873669 399476994944087029288813)
                  ·
                    rfl

theorem cell20_875226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_875226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875226 prefixEnd_875226 := by exact prefixLift 875226
  have htrace : WordTrace (prefixWord ++ tailWord_875226) baseStart_875226 baseEnd_875226 := by
    simpa [prefixWord, tailWord_875226, baseEnd_875226] using wordTrace_append hprefix tailTrace_875226
  have hstable : (prefixWord ++ tailWord_875226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875226).length < 2 ^ (prefixWord ++ tailWord_875226).sum := by decide
  have hdescent : baseEnd_875226 < baseStart_875226 := by decide
  rcases family_descends (prefixWord ++ tailWord_875226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875250 : List Nat := [3, 2, 1, 3, 1, 4, 6]
def baseStart_875250 : Nat := 118140960795 + 875250 * 2 ^ 59
def prefixEnd_875250 : Nat := 4983230072969 + 3 ^ 40 * 875250 * 2
def baseEnd_875250 : Nat := 44387549910894401387635

theorem tailTrace_875250 : CollatzResearch.WordTrace tailWord_875250 prefixEnd_875250 44387549910894401387635 := by
  unfold tailWord_875250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7980747519781551411083801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21281993386084137096223469 7980747519781551411083801)
  ·
    refine ⟨5985560639836163558312851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7980747519781551411083801 5985560639836163558312851)
    ·
      refine ⟨8978340959754245337469277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5985560639836163558312851 8978340959754245337469277)
      ·
        refine ⟨3366877859907842001550979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8978340959754245337469277 3366877859907842001550979)
        ·
          refine ⟨5050316789861763002326469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366877859907842001550979 5050316789861763002326469)
          ·
            refine ⟨946934398099080562936213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5050316789861763002326469 946934398099080562936213)
            ·
              refine ⟨44387549910894401387635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 946934398099080562936213 44387549910894401387635)
              ·
                rfl

theorem cell20_875250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 6].length) (baseStart_875250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875250 prefixEnd_875250 := by exact prefixLift 875250
  have htrace : WordTrace (prefixWord ++ tailWord_875250) baseStart_875250 baseEnd_875250 := by
    simpa [prefixWord, tailWord_875250, baseEnd_875250] using wordTrace_append hprefix tailTrace_875250
  have hstable : (prefixWord ++ tailWord_875250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875250).length < 2 ^ (prefixWord ++ tailWord_875250).sum := by decide
  have hdescent : baseEnd_875250 < baseStart_875250 := by decide
  rcases family_descends (prefixWord ++ tailWord_875250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875315 : List Nat := [1, 1, 1, 2, 6, 3, 2, 2, 2]
def baseStart_875315 : Nat := 118140960795 + 875315 * 2 ^ 59
def prefixEnd_875315 : Nat := 4983230072969 + 3 ^ 40 * 875315 * 2
def baseEnd_875315 : Nat := 399517616969198275321783

theorem tailTrace_875315 : CollatzResearch.WordTrace tailWord_875315 prefixEnd_875315 399517616969198275321783 := by
  unfold tailWord_875315
  simp only [CollatzResearch.WordTrace]
  refine ⟨31925360823890721745451399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21283573882593814496967599 31925360823890721745451399)
  ·
    refine ⟨47888041235836082618177099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31925360823890721745451399 47888041235836082618177099)
    ·
      refine ⟨71832061853754123927265649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47888041235836082618177099 71832061853754123927265649)
      ·
        refine ⟨53874046390315592945449237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71832061853754123927265649 53874046390315592945449237)
        ·
          refine ⟨2525345924546043419317933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53874046390315592945449237 2525345924546043419317933)
          ·
            refine ⟨947004721704766282244225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2525345924546043419317933 947004721704766282244225)
            ·
              refine ⟨710253541278574711683169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947004721704766282244225 710253541278574711683169)
              ·
                refine ⟨532690155958931033762377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710253541278574711683169 532690155958931033762377)
                ·
                  refine ⟨399517616969198275321783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532690155958931033762377 399517616969198275321783)
                  ·
                    rfl

theorem cell20_875315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 2].length) (baseStart_875315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875315 prefixEnd_875315 := by exact prefixLift 875315
  have htrace : WordTrace (prefixWord ++ tailWord_875315) baseStart_875315 baseEnd_875315 := by
    simpa [prefixWord, tailWord_875315, baseEnd_875315] using wordTrace_append hprefix tailTrace_875315
  have hstable : (prefixWord ++ tailWord_875315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875315).length < 2 ^ (prefixWord ++ tailWord_875315).sum := by decide
  have hdescent : baseEnd_875315 < baseStart_875315 := by decide
  rcases family_descends (prefixWord ++ tailWord_875315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875319 : List Nat := [1, 1, 3, 1, 2, 1, 5, 4, 2]
def baseStart_875319 : Nat := 118140960795 + 875319 * 2 ^ 59
def prefixEnd_875319 : Nat := 4983230072969 + 3 ^ 40 * 875319 * 2
def baseEnd_875319 : Nat := 399519442678192039188433

theorem tailTrace_875319 : CollatzResearch.WordTrace tailWord_875319 prefixEnd_875319 399519442678192039188433 := by
  unfold tailWord_875319
  simp only [CollatzResearch.WordTrace]
  refine ⟨31925506715876230428597011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21283671143917486952398007 31925506715876230428597011)
  ·
    refine ⟨47888260073814345642895517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31925506715876230428597011 47888260073814345642895517)
    ·
      refine ⟨17958097527680379616085819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47888260073814345642895517 17958097527680379616085819)
      ·
        refine ⟨26937146291520569424128729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17958097527680379616085819 26937146291520569424128729)
        ·
          refine ⟨20202859718640427068096547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26937146291520569424128729 20202859718640427068096547)
          ·
            refine ⟨30304289577960640602144821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20202859718640427068096547 30304289577960640602144821)
            ·
              refine ⟨2841027147933810056451077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30304289577960640602144821 2841027147933810056451077)
              ·
                refine ⟨532692590237589385584577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2841027147933810056451077 532692590237589385584577)
                ·
                  refine ⟨399519442678192039188433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532692590237589385584577 399519442678192039188433)
                  ·
                    rfl

theorem cell20_875319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 2].length) (baseStart_875319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875319 prefixEnd_875319 := by exact prefixLift 875319
  have htrace : WordTrace (prefixWord ++ tailWord_875319) baseStart_875319 baseEnd_875319 := by
    simpa [prefixWord, tailWord_875319, baseEnd_875319] using wordTrace_append hprefix tailTrace_875319
  have hstable : (prefixWord ++ tailWord_875319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875319).length < 2 ^ (prefixWord ++ tailWord_875319).sum := by decide
  have hdescent : baseEnd_875319 < baseStart_875319 := by decide
  rcases family_descends (prefixWord ++ tailWord_875319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875340 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_875340 : Nat := 118140960795 + 875340 * 2 ^ 59
def prefixEnd_875340 : Nat := 4983230072969 + 3 ^ 40 * 875340 * 2
def baseEnd_875340 : Nat := 399529027650409299488347

theorem tailTrace_875340 : CollatzResearch.WordTrace tailWord_875340 prefixEnd_875340 399529027650409299488347 := by
  unfold tailWord_875340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15963136324400075507555737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21284181765866767343407649 15963136324400075507555737)
  ·
    refine ⟨11972352243300056630666803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15963136324400075507555737 11972352243300056630666803)
    ·
      refine ⟨17958528364950084946000205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11972352243300056630666803 17958528364950084946000205)
      ·
        refine ⟨6734448136856281854750077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17958528364950084946000205 6734448136856281854750077)
        ·
          refine ⟨2525418051321105695531279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6734448136856281854750077 2525418051321105695531279)
          ·
            refine ⟨3788127076981658543296919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525418051321105695531279 3788127076981658543296919)
            ·
              refine ⟨5682190615472487814945379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788127076981658543296919 5682190615472487814945379)
              ·
                refine ⟨8523285923208731722418069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682190615472487814945379 8523285923208731722418069)
                ·
                  refine ⟨399529027650409299488347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8523285923208731722418069 399529027650409299488347)
                  ·
                    rfl

theorem cell20_875340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_875340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875340 prefixEnd_875340 := by exact prefixLift 875340
  have htrace : WordTrace (prefixWord ++ tailWord_875340) baseStart_875340 baseEnd_875340 := by
    simpa [prefixWord, tailWord_875340, baseEnd_875340] using wordTrace_append hprefix tailTrace_875340
  have hstable : (prefixWord ++ tailWord_875340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875340).length < 2 ^ (prefixWord ++ tailWord_875340).sum := by decide
  have hdescent : baseEnd_875340 < baseStart_875340 := by decide
  rcases family_descends (prefixWord ++ tailWord_875340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875371 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 3]
def baseStart_875371 : Nat := 118140960795 + 875371 * 2 ^ 59
def prefixEnd_875371 : Nat := 4983230072969 + 3 ^ 40 * 875371 * 2
def baseEnd_875371 : Nat := 399543176895110969454887

theorem tailTrace_875371 : CollatzResearch.WordTrace tailWord_875371 prefixEnd_875371 399543176895110969454887 := by
  unfold tailWord_875371
  simp only [CollatzResearch.WordTrace]
  refine ⟨31927403311687843309489967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21284935541125228872993311 31927403311687843309489967)
  ·
    refine ⟨47891104967531764964234951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31927403311687843309489967 47891104967531764964234951)
    ·
      refine ⟨71836657451297647446352427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47891104967531764964234951 71836657451297647446352427)
      ·
        refine ⟨107754986176946471169528641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71836657451297647446352427 107754986176946471169528641)
        ·
          refine ⟨80816239632709853377146481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107754986176946471169528641 80816239632709853377146481)
          ·
            refine ⟨60612179724532390032859861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80816239632709853377146481 60612179724532390032859861)
            ·
              refine ⟨1420597962293727891395153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60612179724532390032859861 1420597962293727891395153)
              ·
                refine ⟨1065448471720295918546365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420597962293727891395153 1065448471720295918546365)
                ·
                  refine ⟨399543176895110969454887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065448471720295918546365 399543176895110969454887)
                  ·
                    rfl

theorem cell20_875371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_875371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875371 prefixEnd_875371 := by exact prefixLift 875371
  have htrace : WordTrace (prefixWord ++ tailWord_875371) baseStart_875371 baseEnd_875371 := by
    simpa [prefixWord, tailWord_875371, baseEnd_875371] using wordTrace_append hprefix tailTrace_875371
  have hstable : (prefixWord ++ tailWord_875371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875371).length < 2 ^ (prefixWord ++ tailWord_875371).sum := by decide
  have hdescent : baseEnd_875371 < baseStart_875371 := by decide
  rcases family_descends (prefixWord ++ tailWord_875371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875374 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_875374 : Nat := 118140960795 + 875374 * 2 ^ 59
def prefixEnd_875374 : Nat := 4983230072969 + 3 ^ 40 * 875374 * 2
def baseEnd_875374 : Nat := 399544546176856292354875

theorem tailTrace_875374 : CollatzResearch.WordTrace tailWord_875374 prefixEnd_875374 399544546176856292354875 := by
  unfold tailWord_875374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990939091334621852731147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21285008487117983214566117 3990939091334621852731147)
  ·
    refine ⟨5986408637001932779096721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3990939091334621852731147 5986408637001932779096721)
    ·
      refine ⟨4489806477751449584322541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5986408637001932779096721 4489806477751449584322541)
      ·
        refine ⟨1683677429156793594120953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4489806477751449584322541 1683677429156793594120953)
        ·
          refine ⟨1262758071867595195590715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1683677429156793594120953 1262758071867595195590715)
          ·
            refine ⟨1894137107801392793386073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262758071867595195590715 1894137107801392793386073)
            ·
              refine ⟨1420602830851044595039555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894137107801392793386073 1420602830851044595039555)
              ·
                refine ⟨2130904246276566892559333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420602830851044595039555 2130904246276566892559333)
                ·
                  refine ⟨399544546176856292354875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130904246276566892559333 399544546176856292354875)
                  ·
                    rfl

theorem cell20_875374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_875374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875374 prefixEnd_875374 := by exact prefixLift 875374
  have htrace : WordTrace (prefixWord ++ tailWord_875374) baseStart_875374 baseEnd_875374 := by
    simpa [prefixWord, tailWord_875374, baseEnd_875374] using wordTrace_append hprefix tailTrace_875374
  have hstable : (prefixWord ++ tailWord_875374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875374).length < 2 ^ (prefixWord ++ tailWord_875374).sum := by decide
  have hdescent : baseEnd_875374 < baseStart_875374 := by decide
  rcases family_descends (prefixWord ++ tailWord_875374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875378 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_875378 : Nat := 118140960795 + 875378 * 2 ^ 59
def prefixEnd_875378 : Nat := 4983230072969 + 3 ^ 40 * 875378 * 2
def baseEnd_875378 : Nat := 399546371885850056221525

theorem tailTrace_875378 : CollatzResearch.WordTrace tailWord_875378 prefixEnd_875378 399546371885850056221525 := by
  unfold tailWord_875378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7981914655665620876248697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21285105748441655669996525 7981914655665620876248697)
  ·
    refine ⟨5986435991749215657186523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7981914655665620876248697 5986435991749215657186523)
    ·
      refine ⟨8979653987623823485779785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5986435991749215657186523 8979653987623823485779785)
      ·
        refine ⟨6734740490717867614334839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8979653987623823485779785 6734740490717867614334839)
        ·
          refine ⟨10102110736076801421502259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734740490717867614334839 10102110736076801421502259)
          ·
            refine ⟨15153166104115202132253389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102110736076801421502259 15153166104115202132253389)
            ·
              refine ⟨5682437289043200799595021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15153166104115202132253389 5682437289043200799595021)
              ·
                refine ⟨2130913983391200299848133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5682437289043200799595021 2130913983391200299848133)
                ·
                  refine ⟨399546371885850056221525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130913983391200299848133 399546371885850056221525)
                  ·
                    rfl

theorem cell20_875378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_875378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875378 prefixEnd_875378 := by exact prefixLift 875378
  have htrace : WordTrace (prefixWord ++ tailWord_875378) baseStart_875378 baseEnd_875378 := by
    simpa [prefixWord, tailWord_875378, baseEnd_875378] using wordTrace_append hprefix tailTrace_875378
  have hstable : (prefixWord ++ tailWord_875378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875378).length < 2 ^ (prefixWord ++ tailWord_875378).sum := by decide
  have hdescent : baseEnd_875378 < baseStart_875378 := by decide
  rcases family_descends (prefixWord ++ tailWord_875378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875394 : List Nat := [3, 4, 2, 2, 2, 1, 2, 4]
def baseStart_875394 : Nat := 118140960795 + 875394 * 2 ^ 59
def prefixEnd_875394 : Nat := 4983230072969 + 3 ^ 40 * 875394 * 2
def baseEnd_875394 : Nat := 133184558240608370562709

theorem tailTrace_875394 : CollatzResearch.WordTrace tailWord_875394 prefixEnd_875394 133184558240608370562709 := by
  unfold tailWord_875394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982060547651129559394309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21285494793736345491718157 7982060547651129559394309)
  ·
    refine ⟨1496636352684586792386433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7982060547651129559394309 1496636352684586792386433)
    ·
      refine ⟨1122477264513440094289825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1496636352684586792386433 1122477264513440094289825)
      ·
        refine ⟨841857948385080070717369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1122477264513440094289825 841857948385080070717369)
        ·
          refine ⟨631393461288810053038027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841857948385080070717369 631393461288810053038027)
          ·
            refine ⟨947090191933215079557041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631393461288810053038027 947090191933215079557041)
            ·
              refine ⟨710317643949911309667781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947090191933215079557041 710317643949911309667781)
              ·
                refine ⟨133184558240608370562709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710317643949911309667781 133184558240608370562709)
                ·
                  rfl

theorem cell20_875394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_875394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875394 prefixEnd_875394 := by exact prefixLift 875394
  have htrace : WordTrace (prefixWord ++ tailWord_875394) baseStart_875394 baseEnd_875394 := by
    simpa [prefixWord, tailWord_875394, baseEnd_875394] using wordTrace_append hprefix tailTrace_875394
  have hstable : (prefixWord ++ tailWord_875394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875394).length < 2 ^ (prefixWord ++ tailWord_875394).sum := by decide
  have hdescent : baseEnd_875394 < baseStart_875394 := by decide
  rcases family_descends (prefixWord ++ tailWord_875394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875402 : List Nat := [3, 1, 2, 4, 1, 2, 1, 6]
def baseStart_875402 : Nat := 118140960795 + 875402 * 2 ^ 59
def prefixEnd_875402 : Nat := 4983230072969 + 3 ^ 40 * 875402 * 2
def baseEnd_875402 : Nat := 133185775379937546473809

theorem tailTrace_875402 : CollatzResearch.WordTrace tailWord_875402 prefixEnd_875402 133185775379937546473809 := by
  unfold tailWord_875402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982133493643883900967115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21285689316383690402578973 7982133493643883900967115)
  ·
    refine ⟨11973200240465825851450673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7982133493643883900967115 11973200240465825851450673)
    ·
      refine ⟨8979900180349369388588005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11973200240465825851450673 8979900180349369388588005)
      ·
        refine ⟨1683731283815506760360251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8979900180349369388588005 1683731283815506760360251)
        ·
          refine ⟨2525596925723260140540377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683731283815506760360251 2525596925723260140540377)
          ·
            refine ⟨1894197694292445105405283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2525596925723260140540377 1894197694292445105405283)
            ·
              refine ⟨2841296541438667658107925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894197694292445105405283 2841296541438667658107925)
              ·
                refine ⟨133185775379937546473809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2841296541438667658107925 133185775379937546473809)
                ·
                  rfl

theorem cell20_875402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_875402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875402 prefixEnd_875402 := by exact prefixLift 875402
  have htrace : WordTrace (prefixWord ++ tailWord_875402) baseStart_875402 baseEnd_875402 := by
    simpa [prefixWord, tailWord_875402, baseEnd_875402] using wordTrace_append hprefix tailTrace_875402
  have hstable : (prefixWord ++ tailWord_875402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875402).length < 2 ^ (prefixWord ++ tailWord_875402).sum := by decide
  have hdescent : baseEnd_875402 < baseStart_875402 := by decide
  rcases family_descends (prefixWord ++ tailWord_875402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875423 : List Nat := [1, 1, 2, 5, 2, 1, 8]
def baseStart_875423 : Nat := 118140960795 + 875423 * 2 ^ 59
def prefixEnd_875423 : Nat := 4983230072969 + 3 ^ 40 * 875423 * 2
def baseEnd_875423 : Nat := 44396323456892211080149

theorem tailTrace_875423 : CollatzResearch.WordTrace tailWord_875423 prefixEnd_875423 44396323456892211080149 := by
  unfold tailWord_875423
  simp only [CollatzResearch.WordTrace]
  refine ⟨31929299907499456190382923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21286199938332970793588615 31929299907499456190382923)
  ·
    refine ⟨47893949861249184285574385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31929299907499456190382923 47893949861249184285574385)
    ·
      refine ⟨35920462395936888214180789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47893949861249184285574385 35920462395936888214180789)
      ·
        refine ⟨3367543349619083270079449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35920462395936888214180789 3367543349619083270079449)
        ·
          refine ⟨2525657512214312452559587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3367543349619083270079449 2525657512214312452559587)
          ·
            refine ⟨3788486268321468678839381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525657512214312452559587 3788486268321468678839381)
            ·
              refine ⟨44396323456892211080149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3788486268321468678839381 44396323456892211080149)
              ·
                rfl

theorem cell20_875423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 8].length) (baseStart_875423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875423 prefixEnd_875423 := by exact prefixLift 875423
  have htrace : WordTrace (prefixWord ++ tailWord_875423) baseStart_875423 baseEnd_875423 := by
    simpa [prefixWord, tailWord_875423, baseEnd_875423] using wordTrace_append hprefix tailTrace_875423
  have hstable : (prefixWord ++ tailWord_875423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875423).length < 2 ^ (prefixWord ++ tailWord_875423).sum := by decide
  have hdescent : baseEnd_875423 < baseStart_875423 := by decide
  rcases family_descends (prefixWord ++ tailWord_875423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875454 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_875454 : Nat := 118140960795 + 875454 * 2 ^ 59
def prefixEnd_875454 : Nat := 4983230072969 + 3 ^ 40 * 875454 * 2
def baseEnd_875454 : Nat := 399581060356731569687881

theorem tailTrace_875454 : CollatzResearch.WordTrace tailWord_875454 prefixEnd_875454 399581060356731569687881 := by
  unfold tailWord_875454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991303821298393560595177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21286953713591432323174277 3991303821298393560595177)
  ·
    refine ⟨2993477865973795170446383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3991303821298393560595177 2993477865973795170446383)
    ·
      refine ⟨4490216798960692755669575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993477865973795170446383 4490216798960692755669575)
      ·
        refine ⟨6735325198441039133504363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490216798960692755669575 6735325198441039133504363)
        ·
          refine ⟨10102987797661558700256545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735325198441039133504363 10102987797661558700256545)
          ·
            refine ⟨7577240848246169025192409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10102987797661558700256545 7577240848246169025192409)
            ·
              refine ⟨5682930636184626768894307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7577240848246169025192409 5682930636184626768894307)
              ·
                refine ⟨8524395954276940153341461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682930636184626768894307 8524395954276940153341461)
                ·
                  refine ⟨399581060356731569687881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8524395954276940153341461 399581060356731569687881)
                  ·
                    rfl

theorem cell20_875454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_875454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875454 prefixEnd_875454 := by exact prefixLift 875454
  have htrace : WordTrace (prefixWord ++ tailWord_875454) baseStart_875454 baseEnd_875454 := by
    simpa [prefixWord, tailWord_875454, baseEnd_875454] using wordTrace_append hprefix tailTrace_875454
  have hstable : (prefixWord ++ tailWord_875454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875454).length < 2 ^ (prefixWord ++ tailWord_875454).sum := by decide
  have hdescent : baseEnd_875454 < baseStart_875454 := by decide
  rcases family_descends (prefixWord ++ tailWord_875454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875478 : List Nat := [5, 2, 1, 1, 2, 9]
def baseStart_875478 : Nat := 118140960795 + 875478 * 2 ^ 59
def prefixEnd_875478 : Nat := 4983230072969 + 3 ^ 40 * 875478 * 2
def baseEnd_875478 : Nat := 14799704244840524181029

theorem tailTrace_875478 : CollatzResearch.WordTrace tailWord_875478 prefixEnd_875478 14799704244840524181029 := by
  unfold tailWord_875478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995706620143762536477193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21287537281533467055756725 1995706620143762536477193)
  ·
    refine ⟨1496779965107821902357895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1995706620143762536477193 1496779965107821902357895)
    ·
      refine ⟨2245169947661732853536843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496779965107821902357895 2245169947661732853536843)
      ·
        refine ⟨3367754921492599280305265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2245169947661732853536843 3367754921492599280305265)
        ·
          refine ⟨2525816191119449460228949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3367754921492599280305265 2525816191119449460228949)
          ·
            refine ⟨14799704244840524181029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2525816191119449460228949 14799704244840524181029)
            ·
              rfl

theorem cell20_875478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 9].length) (baseStart_875478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875478 prefixEnd_875478 := by exact prefixLift 875478
  have htrace : WordTrace (prefixWord ++ tailWord_875478) baseStart_875478 baseEnd_875478 := by
    simpa [prefixWord, tailWord_875478, baseEnd_875478] using wordTrace_append hprefix tailTrace_875478
  have hstable : (prefixWord ++ tailWord_875478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875478).length < 2 ^ (prefixWord ++ tailWord_875478).sum := by decide
  have hdescent : baseEnd_875478 < baseStart_875478 := by decide
  rcases family_descends (prefixWord ++ tailWord_875478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875508 : List Nat := [2, 6, 2, 1, 1, 1, 3, 4]
def baseStart_875508 : Nat := 118140960795 + 875508 * 2 ^ 59
def prefixEnd_875508 : Nat := 4983230072969 + 3 ^ 40 * 875508 * 2
def baseEnd_875508 : Nat := 133201902476049127295887

theorem tailTrace_875508 : CollatzResearch.WordTrace tailWord_875508 prefixEnd_875508 133201902476049127295887 := by
  unfold tailWord_875508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15966200056095757853613589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21288266741461010471484785 15966200056095757853613589)
  ·
    refine ⟨748415627629488649388137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15966200056095757853613589 748415627629488649388137)
    ·
      refine ⟨561311720722116487041103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748415627629488649388137 561311720722116487041103)
      ·
        refine ⟨841967581083174730561655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561311720722116487041103 841967581083174730561655)
        ·
          refine ⟨1262951371624762095842483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841967581083174730561655 1262951371624762095842483)
          ·
            refine ⟨1894427057437143143763725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262951371624762095842483 1894427057437143143763725)
            ·
              refine ⟨710410146538928678911397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1894427057437143143763725 710410146538928678911397)
              ·
                refine ⟨133201902476049127295887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710410146538928678911397 133201902476049127295887)
                ·
                  rfl

theorem cell20_875508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_875508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875508 prefixEnd_875508 := by exact prefixLift 875508
  have htrace : WordTrace (prefixWord ++ tailWord_875508) baseStart_875508 baseEnd_875508 := by
    simpa [prefixWord, tailWord_875508, baseEnd_875508] using wordTrace_append hprefix tailTrace_875508
  have hstable : (prefixWord ++ tailWord_875508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875508).length < 2 ^ (prefixWord ++ tailWord_875508).sum := by decide
  have hdescent : baseEnd_875508 < baseStart_875508 := by decide
  rcases family_descends (prefixWord ++ tailWord_875508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875516 : List Nat := [2, 2, 2, 1, 2, 4, 3, 4]
def baseStart_875516 : Nat := 118140960795 + 875516 * 2 ^ 59
def prefixEnd_875516 : Nat := 4983230072969 + 3 ^ 40 * 875516 * 2
def baseEnd_875516 : Nat := 133203119615378303206987

theorem tailTrace_875516 : CollatzResearch.WordTrace tailWord_875516 prefixEnd_875516 133203119615378303206987 := by
  unfold tailWord_875516
  simp only [CollatzResearch.WordTrace]
  refine ⟨15966345948081266536759201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21288461264108355382345601 15966345948081266536759201)
  ·
    refine ⟨11974759461060949902569401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15966345948081266536759201 11974759461060949902569401)
    ·
      refine ⟨8981069595795712426927051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11974759461060949902569401 8981069595795712426927051)
      ·
        refine ⟨13471604393693568640390577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8981069595795712426927051 13471604393693568640390577)
        ·
          refine ⟨10103703295270176480292933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13471604393693568640390577 10103703295270176480292933)
          ·
            refine ⟨1894444367863158090054925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10103703295270176480292933 1894444367863158090054925)
            ·
              refine ⟨710416637948684283770597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1894444367863158090054925 710416637948684283770597)
              ·
                refine ⟨133203119615378303206987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710416637948684283770597 133203119615378303206987)
                ·
                  rfl

theorem cell20_875516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_875516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875516 prefixEnd_875516 := by exact prefixLift 875516
  have htrace : WordTrace (prefixWord ++ tailWord_875516) baseStart_875516 baseEnd_875516 := by
    simpa [prefixWord, tailWord_875516, baseEnd_875516] using wordTrace_append hprefix tailTrace_875516
  have hstable : (prefixWord ++ tailWord_875516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875516).length < 2 ^ (prefixWord ++ tailWord_875516).sum := by decide
  have hdescent : baseEnd_875516 < baseStart_875516 := by decide
  rcases family_descends (prefixWord ++ tailWord_875516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875522 : List Nat := [3, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_875522 : Nat := 118140960795 + 875522 * 2 ^ 59
def prefixEnd_875522 : Nat := 4983230072969 + 3 ^ 40 * 875522 * 2
def baseEnd_875522 : Nat := 399612097409625555420937

theorem tailTrace_875522 : CollatzResearch.WordTrace tailWord_875522 prefixEnd_875522 399612097409625555420937 := by
  unfold tailWord_875522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7983227683535199024559205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21288607156093864065491213 7983227683535199024559205)
  ·
    refine ⟨1496855190662849817104851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7983227683535199024559205 1496855190662849817104851)
    ·
      refine ⟨2245282785994274725657277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496855190662849817104851 2245282785994274725657277)
      ·
        refine ⟨841981044747853022121479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2245282785994274725657277 841981044747853022121479)
        ·
          refine ⟨1262971567121779533182219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841981044747853022121479 1262971567121779533182219)
          ·
            refine ⟨1894457350682669299773329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262971567121779533182219 1894457350682669299773329)
            ·
              refine ⟨1420843013012001974829997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894457350682669299773329 1420843013012001974829997)
              ·
                refine ⟨532816129879500740561249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1420843013012001974829997 532816129879500740561249)
                ·
                  refine ⟨399612097409625555420937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532816129879500740561249 399612097409625555420937)
                  ·
                    rfl

theorem cell20_875522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_875522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875522 prefixEnd_875522 := by exact prefixLift 875522
  have htrace : WordTrace (prefixWord ++ tailWord_875522) baseStart_875522 baseEnd_875522 := by
    simpa [prefixWord, tailWord_875522, baseEnd_875522] using wordTrace_append hprefix tailTrace_875522
  have hstable : (prefixWord ++ tailWord_875522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875522).length < 2 ^ (prefixWord ++ tailWord_875522).sum := by decide
  have hdescent : baseEnd_875522 < baseStart_875522 := by decide
  rcases family_descends (prefixWord ++ tailWord_875522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875589 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_875589 : Nat := 118140960795 + 875589 * 2 ^ 59
def prefixEnd_875589 : Nat := 4983230072969 + 3 ^ 40 * 875589 * 2
def baseEnd_875589 : Nat := 399642678035271100187329

theorem tailTrace_875589 : CollatzResearch.WordTrace tailWord_875589 prefixEnd_875589 399642678035271100187329 := by
  unfold tailWord_875589
  simp only [CollatzResearch.WordTrace]
  refine ⟨31935354424898066540925821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21290236283265377693950547 31935354424898066540925821)
  ·
    refine ⟨11975757909336774952847183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31935354424898066540925821 11975757909336774952847183)
    ·
      refine ⟨17963636864005162429270775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11975757909336774952847183 17963636864005162429270775)
      ·
        refine ⟨26945455296007743643906163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17963636864005162429270775 26945455296007743643906163)
        ·
          refine ⟨40418182944011615465859245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26945455296007743643906163 40418182944011615465859245)
          ·
            refine ⟨15156818604004355799697217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40418182944011615465859245 15156818604004355799697217)
            ·
              refine ⟨11367613953003266849772913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15156818604004355799697217 11367613953003266849772913)
              ·
                refine ⟨8525710464752450137329685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11367613953003266849772913 8525710464752450137329685)
                ·
                  refine ⟨399642678035271100187329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8525710464752450137329685 399642678035271100187329)
                  ·
                    rfl

theorem cell20_875589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_875589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875589 prefixEnd_875589 := by exact prefixLift 875589
  have htrace : WordTrace (prefixWord ++ tailWord_875589) baseStart_875589 baseEnd_875589 := by
    simpa [prefixWord, tailWord_875589, baseEnd_875589] using wordTrace_append hprefix tailTrace_875589
  have hstable : (prefixWord ++ tailWord_875589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875589).length < 2 ^ (prefixWord ++ tailWord_875589).sum := by decide
  have hdescent : baseEnd_875589 < baseStart_875589 := by decide
  rcases family_descends (prefixWord ++ tailWord_875589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875703 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_875703 : Nat := 118140960795 + 875703 * 2 ^ 59
def prefixEnd_875703 : Nat := 4983230072969 + 3 ^ 40 * 875703 * 2
def baseEnd_875703 : Nat := 399694710741593370386863

theorem tailTrace_875703 : CollatzResearch.WordTrace tailWord_875703 prefixEnd_875703 399694710741593370386863 := by
  unfold tailWord_875703
  simp only [CollatzResearch.WordTrace]
  refine ⟨31939512346485064010575763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21293008230990042673717175 31939512346485064010575763)
  ·
    refine ⟨47909268519727596015863645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31939512346485064010575763 47909268519727596015863645)
    ·
      refine ⟨17965975694897848505948867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47909268519727596015863645 17965975694897848505948867)
      ·
        refine ⟨26948963542346772758923301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17965975694897848505948867 26948963542346772758923301)
        ·
          refine ⟨5052930664190019892298119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26948963542346772758923301 5052930664190019892298119)
          ·
            refine ⟨7579395996285029838447179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5052930664190019892298119 7579395996285029838447179)
            ·
              refine ⟨11369093994427544757670769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7579395996285029838447179 11369093994427544757670769)
              ·
                refine ⟨8526820495820658568253077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11369093994427544757670769 8526820495820658568253077)
                ·
                  refine ⟨399694710741593370386863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8526820495820658568253077 399694710741593370386863)
                  ·
                    rfl

theorem cell20_875703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_875703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875703 prefixEnd_875703 := by exact prefixLift 875703
  have htrace : WordTrace (prefixWord ++ tailWord_875703) baseStart_875703 baseEnd_875703 := by
    simpa [prefixWord, tailWord_875703, baseEnd_875703] using wordTrace_append hprefix tailTrace_875703
  have hstable : (prefixWord ++ tailWord_875703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875703).length < 2 ^ (prefixWord ++ tailWord_875703).sum := by decide
  have hdescent : baseEnd_875703 < baseStart_875703 := by decide
  rcases family_descends (prefixWord ++ tailWord_875703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875730 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_875730 : Nat := 118140960795 + 875730 * 2 ^ 59
def prefixEnd_875730 : Nat := 4983230072969 + 3 ^ 40 * 875730 * 2
def baseEnd_875730 : Nat := 399707034277301276486753

theorem tailTrace_875730 : CollatzResearch.WordTrace tailWord_875730 prefixEnd_875730 399707034277301276486753 := by
  unfold tailWord_875730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7985124279346811905452161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21293664744924831747872429 7985124279346811905452161)
  ·
    refine ⟨5988843209510108929089121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7985124279346811905452161 5988843209510108929089121)
    ·
      refine ⟨4491632407132581696816841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5988843209510108929089121 4491632407132581696816841)
      ·
        refine ⟨3368724305349436272612631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4491632407132581696816841 3368724305349436272612631)
        ·
          refine ⟨5053086458024154408918947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3368724305349436272612631 5053086458024154408918947)
          ·
            refine ⟨7579629687036231613378421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5053086458024154408918947 7579629687036231613378421)
            ·
              refine ⟨710590283159646713754227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7579629687036231613378421 710590283159646713754227)
              ·
                refine ⟨1065885424739470070631341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710590283159646713754227 1065885424739470070631341)
                ·
                  refine ⟨399707034277301276486753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065885424739470070631341 399707034277301276486753)
                  ·
                    rfl

theorem cell20_875730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_875730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875730 prefixEnd_875730 := by exact prefixLift 875730
  have htrace : WordTrace (prefixWord ++ tailWord_875730) baseStart_875730 baseEnd_875730 := by
    simpa [prefixWord, tailWord_875730, baseEnd_875730] using wordTrace_append hprefix tailTrace_875730
  have hstable : (prefixWord ++ tailWord_875730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875730).length < 2 ^ (prefixWord ++ tailWord_875730).sum := by decide
  have hdescent : baseEnd_875730 < baseStart_875730 := by decide
  rcases family_descends (prefixWord ++ tailWord_875730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875744 : List Nat := [2, 1, 1, 3, 1, 6, 2, 4]
def baseStart_875744 : Nat := 118140960795 + 875744 * 2 ^ 59
def prefixEnd_875744 : Nat := 4983230072969 + 3 ^ 40 * 875744 * 2
def baseEnd_875744 : Nat := 133237808086259816673343

theorem tailTrace_875744 : CollatzResearch.WordTrace tailWord_875744 prefixEnd_875744 133237808086259816673343 := by
  unfold tailWord_875744
  simp only [CollatzResearch.WordTrace]
  refine ⟨15970503869668264006409143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21294005159557685341878857 15970503869668264006409143)
  ·
    refine ⟨23955755804502396009613715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15970503869668264006409143 23955755804502396009613715)
    ·
      refine ⟨35933633706753594014420573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23955755804502396009613715 35933633706753594014420573)
      ·
        refine ⟨13475112640032597755407715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35933633706753594014420573 13475112640032597755407715)
        ·
          refine ⟨20212668960048896633111573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13475112640032597755407715 20212668960048896633111573)
          ·
            refine ⟨947468857502292029677105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20212668960048896633111573 947468857502292029677105)
            ·
              refine ⟨710601643126719022257829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947468857502292029677105 710601643126719022257829)
              ·
                refine ⟨133237808086259816673343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710601643126719022257829 133237808086259816673343)
                ·
                  rfl

theorem cell20_875744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_875744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875744 prefixEnd_875744 := by exact prefixLift 875744
  have htrace : WordTrace (prefixWord ++ tailWord_875744) baseStart_875744 baseEnd_875744 := by
    simpa [prefixWord, tailWord_875744, baseEnd_875744] using wordTrace_append hprefix tailTrace_875744
  have hstable : (prefixWord ++ tailWord_875744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875744).length < 2 ^ (prefixWord ++ tailWord_875744).sum := by decide
  have hdescent : baseEnd_875744 < baseStart_875744 := by decide
  rcases family_descends (prefixWord ++ tailWord_875744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875754 : List Nat := [3, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_875754 : Nat := 118140960795 + 875754 * 2 ^ 59
def prefixEnd_875754 : Nat := 4983230072969 + 3 ^ 40 * 875754 * 2
def baseEnd_875754 : Nat := 399717988531263859686655

theorem tailTrace_875754 : CollatzResearch.WordTrace tailWord_875754 prefixEnd_875754 399717988531263859686655 := by
  unfold tailWord_875754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7985343117325074930170579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21294248312866866480454877 7985343117325074930170579)
  ·
    refine ⟨11978014675987612395255869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7985343117325074930170579 11978014675987612395255869)
    ·
      refine ⟨4491755503495354648220951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11978014675987612395255869 4491755503495354648220951)
      ·
        refine ⟨6737633255243031972331427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4491755503495354648220951 6737633255243031972331427)
        ·
          refine ⟨10106449882864547958497141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737633255243031972331427 10106449882864547958497141)
          ·
            refine ⟨947479676518551371109107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10106449882864547958497141 947479676518551371109107)
            ·
              refine ⟨1421219514777827056663661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947479676518551371109107 1421219514777827056663661)
              ·
                refine ⟨532957318041685146248873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1421219514777827056663661 532957318041685146248873)
                ·
                  refine ⟨399717988531263859686655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 532957318041685146248873 399717988531263859686655)
                  ·
                    rfl

theorem cell20_875754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_875754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875754 prefixEnd_875754 := by exact prefixLift 875754
  have htrace : WordTrace (prefixWord ++ tailWord_875754) baseStart_875754 baseEnd_875754 := by
    simpa [prefixWord, tailWord_875754, baseEnd_875754] using wordTrace_append hprefix tailTrace_875754
  have hstable : (prefixWord ++ tailWord_875754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875754).length < 2 ^ (prefixWord ++ tailWord_875754).sum := by decide
  have hdescent : baseEnd_875754 < baseStart_875754 := by decide
  rcases family_descends (prefixWord ++ tailWord_875754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875827 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 3]
def baseStart_875827 : Nat := 118140960795 + 875827 * 2 ^ 59
def prefixEnd_875827 : Nat := 4983230072969 + 3 ^ 40 * 875827 * 2
def baseEnd_875827 : Nat := 399751307720400050253023

theorem tailTrace_875827 : CollatzResearch.WordTrace tailWord_875827 prefixEnd_875827 399751307720400050253023 := by
  unfold tailWord_875827
  simp only [CollatzResearch.WordTrace]
  refine ⟨31944034998035833188089735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21296023332023888792059823 31944034998035833188089735)
  ·
    refine ⟨47916052497053749782134603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31944034998035833188089735 47916052497053749782134603)
    ·
      refine ⟨71874078745580624673201905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47916052497053749782134603 71874078745580624673201905)
      ·
        refine ⟨53905559059185468504901429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71874078745580624673201905 53905559059185468504901429)
        ·
          refine ⟨5053646161798637672334509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53905559059185468504901429 5053646161798637672334509)
          ·
            refine ⟨1895117310674489127125441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5053646161798637672334509 1895117310674489127125441)
            ·
              refine ⟨1421337983005866845344081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895117310674489127125441 1421337983005866845344081)
              ·
                refine ⟨1066003487254400134008061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421337983005866845344081 1066003487254400134008061)
                ·
                  refine ⟨399751307720400050253023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066003487254400134008061 399751307720400050253023)
                  ·
                    rfl

theorem cell20_875827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_875827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875827 prefixEnd_875827 := by exact prefixLift 875827
  have htrace : WordTrace (prefixWord ++ tailWord_875827) baseStart_875827 baseEnd_875827 := by
    simpa [prefixWord, tailWord_875827, baseEnd_875827] using wordTrace_append hprefix tailTrace_875827
  have hstable : (prefixWord ++ tailWord_875827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875827).length < 2 ^ (prefixWord ++ tailWord_875827).sum := by decide
  have hdescent : baseEnd_875827 < baseStart_875827 := by decide
  rcases family_descends (prefixWord ++ tailWord_875827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875837 : List Nat := [1, 4, 1, 5, 1, 2, 1, 5]
def baseStart_875837 : Nat := 118140960795 + 875837 * 2 ^ 59
def prefixEnd_875837 : Nat := 4983230072969 + 3 ^ 40 * 875837 * 2
def baseEnd_875837 : Nat := 133251957330961486639883

theorem tailTrace_875837 : CollatzResearch.WordTrace tailWord_875837 prefixEnd_875837 133251957330961486639883 := by
  unfold tailWord_875837
  simp only [CollatzResearch.WordTrace]
  refine ⟨31944399727999604895953765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21296266485333069930635843 31944399727999604895953765)
  ·
    refine ⟨5989574948999925917991331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31944399727999604895953765 5989574948999925917991331)
    ·
      refine ⟨8984362423499888876986997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5989574948999925917991331 8984362423499888876986997)
      ·
        refine ⟨842283977203114582217531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8984362423499888876986997 842283977203114582217531)
        ·
          refine ⟨1263425965804671873326297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842283977203114582217531 1263425965804671873326297)
          ·
            refine ⟨947569474353503904994723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263425965804671873326297 947569474353503904994723)
            ·
              refine ⟨1421354211530255857492085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947569474353503904994723 1421354211530255857492085)
              ·
                refine ⟨133251957330961486639883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1421354211530255857492085 133251957330961486639883)
                ·
                  rfl

theorem cell20_875837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_875837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875837 prefixEnd_875837 := by exact prefixLift 875837
  have htrace : WordTrace (prefixWord ++ tailWord_875837) baseStart_875837 baseEnd_875837 := by
    simpa [prefixWord, tailWord_875837, baseEnd_875837] using wordTrace_append hprefix tailTrace_875837
  have hstable : (prefixWord ++ tailWord_875837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875837).length < 2 ^ (prefixWord ++ tailWord_875837).sum := by decide
  have hdescent : baseEnd_875837 < baseStart_875837 := by decide
  rcases family_descends (prefixWord ++ tailWord_875837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875844 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_875844 : Nat := 118140960795 + 875844 * 2 ^ 59
def prefixEnd_875844 : Nat := 4983230072969 + 3 ^ 40 * 875844 * 2
def baseEnd_875844 : Nat := 399759066983623546686287

theorem tailTrace_875844 : CollatzResearch.WordTrace tailWord_875844 prefixEnd_875844 399759066983623546686287 := by
  unfold tailWord_875844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15972327519487122545729293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21296436692649496727639057 15972327519487122545729293)
  ·
    refine ⟨5989622819807670954648485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15972327519487122545729293 5989622819807670954648485)
    ·
      refine ⟨1123054278713938303996591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5989622819807670954648485 1123054278713938303996591)
      ·
        refine ⟨1684581418070907455994887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123054278713938303996591 1684581418070907455994887)
        ·
          refine ⟨2526872127106361183992331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684581418070907455994887 2526872127106361183992331)
          ·
            refine ⟨3790308190659541775988497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526872127106361183992331 3790308190659541775988497)
            ·
              refine ⟨2842731142994656331991373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790308190659541775988497 2842731142994656331991373)
              ·
                refine ⟨1066024178622996124496765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842731142994656331991373 1066024178622996124496765)
                ·
                  refine ⟨399759066983623546686287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066024178622996124496765 399759066983623546686287)
                  ·
                    rfl

theorem cell20_875844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_875844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875844 prefixEnd_875844 := by exact prefixLift 875844
  have htrace : WordTrace (prefixWord ++ tailWord_875844) baseStart_875844 baseEnd_875844 := by
    simpa [prefixWord, tailWord_875844, baseEnd_875844] using wordTrace_append hprefix tailTrace_875844
  have hstable : (prefixWord ++ tailWord_875844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875844).length < 2 ^ (prefixWord ++ tailWord_875844).sum := by decide
  have hdescent : baseEnd_875844 < baseStart_875844 := by decide
  rcases family_descends (prefixWord ++ tailWord_875844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875879 : List Nat := [1, 1, 5, 1, 4, 1, 7]
def baseStart_875879 : Nat := 118140960795 + 875879 * 2 ^ 59
def prefixEnd_875879 : Nat := 4983230072969 + 3 ^ 40 * 875879 * 2
def baseEnd_875879 : Nat := 44419449104146553391053

theorem tailTrace_875879 : CollatzResearch.WordTrace tailWord_875879 prefixEnd_875879 44419449104146553391053 := by
  unfold tailWord_875879
  simp only [CollatzResearch.WordTrace]
  refine ⟨31945931593847446068982691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21297287729231630712655127 31945931593847446068982691)
  ·
    refine ⟨47918897390771169103474037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31945931593847446068982691 47918897390771169103474037)
    ·
      refine ⟨4492396630384797103450691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47918897390771169103474037 4492396630384797103450691)
      ·
        refine ⟨6738594945577195655176037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492396630384797103450691 6738594945577195655176037)
        ·
          refine ⟨1263486552295724185345507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6738594945577195655176037 1263486552295724185345507)
          ·
            refine ⟨1895229828443586278018261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263486552295724185345507 1895229828443586278018261)
            ·
              refine ⟨44419449104146553391053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1895229828443586278018261 44419449104146553391053)
              ·
                rfl

theorem cell20_875879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 7].length) (baseStart_875879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875879 prefixEnd_875879 := by exact prefixLift 875879
  have htrace : WordTrace (prefixWord ++ tailWord_875879) baseStart_875879 baseEnd_875879 := by
    simpa [prefixWord, tailWord_875879, baseEnd_875879] using wordTrace_append hprefix tailTrace_875879
  have hstable : (prefixWord ++ tailWord_875879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875879).length < 2 ^ (prefixWord ++ tailWord_875879).sum := by decide
  have hdescent : baseEnd_875879 < baseStart_875879 := by decide
  rcases family_descends (prefixWord ++ tailWord_875879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875900 : List Nat := [2, 2, 2, 1, 1, 1, 4, 7]
def baseStart_875900 : Nat := 118140960795 + 875900 * 2 ^ 59
def prefixEnd_875900 : Nat := 4983230072969 + 3 ^ 40 * 875900 * 2
def baseEnd_875900 : Nat := 133261542303178746939797

theorem tailTrace_875900 : CollatzResearch.WordTrace tailWord_875900 prefixEnd_875900 133261542303178746939797 := by
  unfold tailWord_875900
  simp only [CollatzResearch.WordTrace]
  refine ⟨15973348763385683327748577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21297798351180911103664769 15973348763385683327748577)
  ·
    refine ⟨11980011572539262495811433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15973348763385683327748577 11980011572539262495811433)
    ·
      refine ⟨8985008679404446871858575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11980011572539262495811433 8985008679404446871858575)
      ·
        refine ⟨13477513019106670307787863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8985008679404446871858575 13477513019106670307787863)
        ·
          refine ⟨20216269528660005461681795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13477513019106670307787863 20216269528660005461681795)
          ·
            refine ⟨30324404292990008192522693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20216269528660005461681795 30324404292990008192522693)
            ·
              refine ⟨5685825804935626536098005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30324404292990008192522693 5685825804935626536098005)
              ·
                refine ⟨133261542303178746939797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5685825804935626536098005 133261542303178746939797)
                ·
                  rfl

theorem cell20_875900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_875900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875900 prefixEnd_875900 := by exact prefixLift 875900
  have htrace : WordTrace (prefixWord ++ tailWord_875900) baseStart_875900 baseEnd_875900 := by
    simpa [prefixWord, tailWord_875900, baseEnd_875900] using wordTrace_append hprefix tailTrace_875900
  have hstable : (prefixWord ++ tailWord_875900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875900).length < 2 ^ (prefixWord ++ tailWord_875900).sum := by decide
  have hdescent : baseEnd_875900 < baseStart_875900 := by decide
  rcases family_descends (prefixWord ++ tailWord_875900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875913 : List Nat := [1, 2, 1, 1, 8, 1, 2, 4]
def baseStart_875913 : Nat := 118140960795 + 875913 * 2 ^ 59
def prefixEnd_875913 : Nat := 4983230072969 + 3 ^ 40 * 875913 * 2
def baseEnd_875913 : Nat := 133263520154588657795335

theorem tailTrace_875913 : CollatzResearch.WordTrace tailWord_875913 prefixEnd_875913 133263520154588657795335 := by
  unfold tailWord_875913
  simp only [CollatzResearch.WordTrace]
  refine ⟨31947171675724269875720393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21298114450482846583813595 31947171675724269875720393)
  ·
    refine ⟨23960378756793202406790295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31947171675724269875720393 23960378756793202406790295)
    ·
      refine ⟨35940568135189803610185443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23960378756793202406790295 35940568135189803610185443)
      ·
        refine ⟨53910852202784705415278165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35940568135189803610185443 53910852202784705415278165)
        ·
          refine ⟨631767799251383266585291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 53910852202784705415278165 631767799251383266585291)
          ·
            refine ⟨947651698877074899877937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631767799251383266585291 947651698877074899877937)
            ·
              refine ⟨710738774157806174908453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947651698877074899877937 710738774157806174908453)
              ·
                refine ⟨133263520154588657795335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710738774157806174908453 133263520154588657795335)
                ·
                  rfl

theorem cell20_875913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 4].length) (baseStart_875913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875913 prefixEnd_875913 := by exact prefixLift 875913
  have htrace : WordTrace (prefixWord ++ tailWord_875913) baseStart_875913 baseEnd_875913 := by
    simpa [prefixWord, tailWord_875913, baseEnd_875913] using wordTrace_append hprefix tailTrace_875913
  have hstable : (prefixWord ++ tailWord_875913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875913).length < 2 ^ (prefixWord ++ tailWord_875913).sum := by decide
  have hdescent : baseEnd_875913 < baseStart_875913 := by decide
  rcases family_descends (prefixWord ++ tailWord_875913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875944 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_875944 : Nat := 118140960795 + 875944 * 2 ^ 59
def prefixEnd_875944 : Nat := 4983230072969 + 3 ^ 40 * 875944 * 2
def baseEnd_875944 : Nat := 399804709708467643352545

theorem tailTrace_875944 : CollatzResearch.WordTrace tailWord_875944 prefixEnd_875944 399804709708467643352545 := by
  unfold tailWord_875944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15974151169305981085049443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21298868225741308113399257 15974151169305981085049443)
  ·
    refine ⟨23961226753958971627574165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15974151169305981085049443 23961226753958971627574165)
    ·
      refine ⟨1123182504091826795042539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23961226753958971627574165 1123182504091826795042539)
      ·
        refine ⟨1684773756137740192563809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123182504091826795042539 1684773756137740192563809)
        ·
          refine ⟨1263580317103305144422857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1684773756137740192563809 1263580317103305144422857)
          ·
            refine ⟨947685237827478858317143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263580317103305144422857 947685237827478858317143)
            ·
              refine ⟨1421527856741218287475715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947685237827478858317143 1421527856741218287475715)
              ·
                refine ⟨2132291785111827431213573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421527856741218287475715 2132291785111827431213573)
                ·
                  refine ⟨399804709708467643352545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132291785111827431213573 399804709708467643352545)
                  ·
                    rfl

theorem cell20_875944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_875944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875944 prefixEnd_875944 := by exact prefixLift 875944
  have htrace : WordTrace (prefixWord ++ tailWord_875944) baseStart_875944 baseEnd_875944 := by
    simpa [prefixWord, tailWord_875944, baseEnd_875944] using wordTrace_append hprefix tailTrace_875944
  have hstable : (prefixWord ++ tailWord_875944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875944).length < 2 ^ (prefixWord ++ tailWord_875944).sum := by decide
  have hdescent : baseEnd_875944 < baseStart_875944 := by decide
  rcases family_descends (prefixWord ++ tailWord_875944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875948 : List Nat := [2, 2, 1, 1, 1, 1, 4, 6, 2]
def baseStart_875948 : Nat := 118140960795 + 875948 * 2 ^ 59
def prefixEnd_875948 : Nat := 4983230072969 + 3 ^ 40 * 875948 * 2
def baseEnd_875948 : Nat := 399806535417461407219195

theorem tailTrace_875948 : CollatzResearch.WordTrace tailWord_875948 prefixEnd_875948 399806535417461407219195 := by
  unfold tailWord_875948
  simp only [CollatzResearch.WordTrace]
  refine ⟨15974224115298735426622249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21298965487064980568829665 15974224115298735426622249)
  ·
    refine ⟨11980668086474051569966687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15974224115298735426622249 11980668086474051569966687)
    ·
      refine ⟨17971002129711077354950031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11980668086474051569966687 17971002129711077354950031)
      ·
        refine ⟨26956503194566616032425047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17971002129711077354950031 26956503194566616032425047)
        ·
          refine ⟨40434754791849924048637571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26956503194566616032425047 40434754791849924048637571)
          ·
            refine ⟨60652132187774886072956357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40434754791849924048637571 60652132187774886072956357)
            ·
              refine ⟨11372274785207791138679317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60652132187774886072956357 11372274785207791138679317)
              ·
                refine ⟨533075380556615209625593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11372274785207791138679317 533075380556615209625593)
                ·
                  refine ⟨399806535417461407219195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533075380556615209625593 399806535417461407219195)
                  ·
                    rfl

theorem cell20_875948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_875948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875948 prefixEnd_875948 := by exact prefixLift 875948
  have htrace : WordTrace (prefixWord ++ tailWord_875948) baseStart_875948 baseEnd_875948 := by
    simpa [prefixWord, tailWord_875948, baseEnd_875948] using wordTrace_append hprefix tailTrace_875948
  have hstable : (prefixWord ++ tailWord_875948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875948).length < 2 ^ (prefixWord ++ tailWord_875948).sum := by decide
  have hdescent : baseEnd_875948 < baseStart_875948 := by decide
  rcases family_descends (prefixWord ++ tailWord_875948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875976 : List Nat := [2, 1, 3, 1, 3, 1, 1, 8]
def baseStart_875976 : Nat := 118140960795 + 875976 * 2 ^ 59
def prefixEnd_875976 : Nat := 4983230072969 + 3 ^ 40 * 875976 * 2
def baseEnd_875976 : Nat := 133273105126805918095249

theorem tailTrace_875976 : CollatzResearch.WordTrace tailWord_875976 prefixEnd_875976 133273105126805918095249 := by
  unfold tailWord_875976
  simp only [CollatzResearch.WordTrace]
  refine ⟨15974734737248015817631891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21299646316330687756842521 15974734737248015817631891)
  ·
    refine ⟨23962102105872023726447837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15974734737248015817631891 23962102105872023726447837)
    ·
      refine ⟨8985788289702008897417939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23962102105872023726447837 8985788289702008897417939)
      ·
        refine ⟨13478682434553013346126909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8985788289702008897417939 13478682434553013346126909)
        ·
          refine ⟨5054505912957380004797591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13478682434553013346126909 5054505912957380004797591)
          ·
            refine ⟨7581758869436070007196387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054505912957380004797591 7581758869436070007196387)
            ·
              refine ⟨11372638304154105010794581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581758869436070007196387 11372638304154105010794581)
              ·
                refine ⟨133273105126805918095249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11372638304154105010794581 133273105126805918095249)
                ·
                  rfl

theorem cell20_875976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_875976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875976 prefixEnd_875976 := by exact prefixLift 875976
  have htrace : WordTrace (prefixWord ++ tailWord_875976) baseStart_875976 baseEnd_875976 := by
    simpa [prefixWord, tailWord_875976, baseEnd_875976] using wordTrace_append hprefix tailTrace_875976
  have hstable : (prefixWord ++ tailWord_875976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875976).length < 2 ^ (prefixWord ++ tailWord_875976).sum := by decide
  have hdescent : baseEnd_875976 < baseStart_875976 := by decide
  rcases family_descends (prefixWord ++ tailWord_875976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875983 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_875983 : Nat := 118140960795 + 875983 * 2 ^ 59
def prefixEnd_875983 : Nat := 4983230072969 + 3 ^ 40 * 875983 * 2
def baseEnd_875983 : Nat := 399822510371156841052385

theorem tailTrace_875983 : CollatzResearch.WordTrace tailWord_875983 prefixEnd_875983 399822510371156841052385 := by
  unfold tailWord_875983
  simp only [CollatzResearch.WordTrace]
  refine ⟨31949724785470671830768603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21299816523647114553845735 31949724785470671830768603)
  ·
    refine ⟨47924587178206007746152905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31949724785470671830768603 47924587178206007746152905)
    ·
      refine ⟨35943440383654505809614679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47924587178206007746152905 35943440383654505809614679)
      ·
        refine ⟨53915160575481758714422019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35943440383654505809614679 53915160575481758714422019)
        ·
          refine ⟨80872740863222638071633029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53915160575481758714422019 80872740863222638071633029)
          ·
            refine ⟨15163638911854244638431193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80872740863222638071633029 15163638911854244638431193)
            ·
              refine ⟨11372729183890683478823395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15163638911854244638431193 11372729183890683478823395)
              ·
                refine ⟨17059093775836025218235093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11372729183890683478823395 17059093775836025218235093)
                ·
                  refine ⟨399822510371156841052385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17059093775836025218235093 399822510371156841052385)
                  ·
                    rfl

theorem cell20_875983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_875983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_875983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_875983 prefixEnd_875983 := by exact prefixLift 875983
  have htrace : WordTrace (prefixWord ++ tailWord_875983) baseStart_875983 baseEnd_875983 := by
    simpa [prefixWord, tailWord_875983, baseEnd_875983] using wordTrace_append hprefix tailTrace_875983
  have hstable : (prefixWord ++ tailWord_875983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875983).length < 2 ^ (prefixWord ++ tailWord_875983).sum := by decide
  have hdescent : baseEnd_875983 < baseStart_875983 := by decide
  rcases family_descends (prefixWord ++ tailWord_875983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876003 : List Nat := [1, 1, 1, 6, 2, 2, 1, 4, 2]
def baseStart_876003 : Nat := 118140960795 + 876003 * 2 ^ 59
def prefixEnd_876003 : Nat := 4983230072969 + 3 ^ 40 * 876003 * 2
def baseEnd_876003 : Nat := 399831638916125660385637

theorem tailTrace_876003 : CollatzResearch.WordTrace tailWord_876003 prefixEnd_876003 399831638916125660385637 := by
  unfold tailWord_876003
  simp only [CollatzResearch.WordTrace]
  refine ⟨31950454245398215246496663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21300302830265476830997775 31950454245398215246496663)
  ·
    refine ⟨47925681368097322869744995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31950454245398215246496663 47925681368097322869744995)
    ·
      refine ⟨71888522052145984304617493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47925681368097322869744995 71888522052145984304617493)
      ·
        refine ⟨3369774471194343014278945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71888522052145984304617493 3369774471194343014278945)
        ·
          refine ⟨2527330853395757260709209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369774471194343014278945 2527330853395757260709209)
          ·
            refine ⟨1895498140046817945531907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2527330853395757260709209 1895498140046817945531907)
            ·
              refine ⟨2843247210070226918297861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895498140046817945531907 2843247210070226918297861)
              ·
                refine ⟨533108851888167547180849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2843247210070226918297861 533108851888167547180849)
                ·
                  refine ⟨399831638916125660385637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533108851888167547180849 399831638916125660385637)
                  ·
                    rfl

theorem cell20_876003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 2].length) (baseStart_876003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876003 prefixEnd_876003 := by exact prefixLift 876003
  have htrace : WordTrace (prefixWord ++ tailWord_876003) baseStart_876003 baseEnd_876003 := by
    simpa [prefixWord, tailWord_876003, baseEnd_876003] using wordTrace_append hprefix tailTrace_876003
  have hstable : (prefixWord ++ tailWord_876003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876003).length < 2 ^ (prefixWord ++ tailWord_876003).sum := by decide
  have hdescent : baseEnd_876003 < baseStart_876003 := by decide
  rcases family_descends (prefixWord ++ tailWord_876003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876010 : List Nat := [3, 1, 3, 1, 4, 2, 1, 5]
def baseStart_876010 : Nat := 118140960795 + 876010 * 2 ^ 59
def prefixEnd_876010 : Nat := 4983230072969 + 3 ^ 40 * 876010 * 2
def baseEnd_876010 : Nat := 133278277968954915717425

theorem tailTrace_876010 : CollatzResearch.WordTrace tailWord_876010 prefixEnd_876010 133278277968954915717425 := by
  unfold tailWord_876010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987677389093213860500371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21300473037581903628000989 7987677389093213860500371)
  ·
    refine ⟨11981516083639820790750557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7987677389093213860500371 11981516083639820790750557)
    ·
      refine ⟨4493068531364932796531459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11981516083639820790750557 4493068531364932796531459)
      ·
        refine ⟨6739602797047399194797189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493068531364932796531459 6739602797047399194797189)
        ·
          refine ⟨1263675524446387349024473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6739602797047399194797189 1263675524446387349024473)
          ·
            refine ⟨947756643334790511768355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263675524446387349024473 947756643334790511768355)
            ·
              refine ⟨1421634965002185767652533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947756643334790511768355 1421634965002185767652533)
              ·
                refine ⟨133278277968954915717425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1421634965002185767652533 133278277968954915717425)
                ·
                  rfl

theorem cell20_876010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_876010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876010 prefixEnd_876010 := by exact prefixLift 876010
  have htrace : WordTrace (prefixWord ++ tailWord_876010) baseStart_876010 baseEnd_876010 := by
    simpa [prefixWord, tailWord_876010, baseEnd_876010] using wordTrace_append hprefix tailTrace_876010
  have hstable : (prefixWord ++ tailWord_876010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876010).length < 2 ^ (prefixWord ++ tailWord_876010).sum := by decide
  have hdescent : baseEnd_876010 < baseStart_876010 := by decide
  rcases family_descends (prefixWord ++ tailWord_876010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876083 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_876083 : Nat := 118140960795 + 876083 * 2 ^ 59
def prefixEnd_876083 : Nat := 4983230072969 + 3 ^ 40 * 876083 * 2
def baseEnd_876083 : Nat := 399868153096000937718643

theorem tailTrace_876083 : CollatzResearch.WordTrace tailWord_876083 prefixEnd_876083 399868153096000937718643 := by
  unfold tailWord_876083
  simp only [CollatzResearch.WordTrace]
  refine ⟨31953372085108388909408903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21302248056738925939605935 31953372085108388909408903)
  ·
    refine ⟨47930058127662583364113355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31953372085108388909408903 47930058127662583364113355)
    ·
      refine ⟨71895087191493875046170033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47930058127662583364113355 71895087191493875046170033)
      ·
        refine ⟨53921315393620406284627525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71895087191493875046170033 53921315393620406284627525)
        ·
          refine ⟨10110246636303826178367661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53921315393620406284627525 10110246636303826178367661)
          ·
            refine ⟨3791342488613934816887873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10110246636303826178367661 3791342488613934816887873)
            ·
              refine ⟨2843506866460451112665905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791342488613934816887873 2843506866460451112665905)
              ·
                refine ⟨2132630149845338334499429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843506866460451112665905 2132630149845338334499429)
                ·
                  refine ⟨399868153096000937718643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132630149845338334499429 399868153096000937718643)
                  ·
                    rfl

theorem cell20_876083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_876083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876083 prefixEnd_876083 := by exact prefixLift 876083
  have htrace : WordTrace (prefixWord ++ tailWord_876083) baseStart_876083 baseEnd_876083 := by
    simpa [prefixWord, tailWord_876083, baseEnd_876083] using wordTrace_append hprefix tailTrace_876083
  have hstable : (prefixWord ++ tailWord_876083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876083).length < 2 ^ (prefixWord ++ tailWord_876083).sum := by decide
  have hdescent : baseEnd_876083 < baseStart_876083 := by decide
  rcases family_descends (prefixWord ++ tailWord_876083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876086 : List Nat := [5, 1, 2, 1, 3, 1, 1, 6]
def baseStart_876086 : Nat := 118140960795 + 876086 * 2 ^ 59
def prefixEnd_876086 : Nat := 4983230072969 + 3 ^ 40 * 876086 * 2
def baseEnd_876086 : Nat := 133289840792582086872877

theorem tailTrace_876086 : CollatzResearch.WordTrace tailWord_876086 prefixEnd_876086 133289840792582086872877 := by
  unfold tailWord_876086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997092594006095026360507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21302321002731680281178741 1997092594006095026360507)
  ·
    refine ⟨2995638891009142539540761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1997092594006095026360507 2995638891009142539540761)
    ·
      refine ⟨2246729168256856904655571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2995638891009142539540761 2246729168256856904655571)
      ·
        refine ⟨3370093752385285356983357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246729168256856904655571 3370093752385285356983357)
        ·
          refine ⟨1263785157144482008868759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3370093752385285356983357 1263785157144482008868759)
          ·
            refine ⟨1895677735716723013303139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263785157144482008868759 1895677735716723013303139)
            ·
              refine ⟨2843516603575084519954709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895677735716723013303139 2843516603575084519954709)
              ·
                refine ⟨133289840792582086872877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2843516603575084519954709 133289840792582086872877)
                ·
                  rfl

theorem cell20_876086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_876086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876086 prefixEnd_876086 := by exact prefixLift 876086
  have htrace : WordTrace (prefixWord ++ tailWord_876086) baseStart_876086 baseEnd_876086 := by
    simpa [prefixWord, tailWord_876086, baseEnd_876086] using wordTrace_append hprefix tailTrace_876086
  have hstable : (prefixWord ++ tailWord_876086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876086).length < 2 ^ (prefixWord ++ tailWord_876086).sum := by decide
  have hdescent : baseEnd_876086 < baseStart_876086 := by decide
  rcases family_descends (prefixWord ++ tailWord_876086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876090 : List Nat := [3, 1, 1, 1, 3, 2, 3, 6]
def baseStart_876090 : Nat := 118140960795 + 876090 * 2 ^ 59
def prefixEnd_876090 : Nat := 4983230072969 + 3 ^ 40 * 876090 * 2
def baseEnd_876090 : Nat := 133290449362246674828427

theorem tailTrace_876090 : CollatzResearch.WordTrace tailWord_876090 prefixEnd_876090 133290449362246674828427 := by
  unfold tailWord_876090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7988406849020757276228431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21302418264055352736609149 7988406849020757276228431)
  ·
    refine ⟨11982610273531135914342647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7988406849020757276228431 11982610273531135914342647)
    ·
      refine ⟨17973915410296703871513971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11982610273531135914342647 17973915410296703871513971)
      ·
        refine ⟨26960873115445055807270957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17973915410296703871513971 26960873115445055807270957)
        ·
          refine ⟨10110327418291895927726609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26960873115445055807270957 10110327418291895927726609)
          ·
            refine ⟨7582745563718921945794957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10110327418291895927726609 7582745563718921945794957)
            ·
              refine ⟨2843529586394595729673109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7582745563718921945794957 2843529586394595729673109)
              ·
                refine ⟨133290449362246674828427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2843529586394595729673109 133290449362246674828427)
                ·
                  rfl

theorem cell20_876090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_876090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876090 prefixEnd_876090 := by exact prefixLift 876090
  have htrace : WordTrace (prefixWord ++ tailWord_876090) baseStart_876090 baseEnd_876090 := by
    simpa [prefixWord, tailWord_876090, baseEnd_876090] using wordTrace_append hprefix tailTrace_876090
  have hstable : (prefixWord ++ tailWord_876090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876090).length < 2 ^ (prefixWord ++ tailWord_876090).sum := by decide
  have hdescent : baseEnd_876090 < baseStart_876090 := by decide
  rcases family_descends (prefixWord ++ tailWord_876090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876114 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_876114 : Nat := 118140960795 + 876114 * 2 ^ 59
def prefixEnd_876114 : Nat := 4983230072969 + 3 ^ 40 * 876114 * 2
def baseEnd_876114 : Nat := 399882302340702607685183

theorem tailTrace_876114 : CollatzResearch.WordTrace tailWord_876114 prefixEnd_876114 399882302340702607685183 := by
  unfold tailWord_876114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7988625686999020300946849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21303001831997387469191597 7988625686999020300946849)
  ·
    refine ⟨5991469265249265225710137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7988625686999020300946849 5991469265249265225710137)
    ·
      refine ⟨4493601948936948919282603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5991469265249265225710137 4493601948936948919282603)
      ·
        refine ⟨6740402923405423378923905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493601948936948919282603 6740402923405423378923905)
        ·
          refine ⟨5055302192554067534192929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6740402923405423378923905 5055302192554067534192929)
          ·
            refine ⟨3791476644415550650644697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5055302192554067534192929 3791476644415550650644697)
            ·
              refine ⟨2843607483311662987983523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791476644415550650644697 2843607483311662987983523)
              ·
                refine ⟨4265411224967494481975285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843607483311662987983523 4265411224967494481975285)
                ·
                  refine ⟨399882302340702607685183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265411224967494481975285 399882302340702607685183)
                  ·
                    rfl

theorem cell20_876114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_876114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876114 prefixEnd_876114 := by exact prefixLift 876114
  have htrace : WordTrace (prefixWord ++ tailWord_876114) baseStart_876114 baseEnd_876114 := by
    simpa [prefixWord, tailWord_876114, baseEnd_876114] using wordTrace_append hprefix tailTrace_876114
  have hstable : (prefixWord ++ tailWord_876114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876114).length < 2 ^ (prefixWord ++ tailWord_876114).sum := by decide
  have hdescent : baseEnd_876114 < baseStart_876114 := by decide
  rcases family_descends (prefixWord ++ tailWord_876114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876131 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 3]
def baseStart_876131 : Nat := 118140960795 + 876131 * 2 ^ 59
def prefixEnd_876131 : Nat := 4983230072969 + 3 ^ 40 * 876131 * 2
def baseEnd_876131 : Nat := 399890061603926104118447

theorem tailTrace_876131 : CollatzResearch.WordTrace tailWord_876131 prefixEnd_876131 399890061603926104118447 := by
  unfold tailWord_876131
  simp only [CollatzResearch.WordTrace]
  refine ⟨31955122788934493107156247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21303415192622995404770831 31955122788934493107156247)
  ·
    refine ⟨47932684183401739660734371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31955122788934493107156247 47932684183401739660734371)
    ·
      refine ⟨71899026275102609491101557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47932684183401739660734371 71899026275102609491101557)
      ·
        refine ⟨6740533713290869639790771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71899026275102609491101557 6740533713290869639790771)
        ·
          refine ⟨10110800569936304459686157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740533713290869639790771 10110800569936304459686157)
          ·
            refine ⟨3791550213726114172382309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10110800569936304459686157 3791550213726114172382309)
            ·
              refine ⟨710915665073646407321683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3791550213726114172382309 710915665073646407321683)
              ·
                refine ⟨1066373497610469610982525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710915665073646407321683 1066373497610469610982525)
                ·
                  refine ⟨399890061603926104118447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066373497610469610982525 399890061603926104118447)
                  ·
                    rfl

theorem cell20_876131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 3].length) (baseStart_876131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876131 prefixEnd_876131 := by exact prefixLift 876131
  have htrace : WordTrace (prefixWord ++ tailWord_876131) baseStart_876131 baseEnd_876131 := by
    simpa [prefixWord, tailWord_876131, baseEnd_876131] using wordTrace_append hprefix tailTrace_876131
  have hstable : (prefixWord ++ tailWord_876131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876131).length < 2 ^ (prefixWord ++ tailWord_876131).sum := by decide
  have hdescent : baseEnd_876131 < baseStart_876131 := by decide
  rcases family_descends (prefixWord ++ tailWord_876131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876166 : List Nat := [6, 14]
def baseStart_876166 : Nat := 118140960795 + 876166 * 2 ^ 59
def prefixEnd_876166 : Nat := 4983230072969 + 3 ^ 40 * 876166 * 2
def baseEnd_876166 : Nat := 182855983794065632351

theorem tailTrace_876166 : CollatzResearch.WordTrace tailWord_876166 prefixEnd_876166 182855983794065632351 := by
  unfold tailWord_876166
  simp only [CollatzResearch.WordTrace]
  refine ⟨998637479493990440146261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21304266229205129389786901 998637479493990440146261)
  ·
    refine ⟨182855983794065632351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 14 998637479493990440146261 182855983794065632351)
    ·
      rfl

theorem cell20_876166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 14].length) (baseStart_876166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876166 prefixEnd_876166 := by exact prefixLift 876166
  have htrace : WordTrace (prefixWord ++ tailWord_876166) baseStart_876166 baseEnd_876166 := by
    simpa [prefixWord, tailWord_876166, baseEnd_876166] using wordTrace_append hprefix tailTrace_876166
  have hstable : (prefixWord ++ tailWord_876166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876166).length < 2 ^ (prefixWord ++ tailWord_876166).sum := by decide
  have hdescent : baseEnd_876166 < baseStart_876166 := by decide
  rcases family_descends (prefixWord ++ tailWord_876166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876168 : List Nat := [2, 1, 3, 5, 2, 1, 2, 2, 2]
def baseStart_876168 : Nat := 118140960795 + 876168 * 2 ^ 59
def prefixEnd_876168 : Nat := 4983230072969 + 3 ^ 40 * 876168 * 2
def baseEnd_876168 : Nat := 399906949412118419884963

theorem tailTrace_876168 : CollatzResearch.WordTrace tailWord_876168 prefixEnd_876168 399906949412118419884963 := by
  unfold tailWord_876168
  simp only [CollatzResearch.WordTrace]
  refine ⟨15978236144900224213126579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21304314859866965617502105 15978236144900224213126579)
  ·
    refine ⟨23967354217350336319689869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15978236144900224213126579 23967354217350336319689869)
    ·
      refine ⟨8987757831506376119883701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23967354217350336319689869 8987757831506376119883701)
      ·
        refine ⟨842602296703722761239097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8987757831506376119883701 842602296703722761239097)
        ·
          refine ⟨631951722527792070929323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842602296703722761239097 631951722527792070929323)
          ·
            refine ⟨947927583791688106393985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631951722527792070929323 947927583791688106393985)
            ·
              refine ⟨710945687843766079795489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947927583791688106393985 710945687843766079795489)
              ·
                refine ⟨533209265882824559846617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710945687843766079795489 533209265882824559846617)
                ·
                  refine ⟨399906949412118419884963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533209265882824559846617 399906949412118419884963)
                  ·
                    rfl

theorem cell20_876168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_876168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876168 prefixEnd_876168 := by exact prefixLift 876168
  have htrace : WordTrace (prefixWord ++ tailWord_876168) baseStart_876168 baseEnd_876168 := by
    simpa [prefixWord, tailWord_876168, baseEnd_876168] using wordTrace_append hprefix tailTrace_876168
  have hstable : (prefixWord ++ tailWord_876168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876168).length < 2 ^ (prefixWord ++ tailWord_876168).sum := by decide
  have hdescent : baseEnd_876168 < baseStart_876168 := by decide
  rcases family_descends (prefixWord ++ tailWord_876168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876183 : List Nat := [1, 1, 3, 3, 2, 4, 1, 5]
def baseStart_876183 : Nat := 118140960795 + 876183 * 2 ^ 59
def prefixEnd_876183 : Nat := 4983230072969 + 3 ^ 40 * 876183 * 2
def baseEnd_876183 : Nat := 133304598606948344794967

theorem tailTrace_876183 : CollatzResearch.WordTrace tailWord_876183 prefixEnd_876183 133304598606948344794967 := by
  unfold tailWord_876183
  simp only [CollatzResearch.WordTrace]
  refine ⟨31957019384746105988049203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21304679589830737325366135 31957019384746105988049203)
  ·
    refine ⟨47935529077119158982073805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31957019384746105988049203 47935529077119158982073805)
    ·
      refine ⟨17975823403919684618277677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47935529077119158982073805 17975823403919684618277677)
      ·
        refine ⟨6740933776469881731854129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17975823403919684618277677 6740933776469881731854129)
        ·
          refine ⟨5055700332352411298890597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6740933776469881731854129 5055700332352411298890597)
          ·
            refine ⟨947943812316077118541987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5055700332352411298890597 947943812316077118541987)
            ·
              refine ⟨1421915718474115677812981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947943812316077118541987 1421915718474115677812981)
              ·
                refine ⟨133304598606948344794967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1421915718474115677812981 133304598606948344794967)
                ·
                  rfl

theorem cell20_876183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_876183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876183 prefixEnd_876183 := by exact prefixLift 876183
  have htrace : WordTrace (prefixWord ++ tailWord_876183) baseStart_876183 baseEnd_876183 := by
    simpa [prefixWord, tailWord_876183, baseEnd_876183] using wordTrace_append hprefix tailTrace_876183
  have hstable : (prefixWord ++ tailWord_876183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876183).length < 2 ^ (prefixWord ++ tailWord_876183).sum := by decide
  have hdescent : baseEnd_876183 < baseStart_876183 := by decide
  rcases family_descends (prefixWord ++ tailWord_876183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876211 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_876211 : Nat := 118140960795 + 876211 * 2 ^ 59
def prefixEnd_876211 : Nat := 4983230072969 + 3 ^ 40 * 876211 * 2
def baseEnd_876211 : Nat := 399926575783801381451453

theorem tailTrace_876211 : CollatzResearch.WordTrace tailWord_876211 prefixEnd_876211 399926575783801381451453 := by
  unfold tailWord_876211
  simp only [CollatzResearch.WordTrace]
  refine ⟨31958040628644666770068487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21305360419096444513378991 31958040628644666770068487)
  ·
    refine ⟨47937060942967000155102731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31958040628644666770068487 47937060942967000155102731)
    ·
      refine ⟨71905591414450500232654097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47937060942967000155102731 71905591414450500232654097)
      ·
        refine ⟨53929193560837875174490573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71905591414450500232654097 53929193560837875174490573)
        ·
          refine ⟨20223447585314203190433965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53929193560837875174490573 20223447585314203190433965)
          ·
            refine ⟨7583792844492826196412737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20223447585314203190433965 7583792844492826196412737)
            ·
              refine ⟨5687844633369619647309553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7583792844492826196412737 5687844633369619647309553)
              ·
                refine ⟨4265883475027214735482165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5687844633369619647309553 4265883475027214735482165)
                ·
                  refine ⟨399926575783801381451453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265883475027214735482165 399926575783801381451453)
                  ·
                    rfl

theorem cell20_876211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_876211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876211 prefixEnd_876211 := by exact prefixLift 876211
  have htrace : WordTrace (prefixWord ++ tailWord_876211) baseStart_876211 baseEnd_876211 := by
    simpa [prefixWord, tailWord_876211, baseEnd_876211] using wordTrace_append hprefix tailTrace_876211
  have hstable : (prefixWord ++ tailWord_876211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876211).length < 2 ^ (prefixWord ++ tailWord_876211).sum := by decide
  have hdescent : baseEnd_876211 < baseStart_876211 := by decide
  rcases family_descends (prefixWord ++ tailWord_876211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876228 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_876228 : Nat := 118140960795 + 876228 * 2 ^ 59
def prefixEnd_876228 : Nat := 4983230072969 + 3 ^ 40 * 876228 * 2
def baseEnd_876228 : Nat := 399934335047024877884717

theorem tailTrace_876228 : CollatzResearch.WordTrace tailWord_876228 prefixEnd_876228 399934335047024877884717 := by
  unfold tailWord_876228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15979330334791539336718669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21305773779722052448958225 15979330334791539336718669)
  ·
    refine ⟨5992248875546827251269501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15979330334791539336718669 5992248875546827251269501)
    ·
      refine ⟨2247093328330060219226063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5992248875546827251269501 2247093328330060219226063)
      ·
        refine ⟨3370639992495090328839095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247093328330060219226063 3370639992495090328839095)
        ·
          refine ⟨5055959988742635493258643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370639992495090328839095 5055959988742635493258643)
          ·
            refine ⟨7583939983113953239887965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055959988742635493258643 7583939983113953239887965)
            ·
              refine ⟨2843977493667732464957987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7583939983113953239887965 2843977493667732464957987)
              ·
                refine ⟨4265966240501598697436981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843977493667732464957987 4265966240501598697436981)
                ·
                  refine ⟨399934335047024877884717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265966240501598697436981 399934335047024877884717)
                  ·
                    rfl

theorem cell20_876228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_876228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876228 prefixEnd_876228 := by exact prefixLift 876228
  have htrace : WordTrace (prefixWord ++ tailWord_876228) baseStart_876228 baseEnd_876228 := by
    simpa [prefixWord, tailWord_876228, baseEnd_876228] using wordTrace_append hprefix tailTrace_876228
  have hstable : (prefixWord ++ tailWord_876228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876228).length < 2 ^ (prefixWord ++ tailWord_876228).sum := by decide
  have hdescent : baseEnd_876228 < baseStart_876228 := by decide
  rcases family_descends (prefixWord ++ tailWord_876228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876259 : List Nat := [1, 1, 1, 7, 2, 1, 1, 6]
def baseStart_876259 : Nat := 118140960795 + 876259 * 2 ^ 59
def prefixEnd_876259 : Nat := 4983230072969 + 3 ^ 40 * 876259 * 2
def baseEnd_876259 : Nat := 133316161430575515950419

theorem tailTrace_876259 : CollatzResearch.WordTrace tailWord_876259 prefixEnd_876259 133316161430575515950419 := by
  unfold tailWord_876259
  simp only [CollatzResearch.WordTrace]
  refine ⟨31959791332470770967815831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21306527554980513978543887 31959791332470770967815831)
  ·
    refine ⟨47939686998706156451723747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31959791332470770967815831 47939686998706156451723747)
    ·
      refine ⟨71909530498059234677585621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47939686998706156451723747 71909530498059234677585621)
      ·
        refine ⟨1685379621048263312755913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 71909530498059234677585621 1685379621048263312755913)
        ·
          refine ⟨1264034715786197484566935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685379621048263312755913 1264034715786197484566935)
          ·
            refine ⟨1896052073679296226850403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264034715786197484566935 1896052073679296226850403)
            ·
              refine ⟨2844078110518944340275605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896052073679296226850403 2844078110518944340275605)
              ·
                refine ⟨133316161430575515950419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2844078110518944340275605 133316161430575515950419)
                ·
                  rfl

theorem cell20_876259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_876259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876259 prefixEnd_876259 := by exact prefixLift 876259
  have htrace : WordTrace (prefixWord ++ tailWord_876259) baseStart_876259 baseEnd_876259 := by
    simpa [prefixWord, tailWord_876259, baseEnd_876259] using wordTrace_append hprefix tailTrace_876259
  have hstable : (prefixWord ++ tailWord_876259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876259).length < 2 ^ (prefixWord ++ tailWord_876259).sum := by decide
  have hdescent : baseEnd_876259 < baseStart_876259 := by decide
  rcases family_descends (prefixWord ++ tailWord_876259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876269 : List Nat := [1, 5, 1, 2, 1, 2, 3, 3, 2]
def baseStart_876269 : Nat := 118140960795 + 876269 * 2 ^ 59
def prefixEnd_876269 : Nat := 4983230072969 + 3 ^ 40 * 876269 * 2
def baseEnd_876269 : Nat := 399953048564210957517883

theorem tailTrace_876269 : CollatzResearch.WordTrace tailWord_876269 prefixEnd_876269 399953048564210957517883 := by
  unfold tailWord_876269
  simp only [CollatzResearch.WordTrace]
  refine ⟨31960156062434542675679861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21306770708289695117119907 31960156062434542675679861)
  ·
    refine ⟨2996264630853238375844987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31960156062434542675679861 2996264630853238375844987)
    ·
      refine ⟨4494396946279857563767481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2996264630853238375844987 4494396946279857563767481)
      ·
        refine ⟨3370797709709893172825611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4494396946279857563767481 3370797709709893172825611)
        ·
          refine ⟨5056196564564839759238417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370797709709893172825611 5056196564564839759238417)
          ·
            refine ⟨3792147423423629819428813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5056196564564839759238417 3792147423423629819428813)
            ·
              refine ⟨1422055283783861182285805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3792147423423629819428813 1422055283783861182285805)
              ·
                refine ⟨533270731418947943357177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1422055283783861182285805 533270731418947943357177)
                ·
                  refine ⟨399953048564210957517883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533270731418947943357177 399953048564210957517883)
                  ·
                    rfl

theorem cell20_876269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_876269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876269 prefixEnd_876269 := by exact prefixLift 876269
  have htrace : WordTrace (prefixWord ++ tailWord_876269) baseStart_876269 baseEnd_876269 := by
    simpa [prefixWord, tailWord_876269, baseEnd_876269] using wordTrace_append hprefix tailTrace_876269
  have hstable : (prefixWord ++ tailWord_876269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876269).length < 2 ^ (prefixWord ++ tailWord_876269).sum := by decide
  have hdescent : baseEnd_876269 < baseStart_876269 := by decide
  rcases family_descends (prefixWord ++ tailWord_876269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876276 : List Nat := [2, 6, 1, 1, 1, 1, 8]
def baseStart_876276 : Nat := 118140960795 + 876276 * 2 ^ 59
def prefixEnd_876276 : Nat := 4983230072969 + 3 ^ 40 * 876276 * 2
def baseEnd_876276 : Nat := 44439582617216671587169

theorem tailTrace_876276 : CollatzResearch.WordTrace tailWord_876276 prefixEnd_876276 44439582617216671587169 := by
  unfold tailWord_876276
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980205686704591435592341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21306940915606121914123121 15980205686704591435592341)
  ·
    refine ⟨749072141564277723543391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15980205686704591435592341 749072141564277723543391)
    ·
      refine ⟨1123608212346416585315087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749072141564277723543391 1123608212346416585315087)
      ·
        refine ⟨1685412318519624877972631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123608212346416585315087 1685412318519624877972631)
        ·
          refine ⟨2528118477779437316958947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685412318519624877972631 2528118477779437316958947)
          ·
            refine ⟨3792177716669155975438421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528118477779437316958947 3792177716669155975438421)
            ·
              refine ⟨44439582617216671587169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3792177716669155975438421 44439582617216671587169)
              ·
                rfl

theorem cell20_876276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 8].length) (baseStart_876276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876276 prefixEnd_876276 := by exact prefixLift 876276
  have htrace : WordTrace (prefixWord ++ tailWord_876276) baseStart_876276 baseEnd_876276 := by
    simpa [prefixWord, tailWord_876276, baseEnd_876276] using wordTrace_append hprefix tailTrace_876276
  have hstable : (prefixWord ++ tailWord_876276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876276).length < 2 ^ (prefixWord ++ tailWord_876276).sum := by decide
  have hdescent : baseEnd_876276 < baseStart_876276 := by decide
  rcases family_descends (prefixWord ++ tailWord_876276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876286 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_876286 : Nat := 118140960795 + 876286 * 2 ^ 59
def prefixEnd_876286 : Nat := 4983230072969 + 3 ^ 40 * 876286 * 2
def baseEnd_876286 : Nat := 399960807827434453951147

theorem tailTrace_876286 : CollatzResearch.WordTrace tailWord_876286 prefixEnd_876286 399960807827434453951147 := by
  unfold tailWord_876286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995097012921619322381089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21307184068915303052699141 3995097012921619322381089)
  ·
    refine ⟨2996322759691214491785817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3995097012921619322381089 2996322759691214491785817)
    ·
      refine ⟨2247242069768410868839363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2996322759691214491785817 2247242069768410868839363)
      ·
        refine ⟨3370863104652616303259045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247242069768410868839363 3370863104652616303259045)
        ·
          refine ⟨632036832122365556861071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3370863104652616303259045 632036832122365556861071)
          ·
            refine ⟨948055248183548335291607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632036832122365556861071 948055248183548335291607)
            ·
              refine ⟨1422082872275322502937411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948055248183548335291607 1422082872275322502937411)
              ·
                refine ⟨2133124308412983754406117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422082872275322502937411 2133124308412983754406117)
                ·
                  refine ⟨399960807827434453951147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133124308412983754406117 399960807827434453951147)
                  ·
                    rfl

theorem cell20_876286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_876286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876286 prefixEnd_876286 := by exact prefixLift 876286
  have htrace : WordTrace (prefixWord ++ tailWord_876286) baseStart_876286 baseEnd_876286 := by
    simpa [prefixWord, tailWord_876286, baseEnd_876286] using wordTrace_append hprefix tailTrace_876286
  have hstable : (prefixWord ++ tailWord_876286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876286).length < 2 ^ (prefixWord ++ tailWord_876286).sum := by decide
  have hdescent : baseEnd_876286 < baseStart_876286 := by decide
  rcases family_descends (prefixWord ++ tailWord_876286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876287 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_876287 : Nat := 118140960795 + 876287 * 2 ^ 59
def prefixEnd_876287 : Nat := 4983230072969 + 3 ^ 40 * 876287 * 2
def baseEnd_876287 : Nat := 399961264254682894917809

theorem tailTrace_876287 : CollatzResearch.WordTrace tailWord_876287 prefixEnd_876287 399961264254682894917809 := by
  unfold tailWord_876287
  simp only [CollatzResearch.WordTrace]
  refine ⟨31960812576369331749835115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21307208384246221166556743 31960812576369331749835115)
  ·
    refine ⟨47941218864553997624752673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31960812576369331749835115 47941218864553997624752673)
    ·
      refine ⟨35955914148415498218564505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47941218864553997624752673 35955914148415498218564505)
      ·
        refine ⟨26966935611311623663923379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35955914148415498218564505 26966935611311623663923379)
        ·
          refine ⟨40450403416967435495885069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26966935611311623663923379 40450403416967435495885069)
          ·
            refine ⟨15168901281362788310956901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40450403416967435495885069 15168901281362788310956901)
            ·
              refine ⟨2844168990255522808304419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15168901281362788310956901 2844168990255522808304419)
              ·
                refine ⟨4266253485383284212456629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844168990255522808304419 4266253485383284212456629)
                ·
                  refine ⟨399961264254682894917809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266253485383284212456629 399961264254682894917809)
                  ·
                    rfl

theorem cell20_876287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_876287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876287 prefixEnd_876287 := by exact prefixLift 876287
  have htrace : WordTrace (prefixWord ++ tailWord_876287) baseStart_876287 baseEnd_876287 := by
    simpa [prefixWord, tailWord_876287, baseEnd_876287] using wordTrace_append hprefix tailTrace_876287
  have hstable : (prefixWord ++ tailWord_876287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876287).length < 2 ^ (prefixWord ++ tailWord_876287).sum := by decide
  have hdescent : baseEnd_876287 < baseStart_876287 := by decide
  rcases family_descends (prefixWord ++ tailWord_876287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876339 : List Nat := [1, 1, 1, 2, 15]
def baseStart_876339 : Nat := 118140960795 + 876339 * 2 ^ 59
def prefixEnd_876339 : Nat := 4983230072969 + 3 ^ 40 * 876339 * 2
def baseEnd_876339 : Nat := 4938086400883973150423

theorem tailTrace_876339 : CollatzResearch.WordTrace tailWord_876339 prefixEnd_876339 4938086400883973150423 := by
  unfold tailWord_876339
  simp only [CollatzResearch.WordTrace]
  refine ⟨31962709172180944630728071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21308472781453963087152047 31962709172180944630728071)
  ·
    refine ⟨47944063758271416946092107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31962709172180944630728071 47944063758271416946092107)
    ·
      refine ⟨71916095637407125419138161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47944063758271416946092107 71916095637407125419138161)
      ·
        refine ⟨53937071728055344064353621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71916095637407125419138161 53937071728055344064353621)
        ·
          refine ⟨4938086400883973150423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 53937071728055344064353621 4938086400883973150423)
          ·
            rfl

theorem cell20_876339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 15].length) (baseStart_876339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876339 prefixEnd_876339 := by exact prefixLift 876339
  have htrace : WordTrace (prefixWord ++ tailWord_876339) baseStart_876339 baseEnd_876339 := by
    simpa [prefixWord, tailWord_876339, baseEnd_876339] using wordTrace_append hprefix tailTrace_876339
  have hstable : (prefixWord ++ tailWord_876339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876339).length < 2 ^ (prefixWord ++ tailWord_876339).sum := by decide
  have hdescent : baseEnd_876339 < baseStart_876339 := by decide
  rcases family_descends (prefixWord ++ tailWord_876339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876341 : List Nat := [1, 3, 3, 1, 5, 1, 2, 2, 2]
def baseStart_876341 : Nat := 118140960795 + 876341 * 2 ^ 59
def prefixEnd_876341 : Nat := 4983230072969 + 3 ^ 40 * 876341 * 2
def baseEnd_876341 : Nat := 399985911326098707117589

theorem tailTrace_876341 : CollatzResearch.WordTrace tailWord_876341 prefixEnd_876341 399985911326098707117589 := by
  unfold tailWord_876341
  simp only [CollatzResearch.WordTrace]
  refine ⟨31962782118173698972300877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21308521412115799314867251 31962782118173698972300877)
  ·
    refine ⟨11986043294315137114612829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31962782118173698972300877 11986043294315137114612829)
    ·
      refine ⟨4494766235368176417979811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11986043294315137114612829 4494766235368176417979811)
      ·
        refine ⟨6742149353052264626969717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494766235368176417979811 6742149353052264626969717)
        ·
          refine ⟨632076501848649808778411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6742149353052264626969717 632076501848649808778411)
          ·
            refine ⟨948114752772974713167617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632076501848649808778411 948114752772974713167617)
            ·
              refine ⟨711086064579731034875713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948114752772974713167617 711086064579731034875713)
              ·
                refine ⟨533314548434798276156785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711086064579731034875713 533314548434798276156785)
                ·
                  refine ⟨399985911326098707117589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533314548434798276156785 399985911326098707117589)
                  ·
                    rfl

theorem cell20_876341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_876341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876341 prefixEnd_876341 := by exact prefixLift 876341
  have htrace : WordTrace (prefixWord ++ tailWord_876341) baseStart_876341 baseEnd_876341 := by
    simpa [prefixWord, tailWord_876341, baseEnd_876341] using wordTrace_append hprefix tailTrace_876341
  have hstable : (prefixWord ++ tailWord_876341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876341).length < 2 ^ (prefixWord ++ tailWord_876341).sum := by decide
  have hdescent : baseEnd_876341 < baseStart_876341 := by decide
  rcases family_descends (prefixWord ++ tailWord_876341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876373 : List Nat := [1, 3, 2, 2, 2, 3, 3, 4]
def baseStart_876373 : Nat := 118140960795 + 876373 * 2 ^ 59
def prefixEnd_876373 : Nat := 4983230072969 + 3 ^ 40 * 876373 * 2
def baseEnd_876373 : Nat := 133333505666016272683597

theorem tailTrace_876373 : CollatzResearch.WordTrace tailWord_876373 prefixEnd_876373 133333505666016272683597 := by
  unfold tailWord_876373
  simp only [CollatzResearch.WordTrace]
  refine ⟨31963949254057768437465773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21309299502705178958310515 31963949254057768437465773)
  ·
    refine ⟨11986480970271663164049665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31963949254057768437465773 11986480970271663164049665)
    ·
      refine ⟨8989860727703747373037249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11986480970271663164049665 8989860727703747373037249)
      ·
        refine ⟨6742395545777810529777937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8989860727703747373037249 6742395545777810529777937)
        ·
          refine ⟨5056796659333357897333453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6742395545777810529777937 5056796659333357897333453)
          ·
            refine ⟨1896298747250009211500045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5056796659333357897333453 1896298747250009211500045)
            ·
              refine ⟨711112030218753454312517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1896298747250009211500045 711112030218753454312517)
              ·
                refine ⟨133333505666016272683597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 711112030218753454312517 133333505666016272683597)
                ·
                  rfl

theorem cell20_876373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 4].length) (baseStart_876373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876373 prefixEnd_876373 := by exact prefixLift 876373
  have htrace : WordTrace (prefixWord ++ tailWord_876373) baseStart_876373 baseEnd_876373 := by
    simpa [prefixWord, tailWord_876373, baseEnd_876373] using wordTrace_append hprefix tailTrace_876373
  have hstable : (prefixWord ++ tailWord_876373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876373).length < 2 ^ (prefixWord ++ tailWord_876373).sum := by decide
  have hdescent : baseEnd_876373 < baseStart_876373 := by decide
  rcases family_descends (prefixWord ++ tailWord_876373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876401 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_876401 : Nat := 118140960795 + 876401 * 2 ^ 59
def prefixEnd_876401 : Nat := 4983230072969 + 3 ^ 40 * 876401 * 2
def baseEnd_876401 : Nat := 400013296961005165117343

theorem tailTrace_876401 : CollatzResearch.WordTrace tailWord_876401 prefixEnd_876401 400013296961005165117343 := by
  unfold tailWord_876401
  simp only [CollatzResearch.WordTrace]
  refine ⟨31964970497956329219485057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21309980331970886146323371 31964970497956329219485057)
  ·
    refine ⟨23973727873467246914613793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31964970497956329219485057 23973727873467246914613793)
    ·
      refine ⟨17980295905100435185960345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23973727873467246914613793 17980295905100435185960345)
      ·
        refine ⟨13485221928825326389470259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17980295905100435185960345 13485221928825326389470259)
        ·
          refine ⟨20227832893237989584205389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13485221928825326389470259 20227832893237989584205389)
          ·
            refine ⟨7585437334964246094077021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20227832893237989584205389 7585437334964246094077021)
            ·
              refine ⟨2844539000611592285278883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7585437334964246094077021 2844539000611592285278883)
              ·
                refine ⟨4266808500917388427918325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844539000611592285278883 4266808500917388427918325)
                ·
                  refine ⟨400013296961005165117343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266808500917388427918325 400013296961005165117343)
                  ·
                    rfl

theorem cell20_876401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_876401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876401 prefixEnd_876401 := by exact prefixLift 876401
  have htrace : WordTrace (prefixWord ++ tailWord_876401) baseStart_876401 baseEnd_876401 := by
    simpa [prefixWord, tailWord_876401, baseEnd_876401] using wordTrace_append hprefix tailTrace_876401
  have hstable : (prefixWord ++ tailWord_876401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876401).length < 2 ^ (prefixWord ++ tailWord_876401).sum := by decide
  have hdescent : baseEnd_876401 < baseStart_876401 := by decide
  rcases family_descends (prefixWord ++ tailWord_876401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876415 : List Nat := [1, 1, 2, 2, 1, 1, 3, 9]
def baseStart_876415 : Nat := 118140960795 + 876415 * 2 ^ 59
def prefixEnd_876415 : Nat := 4983230072969 + 3 ^ 40 * 876415 * 2
def baseEnd_876415 : Nat := 133339895647494446216873

theorem tailTrace_876415 : CollatzResearch.WordTrace tailWord_876415 prefixEnd_876415 133339895647494446216873 := by
  unfold tailWord_876415
  simp only [CollatzResearch.WordTrace]
  refine ⟨31965481119905609610494699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21310320746603739740329799 31965481119905609610494699)
  ·
    refine ⟨47948221679858414415742049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31965481119905609610494699 47948221679858414415742049)
    ·
      refine ⟨35961166259893810811806537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47948221679858414415742049 35961166259893810811806537)
      ·
        refine ⟨26970874694920358108854903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35961166259893810811806537 26970874694920358108854903)
        ·
          refine ⟨40456312042380537163282355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26970874694920358108854903 40456312042380537163282355)
          ·
            refine ⟨60684468063570805744923533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40456312042380537163282355 60684468063570805744923533)
            ·
              refine ⟨22756675523839052154346325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60684468063570805744923533 22756675523839052154346325)
              ·
                refine ⟨133339895647494446216873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22756675523839052154346325 133339895647494446216873)
                ·
                  rfl

theorem cell20_876415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_876415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876415 prefixEnd_876415 := by exact prefixLift 876415
  have htrace : WordTrace (prefixWord ++ tailWord_876415) baseStart_876415 baseEnd_876415 := by
    simpa [prefixWord, tailWord_876415, baseEnd_876415] using wordTrace_append hprefix tailTrace_876415
  have hstable : (prefixWord ++ tailWord_876415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876415).length < 2 ^ (prefixWord ++ tailWord_876415).sum := by decide
  have hdescent : baseEnd_876415 < baseStart_876415 := by decide
  rcases family_descends (prefixWord ++ tailWord_876415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
