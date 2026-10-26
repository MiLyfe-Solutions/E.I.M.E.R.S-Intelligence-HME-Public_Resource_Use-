import V185TrunkScan23Chunk1111

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6585803 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 5]
def baseStart_6585803 : Nat := 118140960795 + 6585803 * 2 ^ 59
def prefixEnd_6585803 : Nat := 4983230072969 + 3 ^ 40 * 6585803 * 2
def baseEnd_6585803 : Nat := 3381682434822401749174949

theorem tailTrace_6585803 : CollatzResearch.WordTrace tailWord_6585803 prefixEnd_6585803 3381682434822401749174949 := by
  unfold tailWord_6585803
  simp only [CollatzResearch.WordTrace]
  refine ⟨240203968959767971450346063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160135979306511980966897375 240203968959767971450346063)
  ·
    refine ⟨360305953439651957175519095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240203968959767971450346063 360305953439651957175519095)
    ·
      refine ⟨540458930159477935763278643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360305953439651957175519095 540458930159477935763278643)
      ·
        refine ⟨810688395239216903644917965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540458930159477935763278643 810688395239216903644917965)
        ·
          refine ⟨304008148214706338866844237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 810688395239216903644917965 304008148214706338866844237)
          ·
            refine ⟨114003055580514877075066589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304008148214706338866844237 114003055580514877075066589)
            ·
              refine ⟨42751145842693078903149971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114003055580514877075066589 42751145842693078903149971)
              ·
                refine ⟨64126718764039618354724957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42751145842693078903149971 64126718764039618354724957)
                ·
                  refine ⟨24047519536514856883021859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64126718764039618354724957 24047519536514856883021859)
                  ·
                    refine ⟨36071279304772285324532789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24047519536514856883021859 36071279304772285324532789)
                    ·
                      refine ⟨3381682434822401749174949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36071279304772285324532789 3381682434822401749174949)
                      ·
                        rfl

theorem cell23_6585803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_6585803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585803 prefixEnd_6585803 := by exact prefixLift 6585803
  have htrace : WordTrace (prefixWord ++ tailWord_6585803) baseStart_6585803 baseEnd_6585803 := by
    simpa [prefixWord, tailWord_6585803, baseEnd_6585803] using wordTrace_append hprefix tailTrace_6585803
  have hstable : (prefixWord ++ tailWord_6585803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585803).length < 2 ^ (prefixWord ++ tailWord_6585803).sum := by decide
  have hdescent : baseEnd_6585803 < baseStart_6585803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585814 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_6585814 : Nat := 118140960795 + 6585814 * 2 ^ 59
def prefixEnd_6585814 : Nat := 4983230072969 + 3 ^ 40 * 6585814 * 2
def baseEnd_6585814 : Nat := 1127229361036533735379133

theorem tailTrace_6585814 : CollatzResearch.WordTrace tailWord_6585814 prefixEnd_6585814 1127229361036533735379133 := by
  unfold tailWord_6585814
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012773135170507520562281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160136246775152080219330997 15012773135170507520562281)
  ·
    refine ⟨11259579851377880640421711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15012773135170507520562281 11259579851377880640421711)
    ·
      refine ⟨16889369777066820960632567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11259579851377880640421711 16889369777066820960632567)
      ·
        refine ⟨25334054665600231440948851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16889369777066820960632567 25334054665600231440948851)
        ·
          refine ⟨38001081998400347161423277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25334054665600231440948851 38001081998400347161423277)
          ·
            refine ⟨14250405749400130185533729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38001081998400347161423277 14250405749400130185533729)
            ·
              refine ⟨10687804312050097639150297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14250405749400130185533729 10687804312050097639150297)
              ·
                refine ⟨8015853234037573229362723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10687804312050097639150297 8015853234037573229362723)
                ·
                  refine ⟨12023779851056359844044085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8015853234037573229362723 12023779851056359844044085)
                  ·
                    refine ⟨1127229361036533735379133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12023779851056359844044085 1127229361036533735379133)
                    ·
                      rfl

theorem cell23_6585814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_6585814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585814 prefixEnd_6585814 := by exact prefixLift 6585814
  have htrace : WordTrace (prefixWord ++ tailWord_6585814) baseStart_6585814 baseEnd_6585814 := by
    simpa [prefixWord, tailWord_6585814, baseEnd_6585814] using wordTrace_append hprefix tailTrace_6585814
  have hstable : (prefixWord ++ tailWord_6585814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585814).length < 2 ^ (prefixWord ++ tailWord_6585814).sum := by decide
  have hdescent : baseEnd_6585814 < baseStart_6585814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585817 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 4]
def baseStart_6585817 : Nat := 118140960795 + 6585817 * 2 ^ 59
def prefixEnd_6585817 : Nat := 4983230072969 + 3 ^ 40 * 6585817 * 2
def baseEnd_6585817 : Nat := 3381689623551564694399885

theorem tailTrace_6585817 : CollatzResearch.WordTrace tailWord_6585817 prefixEnd_6585817 3381689623551564694399885 := by
  unfold tailWord_6585817
  simp only [CollatzResearch.WordTrace]
  refine ⟨240204479581717251841355705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160136319721144834560903803 240204479581717251841355705)
  ·
    refine ⟨180153359686287938881016779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240204479581717251841355705 180153359686287938881016779)
    ·
      refine ⟨270230039529431908321525169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180153359686287938881016779 270230039529431908321525169)
      ·
        refine ⟨202672529647073931241143877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270230039529431908321525169 202672529647073931241143877)
        ·
          refine ⟨38001099308826362107714477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202672529647073931241143877 38001099308826362107714477)
          ·
            refine ⟨14250412240809885790392929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38001099308826362107714477 14250412240809885790392929)
            ·
              refine ⟨10687809180607414342794697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14250412240809885790392929 10687809180607414342794697)
              ·
                refine ⟨8015856885455560757096023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10687809180607414342794697 8015856885455560757096023)
                ·
                  refine ⟨12023785328183341135644035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8015856885455560757096023 12023785328183341135644035)
                  ·
                    refine ⟨18035677992275011703466053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12023785328183341135644035 18035677992275011703466053)
                    ·
                      refine ⟨3381689623551564694399885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18035677992275011703466053 3381689623551564694399885)
                      ·
                        rfl

theorem cell23_6585817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_6585817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585817 prefixEnd_6585817 := by exact prefixLift 6585817
  have htrace : WordTrace (prefixWord ++ tailWord_6585817) baseStart_6585817 baseEnd_6585817 := by
    simpa [prefixWord, tailWord_6585817, baseEnd_6585817] using wordTrace_append hprefix tailTrace_6585817
  have hstable : (prefixWord ++ tailWord_6585817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585817).length < 2 ^ (prefixWord ++ tailWord_6585817).sum := by decide
  have hdescent : baseEnd_6585817 < baseStart_6585817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585823 : List Nat := [1, 1, 2, 3, 3, 1, 3, 9]
def baseStart_6585823 : Nat := 118140960795 + 6585823 * 2 ^ 59
def prefixEnd_6585823 : Nat := 4983230072969 + 3 ^ 40 * 6585823 * 2
def baseEnd_6585823 : Nat := 125247877942055247071291

theorem tailTrace_6585823 : CollatzResearch.WordTrace tailWord_6585823 prefixEnd_6585823 125247877942055247071291 := by
  unfold tailWord_6585823
  simp only [CollatzResearch.WordTrace]
  refine ⟨240204698419695514866074123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160136465613130343244049415 240204698419695514866074123)
  ·
    refine ⟨360307047629543272299111185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240204698419695514866074123 360307047629543272299111185)
    ·
      refine ⟨270230285722157454224333389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360307047629543272299111185 270230285722157454224333389)
      ·
        refine ⟨101336357145809045334125021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270230285722157454224333389 101336357145809045334125021)
        ·
          refine ⟨38001133929678392000296883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101336357145809045334125021 38001133929678392000296883)
          ·
            refine ⟨57001700894517588000445325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38001133929678392000296883 57001700894517588000445325)
            ·
              refine ⟨21375637835444095500166997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57001700894517588000445325 21375637835444095500166997)
              ·
                refine ⟨125247877942055247071291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21375637835444095500166997 125247877942055247071291)
                ·
                  rfl

theorem cell23_6585823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 9].length) (baseStart_6585823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585823 prefixEnd_6585823 := by exact prefixLift 6585823
  have htrace : WordTrace (prefixWord ++ tailWord_6585823) baseStart_6585823 baseEnd_6585823 := by
    simpa [prefixWord, tailWord_6585823, baseEnd_6585823] using wordTrace_append hprefix tailTrace_6585823
  have hstable : (prefixWord ++ tailWord_6585823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585823).length < 2 ^ (prefixWord ++ tailWord_6585823).sum := by decide
  have hdescent : baseEnd_6585823 < baseStart_6585823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585917 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_6585917 : Nat := 118140960795 + 6585917 * 2 ^ 59
def prefixEnd_6585917 : Nat := 4983230072969 + 3 ^ 40 * 6585917 * 2
def baseEnd_6585917 : Nat := 1127246990539004767716475

theorem tailTrace_6585917 : CollatzResearch.WordTrace tailWord_6585917 prefixEnd_6585917 1127246990539004767716475 := by
  unfold tailWord_6585917
  simp only [CollatzResearch.WordTrace]
  refine ⟨240208126881354968919996005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160138751254236645946664003 240208126881354968919996005)
  ·
    refine ⟨45039023790254056672499251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240208126881354968919996005 45039023790254056672499251)
    ·
      refine ⟨67558535685381085008748877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45039023790254056672499251 67558535685381085008748877)
      ·
        refine ⟨25334450882017906878280829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67558535685381085008748877 25334450882017906878280829)
        ·
          refine ⟨9500419080756715079355311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25334450882017906878280829 9500419080756715079355311)
          ·
            refine ⟨14250628621135072619032967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9500419080756715079355311 14250628621135072619032967)
            ·
              refine ⟨21375942931702608928549451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14250628621135072619032967 21375942931702608928549451)
              ·
                refine ⟨32063914397553913392824177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21375942931702608928549451 32063914397553913392824177)
                ·
                  refine ⟨24047935798165435044618133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32063914397553913392824177 24047935798165435044618133)
                  ·
                    refine ⟨1127246990539004767716475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24047935798165435044618133 1127246990539004767716475)
                    ·
                      rfl

theorem cell23_6585917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_6585917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585917 prefixEnd_6585917 := by exact prefixLift 6585917
  have htrace : WordTrace (prefixWord ++ tailWord_6585917) baseStart_6585917 baseEnd_6585917 := by
    simpa [prefixWord, tailWord_6585917, baseEnd_6585917] using wordTrace_append hprefix tailTrace_6585917
  have hstable : (prefixWord ++ tailWord_6585917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585917).length < 2 ^ (prefixWord ++ tailWord_6585917).sum := by decide
  have hdescent : baseEnd_6585917 < baseStart_6585917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585930 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 7]
def baseStart_6585930 : Nat := 118140960795 + 6585930 * 2 ^ 59
def prefixEnd_6585930 : Nat := 4983230072969 + 3 ^ 40 * 6585930 * 2
def baseEnd_6585930 : Nat := 375749738540613639142985

theorem tailTrace_6585930 : CollatzResearch.WordTrace tailWord_6585930 prefixEnd_6585930 375749738540613639142985 := by
  unfold tailWord_6585930
  simp only [CollatzResearch.WordTrace]
  refine ⟨60052150257576968035054811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160139067353538581426812829 60052150257576968035054811)
  ·
    refine ⟨90078225386365452052582217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60052150257576968035054811 90078225386365452052582217)
    ·
      refine ⟨67558669039774089039436663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90078225386365452052582217 67558669039774089039436663)
      ·
        refine ⟨101338003559661133559154995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67558669039774089039436663 101338003559661133559154995)
        ·
          refine ⟨152007005339491700338732493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101338003559661133559154995 152007005339491700338732493)
          ·
            refine ⟨57002627002309387627024685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152007005339491700338732493 57002627002309387627024685)
            ·
              refine ⟨21375985125866020360134257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57002627002309387627024685 21375985125866020360134257)
              ·
                refine ⟨16031988844399515270100693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21375985125866020360134257 16031988844399515270100693)
                ·
                  refine ⟨375749738540613639142985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16031988844399515270100693 375749738540613639142985)
                  ·
                    rfl

theorem cell23_6585930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_6585930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585930 prefixEnd_6585930 := by exact prefixLift 6585930
  have htrace : WordTrace (prefixWord ++ tailWord_6585930) baseStart_6585930 baseEnd_6585930 := by
    simpa [prefixWord, tailWord_6585930, baseEnd_6585930] using wordTrace_append hprefix tailTrace_6585930
  have hstable : (prefixWord ++ tailWord_6585930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585930).length < 2 ^ (prefixWord ++ tailWord_6585930).sum := by decide
  have hdescent : baseEnd_6585930 < baseStart_6585930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585957 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_6585957 : Nat := 118140960795 + 6585957 * 2 ^ 59
def prefixEnd_6585957 : Nat := 4983230072969 + 3 ^ 40 * 6585957 * 2
def baseEnd_6585957 : Nat := 3381761510843194146649241

theorem tailTrace_6585957 : CollatzResearch.WordTrace tailWord_6585957 prefixEnd_6585957 3381761510843194146649241 := by
  unfold tailWord_6585957
  simp only [CollatzResearch.WordTrace]
  refine ⟨240209585801210055751452125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160139723867473370500968083 240209585801210055751452125)
  ·
    refine ⟨90078594675453770906794547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240209585801210055751452125 90078594675453770906794547)
    ·
      refine ⟨135117892013180656360191821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90078594675453770906794547 135117892013180656360191821)
      ·
        refine ⟨50669209504942746135071933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135117892013180656360191821 50669209504942746135071933)
        ·
          refine ⟨19000953564353529800651975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50669209504942746135071933 19000953564353529800651975)
          ·
            refine ⟨28501430346530294700977963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19000953564353529800651975 28501430346530294700977963)
            ·
              refine ⟨42752145519795442051466945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28501430346530294700977963 42752145519795442051466945)
              ·
                refine ⟨32064109139846581538600209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42752145519795442051466945 32064109139846581538600209)
                ·
                  refine ⟨24048081854884936153950157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32064109139846581538600209 24048081854884936153950157)
                  ·
                    refine ⟨9018030695581851057731309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24048081854884936153950157 9018030695581851057731309)
                    ·
                      refine ⟨3381761510843194146649241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9018030695581851057731309 3381761510843194146649241)
                      ·
                        rfl

theorem cell23_6585957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_6585957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585957 prefixEnd_6585957 := by exact prefixLift 6585957
  have htrace : WordTrace (prefixWord ++ tailWord_6585957) baseStart_6585957 baseEnd_6585957 := by
    simpa [prefixWord, tailWord_6585957, baseEnd_6585957] using wordTrace_append hprefix tailTrace_6585957
  have hstable : (prefixWord ++ tailWord_6585957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585957).length < 2 ^ (prefixWord ++ tailWord_6585957).sum := by decide
  have hdescent : baseEnd_6585957 < baseStart_6585957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585974 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_6585974 : Nat := 118140960795 + 6585974 * 2 ^ 59
def prefixEnd_6585974 : Nat := 4983230072969 + 3 ^ 40 * 6585974 * 2
def baseEnd_6585974 : Nat := 3381770240014320580136663

theorem tailTrace_6585974 : CollatzResearch.WordTrace tailWord_6585974 prefixEnd_6585974 3381770240014320580136663 := by
  unfold tailWord_6585974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15013137865134279228426311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160140137228098978436547317 15013137865134279228426311)
  ·
    refine ⟨22519706797701418842639467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15013137865134279228426311 22519706797701418842639467)
    ·
      refine ⟨33779560196552128263959201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22519706797701418842639467 33779560196552128263959201)
      ·
        refine ⟨25334670147414096197969401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33779560196552128263959201 25334670147414096197969401)
        ·
          refine ⟨19001002610560572148477051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25334670147414096197969401 19001002610560572148477051)
          ·
            refine ⟨28501503915840858222715577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19001002610560572148477051 28501503915840858222715577)
            ·
              refine ⟨21376127936880643667036683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28501503915840858222715577 21376127936880643667036683)
              ·
                refine ⟨32064191905320965500555025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21376127936880643667036683 32064191905320965500555025)
                ·
                  refine ⟨24048143928990724125416269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32064191905320965500555025 24048143928990724125416269)
                  ·
                    refine ⟨9018053973371521547031101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24048143928990724125416269 9018053973371521547031101)
                    ·
                      refine ⟨3381770240014320580136663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9018053973371521547031101 3381770240014320580136663)
                      ·
                        rfl

theorem cell23_6585974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_6585974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6585974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6585974 prefixEnd_6585974 := by exact prefixLift 6585974
  have htrace : WordTrace (prefixWord ++ tailWord_6585974) baseStart_6585974 baseEnd_6585974 := by
    simpa [prefixWord, tailWord_6585974, baseEnd_6585974] using wordTrace_append hprefix tailTrace_6585974
  have hstable : (prefixWord ++ tailWord_6585974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585974).length < 2 ^ (prefixWord ++ tailWord_6585974).sum := by decide
  have hdescent : baseEnd_6585974 < baseStart_6585974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586014 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_6586014 : Nat := 118140960795 + 6586014 * 2 ^ 59
def prefixEnd_6586014 : Nat := 4983230072969 + 3 ^ 40 * 6586014 * 2
def baseEnd_6586014 : Nat := 3381790779240500423636479

theorem tailTrace_6586014 : CollatzResearch.WordTrace tailWord_6586014 prefixEnd_6586014 3381790779240500423636479 := by
  unfold tailWord_6586014
  simp only [CollatzResearch.WordTrace]
  refine ⟨30026458095250444310784637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160141109841335702990851397 30026458095250444310784637)
  ·
    refine ⟨11259921785718916616544239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30026458095250444310784637 11259921785718916616544239)
    ·
      refine ⟨16889882678578374924816359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11259921785718916616544239 16889882678578374924816359)
      ·
        refine ⟨25334824017867562387224539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16889882678578374924816359 25334824017867562387224539)
        ·
          refine ⟨38002236026801343580836809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25334824017867562387224539 38002236026801343580836809)
          ·
            refine ⟨28501677020101007685627607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38002236026801343580836809 28501677020101007685627607)
            ·
              refine ⟨42752515530151511528441411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28501677020101007685627607 42752515530151511528441411)
              ·
                refine ⟨64128773295227267292662117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42752515530151511528441411 64128773295227267292662117)
                ·
                  refine ⟨12024144992855112617374147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64128773295227267292662117 12024144992855112617374147)
                  ·
                    refine ⟨18036217489282668926061221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12024144992855112617374147 18036217489282668926061221)
                    ·
                      refine ⟨3381790779240500423636479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18036217489282668926061221 3381790779240500423636479)
                      ·
                        rfl

theorem cell23_6586014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_6586014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586014 prefixEnd_6586014 := by exact prefixLift 6586014
  have htrace : WordTrace (prefixWord ++ tailWord_6586014) baseStart_6586014 baseEnd_6586014 := by
    simpa [prefixWord, tailWord_6586014, baseEnd_6586014] using wordTrace_append hprefix tailTrace_6586014
  have hstable : (prefixWord ++ tailWord_6586014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586014).length < 2 ^ (prefixWord ++ tailWord_6586014).sum := by decide
  have hdescent : baseEnd_6586014 < baseStart_6586014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586040 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_6586040 : Nat := 118140960795 + 6586040 * 2 ^ 59
def prefixEnd_6586040 : Nat := 4983230072969 + 3 ^ 40 * 6586040 * 2
def baseEnd_6586040 : Nat := 3381804129737517321911359

theorem tailTrace_6586040 : CollatzResearch.WordTrace tailWord_6586040 prefixEnd_6586040 3381804129737517321911359 := by
  unfold tailWord_6586040
  simp only [CollatzResearch.WordTrace]
  refine ⟨120106306529954680463361787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160141742039939573951149049 120106306529954680463361787)
  ·
    refine ⟨180159459794932020695042681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120106306529954680463361787 180159459794932020695042681)
    ·
      refine ⟨135119594846199015521282011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180159459794932020695042681 135119594846199015521282011)
      ·
        refine ⟨202679392269298523281923017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135119594846199015521282011 202679392269298523281923017)
        ·
          refine ⟨152009544201973892461442263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202679392269298523281923017 152009544201973892461442263)
          ·
            refine ⟨228014316302960838692163395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152009544201973892461442263 228014316302960838692163395)
            ·
              refine ⟨342021474454441258038245093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228014316302960838692163395 342021474454441258038245093)
              ·
                refine ⟨64129026460207735882170955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342021474454441258038245093 64129026460207735882170955)
                ·
                  refine ⟨96193539690311603823256433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64129026460207735882170955 96193539690311603823256433)
                  ·
                    refine ⟨72145154767733702867442325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96193539690311603823256433 72145154767733702867442325)
                    ·
                      refine ⟨3381804129737517321911359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72145154767733702867442325 3381804129737517321911359)
                      ·
                        rfl

theorem cell23_6586040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_6586040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586040 prefixEnd_6586040 := by exact prefixLift 6586040
  have htrace : WordTrace (prefixWord ++ tailWord_6586040) baseStart_6586040 baseEnd_6586040 := by
    simpa [prefixWord, tailWord_6586040, baseEnd_6586040] using wordTrace_append hprefix tailTrace_6586040
  have hstable : (prefixWord ++ tailWord_6586040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586040).length < 2 ^ (prefixWord ++ tailWord_6586040).sum := by decide
  have hdescent : baseEnd_6586040 < baseStart_6586040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586097 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 1, 6]
def baseStart_6586097 : Nat := 118140960795 + 6586097 * 2 ^ 59
def prefixEnd_6586097 : Nat := 4983230072969 + 3 ^ 40 * 6586097 * 2
def baseEnd_6586097 : Nat := 1127277799378274532966199

theorem tailTrace_6586097 : CollatzResearch.WordTrace tailWord_6586097 prefixEnd_6586097 1127277799378274532966199 := by
  unfold tailWord_6586097
  simp only [CollatzResearch.WordTrace]
  refine ⟨240214692020702859661548545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160143128013801906441032363 240214692020702859661548545)
  ·
    refine ⟨180161019015527144746161409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240214692020702859661548545 180161019015527144746161409)
    ·
      refine ⟨135120764261645358559621057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180161019015527144746161409 135120764261645358559621057)
      ·
        refine ⟨101340573196234018919715793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135120764261645358559621057 101340573196234018919715793)
        ·
          refine ⟨76005429897175514189786845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101340573196234018919715793 76005429897175514189786845)
          ·
            refine ⟨28502036211440817821170067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76005429897175514189786845 28502036211440817821170067)
            ·
              refine ⟨42753054317161226731755101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28502036211440817821170067 42753054317161226731755101)
              ·
                refine ⟨16032395368935460024408163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42753054317161226731755101 16032395368935460024408163)
                ·
                  refine ⟨24048593053403190036612245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16032395368935460024408163 24048593053403190036612245)
                  ·
                    refine ⟨1127277799378274532966199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24048593053403190036612245 1127277799378274532966199)
                    ·
                      rfl

theorem cell23_6586097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_6586097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586097 prefixEnd_6586097 := by exact prefixLift 6586097
  have htrace : WordTrace (prefixWord ++ tailWord_6586097) baseStart_6586097 baseEnd_6586097 := by
    simpa [prefixWord, tailWord_6586097, baseEnd_6586097] using wordTrace_append hprefix tailTrace_6586097
  have hstable : (prefixWord ++ tailWord_6586097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586097).length < 2 ^ (prefixWord ++ tailWord_6586097).sum := by decide
  have hdescent : baseEnd_6586097 < baseStart_6586097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586114 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6586114 : Nat := 118140960795 + 6586114 * 2 ^ 59
def prefixEnd_6586114 : Nat := 4983230072969 + 3 ^ 40 * 6586114 * 2
def baseEnd_6586114 : Nat := 1127280709101983344128673

theorem tailTrace_6586114 : CollatzResearch.WordTrace tailWord_6586114 prefixEnd_6586114 1127280709101983344128673 := by
  unfold tailWord_6586114
  simp only [CollatzResearch.WordTrace]
  refine ⟨60053828015410317891229349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160143541374427514376611597 60053828015410317891229349)
  ·
    refine ⟨11260092752889434604605503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60053828015410317891229349 11260092752889434604605503)
    ·
      refine ⟨16890139129334151906908255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11260092752889434604605503 16890139129334151906908255)
      ·
        refine ⟨25335208694001227860362383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16890139129334151906908255 25335208694001227860362383)
        ·
          refine ⟨38002813041001841790543575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25335208694001227860362383 38002813041001841790543575)
          ·
            refine ⟨57004219561502762685815363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38002813041001841790543575 57004219561502762685815363)
            ·
              refine ⟨85506329342254144028723045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57004219561502762685815363 85506329342254144028723045)
              ·
                refine ⟨16032436751672652005385571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85506329342254144028723045 16032436751672652005385571)
                ·
                  refine ⟨24048655127508978008078357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16032436751672652005385571 24048655127508978008078357)
                  ·
                    refine ⟨1127280709101983344128673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24048655127508978008078357 1127280709101983344128673)
                    ·
                      rfl

theorem cell23_6586114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6586114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586114 prefixEnd_6586114 := by exact prefixLift 6586114
  have htrace : WordTrace (prefixWord ++ tailWord_6586114) baseStart_6586114 baseEnd_6586114 := by
    simpa [prefixWord, tailWord_6586114, baseEnd_6586114] using wordTrace_append hprefix tailTrace_6586114
  have hstable : (prefixWord ++ tailWord_6586114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586114).length < 2 ^ (prefixWord ++ tailWord_6586114).sum := by decide
  have hdescent : baseEnd_6586114 < baseStart_6586114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586132 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6586132 : Nat := 118140960795 + 6586132 * 2 ^ 59
def prefixEnd_6586132 : Nat := 4983230072969 + 3 ^ 40 * 6586132 * 2
def baseEnd_6586132 : Nat := 3381851369957730961960937

theorem tailTrace_6586132 : CollatzResearch.WordTrace tailWord_6586132 prefixEnd_6586132 3381851369957730961960937 := by
  unfold tailWord_6586132
  simp only [CollatzResearch.WordTrace]
  refine ⟨120107984287788030319536325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160143979050384040426048433 120107984287788030319536325)
  ·
    refine ⟨22520247053960255684913061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120107984287788030319536325 22520247053960255684913061)
    ·
      refine ⟨4222546322617547940921199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22520247053960255684913061 4222546322617547940921199)
      ·
        refine ⟨6333819483926321911381799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222546322617547940921199 6333819483926321911381799)
        ·
          refine ⟨9500729225889482867072699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6333819483926321911381799 9500729225889482867072699)
          ·
            refine ⟨14251093838834224300609049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9500729225889482867072699 14251093838834224300609049)
            ·
              refine ⟨10688320379125668225456787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14251093838834224300609049 10688320379125668225456787)
              ·
                refine ⟨16032480568688502338185181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10688320379125668225456787 16032480568688502338185181)
                ·
                  refine ⟨6012180213258188376819443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16032480568688502338185181 6012180213258188376819443)
                  ·
                    refine ⟨9018270319887282565229165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6012180213258188376819443 9018270319887282565229165)
                    ·
                      refine ⟨3381851369957730961960937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9018270319887282565229165 3381851369957730961960937)
                      ·
                        rfl

theorem cell23_6586132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6586132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586132 prefixEnd_6586132 := by exact prefixLift 6586132
  have htrace : WordTrace (prefixWord ++ tailWord_6586132) baseStart_6586132 baseEnd_6586132 := by
    simpa [prefixWord, tailWord_6586132, baseEnd_6586132] using wordTrace_append hprefix tailTrace_6586132
  have hstable : (prefixWord ++ tailWord_6586132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586132).length < 2 ^ (prefixWord ++ tailWord_6586132).sum := by decide
  have hdescent : baseEnd_6586132 < baseStart_6586132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586138 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2]
def baseStart_6586138 : Nat := 118140960795 + 6586138 * 2 ^ 59
def prefixEnd_6586138 : Nat := 4983230072969 + 3 ^ 40 * 6586138 * 2
def baseEnd_6586138 : Nat := 3381854450841657938485909

theorem tailTrace_6586138 : CollatzResearch.WordTrace tailWord_6586138 prefixEnd_6586138 3381854450841657938485909 := by
  unfold tailWord_6586138
  simp only [CollatzResearch.WordTrace]
  refine ⟨60054046853388580915947767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160144124942369549109194045 60054046853388580915947767)
  ·
    refine ⟨90081070280082871373921651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60054046853388580915947767 90081070280082871373921651)
    ·
      refine ⟨135121605420124307060882477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90081070280082871373921651 135121605420124307060882477)
      ·
        refine ⟨50670602032546615147830929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135121605420124307060882477 50670602032546615147830929)
        ·
          refine ⟨38002951524409961360873197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50670602032546615147830929 38002951524409961360873197)
          ·
            refine ⟨14251106821653735510327449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38002951524409961360873197 14251106821653735510327449)
            ·
              refine ⟨10688330116240301632745587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14251106821653735510327449 10688330116240301632745587)
              ·
                refine ⟨16032495174360452449118381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10688330116240301632745587 16032495174360452449118381)
                ·
                  refine ⟨6012185690385169668419393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16032495174360452449118381 6012185690385169668419393)
                  ·
                    refine ⟨4509139267788877251314545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6012185690385169668419393 4509139267788877251314545)
                    ·
                      refine ⟨3381854450841657938485909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4509139267788877251314545 3381854450841657938485909)
                      ·
                        rfl

theorem cell23_6586138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_6586138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586138 prefixEnd_6586138 := by exact prefixLift 6586138
  have htrace : WordTrace (prefixWord ++ tailWord_6586138) baseStart_6586138 baseEnd_6586138 := by
    simpa [prefixWord, tailWord_6586138, baseEnd_6586138] using wordTrace_append hprefix tailTrace_6586138
  have hstable : (prefixWord ++ tailWord_6586138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586138).length < 2 ^ (prefixWord ++ tailWord_6586138).sum := by decide
  have hdescent : baseEnd_6586138 < baseStart_6586138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586148 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_6586148 : Nat := 118140960795 + 6586148 * 2 ^ 59
def prefixEnd_6586148 : Nat := 4983230072969 + 3 ^ 40 * 6586148 * 2
def baseEnd_6586148 : Nat := 1127286528549400966453621

theorem tailTrace_6586148 : CollatzResearch.WordTrace tailWord_6586148 prefixEnd_6586148 1127286528549400966453621 := by
  unfold tailWord_6586148
  simp only [CollatzResearch.WordTrace]
  refine ⟨120108276071759047685827549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160144368095678730247770065 120108276071759047685827549)
  ·
    refine ⟨45040603526909642882185331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120108276071759047685827549 45040603526909642882185331)
    ·
      refine ⟨67560905290364464323277997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45040603526909642882185331 67560905290364464323277997)
      ·
        refine ⟨25335339483886674121229249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67560905290364464323277997 25335339483886674121229249)
        ·
          refine ⟨19001504612915005590921937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25335339483886674121229249 19001504612915005590921937)
          ·
            refine ⟨14251128459686254193191453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19001504612915005590921937 14251128459686254193191453)
            ·
              refine ⟨5344173172382345322446795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14251128459686254193191453 5344173172382345322446795)
              ·
                refine ⟨8016259758573517983670193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344173172382345322446795 8016259758573517983670193)
                ·
                  refine ⟨6012194818930138487752645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8016259758573517983670193 6012194818930138487752645)
                  ·
                    refine ⟨1127286528549400966453621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6012194818930138487752645 1127286528549400966453621)
                    ·
                      rfl

theorem cell23_6586148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_6586148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586148 prefixEnd_6586148 := by exact prefixLift 6586148
  have htrace : WordTrace (prefixWord ++ tailWord_6586148) baseStart_6586148 baseEnd_6586148 := by
    simpa [prefixWord, tailWord_6586148, baseEnd_6586148] using wordTrace_append hprefix tailTrace_6586148
  have hstable : (prefixWord ++ tailWord_6586148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586148).length < 2 ^ (prefixWord ++ tailWord_6586148).sum := by decide
  have hdescent : baseEnd_6586148 < baseStart_6586148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586181 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 1, 3, 2]
def baseStart_6586181 : Nat := 118140960795 + 6586181 * 2 ^ 59
def prefixEnd_6586181 : Nat := 4983230072969 + 3 ^ 40 * 6586181 * 2
def baseEnd_6586181 : Nat := 3381876530509801270248211

theorem tailTrace_6586181 : CollatzResearch.WordTrace tailWord_6586181 prefixEnd_6586181 3381876530509801270248211 := by
  unfold tailWord_6586181
  simp only [CollatzResearch.WordTrace]
  refine ⟨240217755752398542007606397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160145170501599028005070931 240217755752398542007606397)
  ·
    refine ⟨90081658407149453252852399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240217755752398542007606397 90081658407149453252852399)
    ·
      refine ⟨135122487610724179879278599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90081658407149453252852399 135122487610724179879278599)
      ·
        refine ⟨202683731416086269818917899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135122487610724179879278599 202683731416086269818917899)
        ·
          refine ⟨304025597124129404728376849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202683731416086269818917899 304025597124129404728376849)
          ·
            refine ⟨228019197843097053546282637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304025597124129404728376849 228019197843097053546282637)
            ·
              refine ⟨85507199191161395079855989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228019197843097053546282637 85507199191161395079855989)
              ·
                refine ⟨8016299924171380788736499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85507199191161395079855989 8016299924171380788736499)
                ·
                  refine ⟨12024449886257071183104749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8016299924171380788736499 12024449886257071183104749)
                  ·
                    refine ⟨4509168707346401693664281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12024449886257071183104749 4509168707346401693664281)
                    ·
                      refine ⟨3381876530509801270248211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4509168707346401693664281 3381876530509801270248211)
                      ·
                        rfl

theorem cell23_6586181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_6586181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586181 prefixEnd_6586181 := by exact prefixLift 6586181
  have htrace : WordTrace (prefixWord ++ tailWord_6586181) baseStart_6586181 baseEnd_6586181 := by
    simpa [prefixWord, tailWord_6586181, baseEnd_6586181] using wordTrace_append hprefix tailTrace_6586181
  have hstable : (prefixWord ++ tailWord_6586181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586181).length < 2 ^ (prefixWord ++ tailWord_6586181).sum := by decide
  have hdescent : baseEnd_6586181 < baseStart_6586181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586189 : List Nat := [1, 6, 1, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6586189 : Nat := 118140960795 + 6586189 * 2 ^ 59
def prefixEnd_6586189 : Nat := 4983230072969 + 3 ^ 40 * 6586189 * 2
def baseEnd_6586189 : Nat := 3381880638355037238948175

theorem tailTrace_6586189 : CollatzResearch.WordTrace tailWord_6586189 prefixEnd_6586189 3381880638355037238948175 := by
  unfold tailWord_6586189
  simp only [CollatzResearch.WordTrace]
  refine ⟨240218047536369559373897621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160145365024246372915931747 240218047536369559373897621)
  ·
    refine ⟨11260220978267323095651451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240218047536369559373897621 11260220978267323095651451)
    ·
      refine ⟨16890331467400984643477177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11260220978267323095651451 16890331467400984643477177)
      ·
        refine ⟨12667748600550738482607883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16890331467400984643477177 12667748600550738482607883)
        ·
          refine ⟨19001622900826107723911825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12667748600550738482607883 19001622900826107723911825)
          ·
            refine ⟨14251217175619580792933869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19001622900826107723911825 14251217175619580792933869)
            ·
              refine ⟨5344206440857342797350201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14251217175619580792933869 5344206440857342797350201)
              ·
                refine ⟨4008154830643007098012651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5344206440857342797350201 4008154830643007098012651)
                ·
                  refine ⟨6012232245964510647018977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4008154830643007098012651 6012232245964510647018977)
                  ·
                    refine ⟨4509174184473382985264233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6012232245964510647018977 4509174184473382985264233)
                    ·
                      refine ⟨3381880638355037238948175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4509174184473382985264233 3381880638355037238948175)
                      ·
                        rfl

theorem cell23_6586189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6586189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586189 prefixEnd_6586189 := by exact prefixLift 6586189
  have htrace : WordTrace (prefixWord ++ tailWord_6586189) baseStart_6586189 baseEnd_6586189 := by
    simpa [prefixWord, tailWord_6586189, baseEnd_6586189] using wordTrace_append hprefix tailTrace_6586189
  have hstable : (prefixWord ++ tailWord_6586189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586189).length < 2 ^ (prefixWord ++ tailWord_6586189).sum := by decide
  have hdescent : baseEnd_6586189 < baseStart_6586189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586217 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 7]
def baseStart_6586217 : Nat := 118140960795 + 6586217 * 2 ^ 59
def prefixEnd_6586217 : Nat := 4983230072969 + 3 ^ 40 * 6586217 * 2
def baseEnd_6586217 : Nat := 375766112868151458822005

theorem tailTrace_6586217 : CollatzResearch.WordTrace tailWord_6586217 prefixEnd_6586217 375766112868151458822005 := by
  unfold tailWord_6586217
  simp only [CollatzResearch.WordTrace]
  refine ⟨240219068780268120155916905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160146045853512080103944603 240219068780268120155916905)
  ·
    refine ⟨180164301585201090116937679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240219068780268120155916905 180164301585201090116937679)
    ·
      refine ⟨270246452377801635175406519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180164301585201090116937679 270246452377801635175406519)
      ·
        refine ⟨405369678566702452763109779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270246452377801635175406519 405369678566702452763109779)
        ·
          refine ⟨608054517850053679144664669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405369678566702452763109779 608054517850053679144664669)
          ·
            refine ⟨228020444193770129679249251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 608054517850053679144664669 228020444193770129679249251)
            ·
              refine ⟨342030666290655194518873877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228020444193770129679249251 342030666290655194518873877)
              ·
                refine ⟨16032687482374462243072213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 342030666290655194518873877 16032687482374462243072213)
                ·
                  refine ⟨375766112868151458822005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16032687482374462243072213 375766112868151458822005)
                  ·
                    rfl

theorem cell23_6586217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 7].length) (baseStart_6586217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586217 prefixEnd_6586217 := by exact prefixLift 6586217
  have htrace : WordTrace (prefixWord ++ tailWord_6586217) baseStart_6586217 baseEnd_6586217 := by
    simpa [prefixWord, tailWord_6586217, baseEnd_6586217] using wordTrace_append hprefix tailTrace_6586217
  have hstable : (prefixWord ++ tailWord_6586217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586217).length < 2 ^ (prefixWord ++ tailWord_6586217).sum := by decide
  have hdescent : baseEnd_6586217 < baseStart_6586217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586418 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_6586418 : Nat := 118140960795 + 6586418 * 2 ^ 59
def prefixEnd_6586418 : Nat := 4983230072969 + 3 ^ 40 * 6586418 * 2
def baseEnd_6586418 : Nat := 1127332741808305614328207

theorem tailTrace_6586418 : CollatzResearch.WordTrace tailWord_6586418 prefixEnd_6586418 1127332741808305614328207 := by
  unfold tailWord_6586418
  simp only [CollatzResearch.WordTrace]
  refine ⟨60056599963134982870995977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160150933235026620989322605 60056599963134982870995977)
  ·
    refine ⟨45042449972351237153246983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60056599963134982870995977 45042449972351237153246983)
    ·
      refine ⟨67563674958526855729870475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45042449972351237153246983 67563674958526855729870475)
      ·
        refine ⟨101345512437790283594805713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67563674958526855729870475 101345512437790283594805713)
        ·
          refine ⟨76009134328342712696104285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101345512437790283594805713 76009134328342712696104285)
          ·
            refine ⟨28503425373128517261039107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76009134328342712696104285 28503425373128517261039107)
            ·
              refine ⟨42755138059692775891558661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28503425373128517261039107 42755138059692775891558661)
              ·
                refine ⟨8016588386192395479667249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42755138059692775891558661 8016588386192395479667249)
                ·
                  refine ⟨6012441289644296609750437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8016588386192395479667249 6012441289644296609750437)
                  ·
                    refine ⟨1127332741808305614328207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6012441289644296609750437 1127332741808305614328207)
                    ·
                      rfl

theorem cell23_6586418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_6586418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586418 prefixEnd_6586418 := by exact prefixLift 6586418
  have htrace : WordTrace (prefixWord ++ tailWord_6586418) baseStart_6586418 baseEnd_6586418 := by
    simpa [prefixWord, tailWord_6586418, baseEnd_6586418] using wordTrace_append hprefix tailTrace_6586418
  have hstable : (prefixWord ++ tailWord_6586418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586418).length < 2 ^ (prefixWord ++ tailWord_6586418).sum := by decide
  have hdescent : baseEnd_6586418 < baseStart_6586418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586445 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_6586445 : Nat := 118140960795 + 6586445 * 2 ^ 59
def prefixEnd_6586445 : Nat := 4983230072969 + 3 ^ 40 * 6586445 * 2
def baseEnd_6586445 : Nat := 3382012089402588237346997

theorem tailTrace_6586445 : CollatzResearch.WordTrace tailWord_6586445 prefixEnd_6586445 3382012089402588237346997 := by
  unfold tailWord_6586445
  simp only [CollatzResearch.WordTrace]
  refine ⟨240227384623442115095216789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160151589748961410063477859 240227384623442115095216789)
  ·
    refine ⟨11260658654223849145088287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240227384623442115095216789 11260658654223849145088287)
    ·
      refine ⟨16890987981335773717632431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11260658654223849145088287 16890987981335773717632431)
      ·
        refine ⟨25336481972003660576448647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16890987981335773717632431 25336481972003660576448647)
        ·
          refine ⟨38004722958005490864672971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25336481972003660576448647 38004722958005490864672971)
          ·
            refine ⟨57007084437008236297009457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38004722958005490864672971 57007084437008236297009457)
            ·
              refine ⟨42755313327756177222757093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57007084437008236297009457 42755313327756177222757093)
              ·
                refine ⟨8016621248954283229266955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42755313327756177222757093 8016621248954283229266955)
                ·
                  refine ⟨12024931873431424843900433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8016621248954283229266955 12024931873431424843900433)
                  ·
                    refine ⟨9018698905073568632925325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12024931873431424843900433 9018698905073568632925325)
                    ·
                      refine ⟨3382012089402588237346997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9018698905073568632925325 3382012089402588237346997)
                      ·
                        rfl

theorem cell23_6586445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_6586445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586445 prefixEnd_6586445 := by exact prefixLift 6586445
  have htrace : WordTrace (prefixWord ++ tailWord_6586445) baseStart_6586445 baseEnd_6586445 := by
    simpa [prefixWord, tailWord_6586445, baseEnd_6586445] using wordTrace_append hprefix tailTrace_6586445
  have hstable : (prefixWord ++ tailWord_6586445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586445).length < 2 ^ (prefixWord ++ tailWord_6586445).sum := by decide
  have hdescent : baseEnd_6586445 < baseStart_6586445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586458 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_6586458 : Nat := 118140960795 + 6586458 * 2 ^ 59
def prefixEnd_6586458 : Nat := 4983230072969 + 3 ^ 40 * 6586458 * 2
def baseEnd_6586458 : Nat := 3382018764651096686484437

theorem tailTrace_6586458 : CollatzResearch.WordTrace tailWord_6586458 prefixEnd_6586458 3382018764651096686484437 := by
  unfold tailWord_6586458
  simp only [CollatzResearch.WordTrace]
  refine ⟨60056964693098754578860007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160151905848263345543626685 60056964693098754578860007)
  ·
    refine ⟨90085447039648131868290011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60056964693098754578860007 90085447039648131868290011)
    ·
      refine ⟨135128170559472197802435017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90085447039648131868290011 135128170559472197802435017)
      ·
        refine ⟨101346127919604148351826263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135128170559472197802435017 101346127919604148351826263)
        ·
          refine ⟨152019191879406222527739395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101346127919604148351826263 152019191879406222527739395)
          ·
            refine ⟨228028787819109333791609093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152019191879406222527739395 228028787819109333791609093)
            ·
              refine ⟨42755397716083000085926705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228028787819109333791609093 42755397716083000085926705)
              ·
                refine ⟨32066548287062250064445029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42755397716083000085926705 32066548287062250064445029)
                ·
                  refine ⟨6012477803824171887083443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32066548287062250064445029 6012477803824171887083443)
                  ·
                    refine ⟨9018716705736257830625165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6012477803824171887083443 9018716705736257830625165)
                    ·
                      refine ⟨3382018764651096686484437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9018716705736257830625165 3382018764651096686484437)
                      ·
                        rfl

theorem cell23_6586458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_6586458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586458 prefixEnd_6586458 := by exact prefixLift 6586458
  have htrace : WordTrace (prefixWord ++ tailWord_6586458) baseStart_6586458 baseEnd_6586458 := by
    simpa [prefixWord, tailWord_6586458, baseEnd_6586458] using wordTrace_append hprefix tailTrace_6586458
  have hstable : (prefixWord ++ tailWord_6586458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586458).length < 2 ^ (prefixWord ++ tailWord_6586458).sum := by decide
  have hdescent : baseEnd_6586458 < baseStart_6586458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586492 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_6586492 : Nat := 118140960795 + 6586492 * 2 ^ 59
def prefixEnd_6586492 : Nat := 4983230072969 + 3 ^ 40 * 6586492 * 2
def baseEnd_6586492 : Nat := 3382036222993349553459281

theorem tailTrace_6586492 : CollatzResearch.WordTrace tailWord_6586492 prefixEnd_6586492 3382036222993349553459281 := by
  unfold tailWord_6586492
  simp only [CollatzResearch.WordTrace]
  refine ⟨120114549427135921061088865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160152732569514561414785153 120114549427135921061088865)
  ·
    refine ⟨90085912070351940795816649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120114549427135921061088865 90085912070351940795816649)
    ·
      refine ⟨67564434052763955596862487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90085912070351940795816649 67564434052763955596862487)
      ·
        refine ⟨101346651079145933395293731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67564434052763955596862487 101346651079145933395293731)
        ·
          refine ⟨152019976618718900092940597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101346651079145933395293731 152019976618718900092940597)
          ·
            refine ⟨14251872808004896883713181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152019976618718900092940597 14251872808004896883713181)
            ·
              refine ⟨5344452303001836331392443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14251872808004896883713181 5344452303001836331392443)
              ·
                refine ⟨8016678454502754497088665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344452303001836331392443 8016678454502754497088665)
                ·
                  refine ⟨6012508840877065872816499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8016678454502754497088665 6012508840877065872816499)
                  ·
                    refine ⟨9018763261315598809224749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6012508840877065872816499 9018763261315598809224749)
                    ·
                      refine ⟨3382036222993349553459281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9018763261315598809224749 3382036222993349553459281)
                      ·
                        rfl

theorem cell23_6586492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_6586492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586492 prefixEnd_6586492 := by exact prefixLift 6586492
  have htrace : WordTrace (prefixWord ++ tailWord_6586492) baseStart_6586492 baseEnd_6586492 := by
    simpa [prefixWord, tailWord_6586492, baseEnd_6586492] using wordTrace_append hprefix tailTrace_6586492
  have hstable : (prefixWord ++ tailWord_6586492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586492).length < 2 ^ (prefixWord ++ tailWord_6586492).sum := by decide
  have hdescent : baseEnd_6586492 < baseStart_6586492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586578 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6586578 : Nat := 118140960795 + 6586578 * 2 ^ 59
def prefixEnd_6586578 : Nat := 4983230072969 + 3 ^ 40 * 6586578 * 2
def baseEnd_6586578 : Nat := 3382080382329636216983885

theorem tailTrace_6586578 : CollatzResearch.WordTrace tailWord_6586578 prefixEnd_6586578 3382080382329636216983885 := by
  unfold tailWord_6586578
  simp only [CollatzResearch.WordTrace]
  refine ⟨60058058882990069702452097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160154823687973519206538925 60058058882990069702452097)
  ·
    refine ⟨45043544162242552276839073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60058058882990069702452097 45043544162242552276839073)
    ·
      refine ⟨33782658121681914207629305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45043544162242552276839073 33782658121681914207629305)
      ·
        refine ⟨25336993591261435655721979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33782658121681914207629305 25336993591261435655721979)
        ·
          refine ⟨38005490386892153483582969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25336993591261435655721979 38005490386892153483582969)
          ·
            refine ⟨28504117790169115112687227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38005490386892153483582969 28504117790169115112687227)
            ·
              refine ⟨42756176685253672669030841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28504117790169115112687227 42756176685253672669030841)
              ·
                refine ⟨32067132513940254501773131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42756176685253672669030841 32067132513940254501773131)
                ·
                  refine ⟨48100698770910381752659697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32067132513940254501773131 48100698770910381752659697)
                  ·
                    refine ⟨36075524078182786314494773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48100698770910381752659697 36075524078182786314494773)
                    ·
                      refine ⟨3382080382329636216983885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36075524078182786314494773 3382080382329636216983885)
                      ·
                        rfl

theorem cell23_6586578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6586578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586578 prefixEnd_6586578 := by exact prefixLift 6586578
  have htrace : WordTrace (prefixWord ++ tailWord_6586578) baseStart_6586578 baseEnd_6586578 := by
    simpa [prefixWord, tailWord_6586578, baseEnd_6586578] using wordTrace_append hprefix tailTrace_6586578
  have hstable : (prefixWord ++ tailWord_6586578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586578).length < 2 ^ (prefixWord ++ tailWord_6586578).sum := by decide
  have hdescent : baseEnd_6586578 < baseStart_6586578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586589 : List Nat := [1, 4, 3, 2, 1, 3, 2, 2, 5]
def baseStart_6586589 : Nat := 118140960795 + 6586589 * 2 ^ 59
def prefixEnd_6586589 : Nat := 4983230072969 + 3 ^ 40 * 6586589 * 2
def baseEnd_6586589 : Nat := 375787336735203963771815

theorem tailTrace_6586589 : CollatzResearch.WordTrace tailWord_6586589 prefixEnd_6586589 375787336735203963771815 := by
  unfold tailWord_6586589
  simp only [CollatzResearch.WordTrace]
  refine ⟨240232636734920427688458821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160155091156613618458972547 240232636734920427688458821)
  ·
    refine ⟨45043619387797580191586029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240232636734920427688458821 45043619387797580191586029)
    ·
      refine ⟨16891357270424092571844761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45043619387797580191586029 16891357270424092571844761)
      ·
        refine ⟨12668517952818069428883571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16891357270424092571844761 12668517952818069428883571)
        ·
          refine ⟨19002776929227104143325357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12668517952818069428883571 19002776929227104143325357)
          ·
            refine ⟨7126041348460164053747009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19002776929227104143325357 7126041348460164053747009)
            ·
              refine ⟨5344531011345123040310257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7126041348460164053747009 5344531011345123040310257)
              ·
                refine ⟨4008398258508842280232693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5344531011345123040310257 4008398258508842280232693)
                ·
                  refine ⟨375787336735203963771815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4008398258508842280232693 375787336735203963771815)
                  ·
                    rfl

theorem cell23_6586589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_6586589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586589 prefixEnd_6586589 := by exact prefixLift 6586589
  have htrace : WordTrace (prefixWord ++ tailWord_6586589) baseStart_6586589 baseEnd_6586589 := by
    simpa [prefixWord, tailWord_6586589, baseEnd_6586589] using wordTrace_append hprefix tailTrace_6586589
  have hstable : (prefixWord ++ tailWord_6586589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586589).length < 2 ^ (prefixWord ++ tailWord_6586589).sum := by decide
  have hdescent : baseEnd_6586589 < baseStart_6586589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586591 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_6586591 : Nat := 118140960795 + 6586591 * 2 ^ 59
def prefixEnd_6586591 : Nat := 4983230072969 + 3 ^ 40 * 6586591 * 2
def baseEnd_6586591 : Nat := 3382087057578144666121325

theorem tailTrace_6586591 : CollatzResearch.WordTrace tailWord_6586591 prefixEnd_6586591 3382087057578144666121325 := by
  unfold tailWord_6586591
  simp only [CollatzResearch.WordTrace]
  refine ⟨240232709680913182030031627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160155139787275454686687751 240232709680913182030031627)
  ·
    refine ⟨360349064521369773045047441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240232709680913182030031627 360349064521369773045047441)
    ·
      refine ⟨270261798391027329783785581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360349064521369773045047441 270261798391027329783785581)
      ·
        refine ⟨101348174396635248668919593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270261798391027329783785581 101348174396635248668919593)
        ·
          refine ⟨76011130797476436501689695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101348174396635248668919593 76011130797476436501689695)
          ·
            refine ⟨114016696196214654752534543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76011130797476436501689695 114016696196214654752534543)
            ·
              refine ⟨171025044294321982128801815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114016696196214654752534543 171025044294321982128801815)
              ·
                refine ⟨256537566441482973193202723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171025044294321982128801815 256537566441482973193202723)
                ·
                  refine ⟨384806349662224459789804085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256537566441482973193202723 384806349662224459789804085)
                  ·
                    refine ⟨36075595280833543105294133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 384806349662224459789804085 36075595280833543105294133)
                    ·
                      refine ⟨3382087057578144666121325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36075595280833543105294133 3382087057578144666121325)
                      ·
                        rfl

theorem cell23_6586591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_6586591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586591 prefixEnd_6586591 := by exact prefixLift 6586591
  have htrace : WordTrace (prefixWord ++ tailWord_6586591) baseStart_6586591 baseEnd_6586591 := by
    simpa [prefixWord, tailWord_6586591, baseEnd_6586591] using wordTrace_append hprefix tailTrace_6586591
  have hstable : (prefixWord ++ tailWord_6586591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586591).length < 2 ^ (prefixWord ++ tailWord_6586591).sum := by decide
  have hdescent : baseEnd_6586591 < baseStart_6586591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586601 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_6586601 : Nat := 118140960795 + 6586601 * 2 ^ 59
def prefixEnd_6586601 : Nat := 4983230072969 + 3 ^ 40 * 6586601 * 2
def baseEnd_6586601 : Nat := 3382092192384689626996279

theorem tailTrace_6586601 : CollatzResearch.WordTrace tailWord_6586601 prefixEnd_6586601 3382092192384689626996279 := by
  unfold tailWord_6586601
  simp only [CollatzResearch.WordTrace]
  refine ⟨240233074410876953737895657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160155382940584635825263771 240233074410876953737895657)
  ·
    refine ⟨180174805808157715303421743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240233074410876953737895657 180174805808157715303421743)
    ·
      refine ⟨270262208712236572955132615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180174805808157715303421743 270262208712236572955132615)
      ·
        refine ⟨405393313068354859432698923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270262208712236572955132615 405393313068354859432698923)
        ·
          refine ⟨608089969602532289149048385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405393313068354859432698923 608089969602532289149048385)
          ·
            refine ⟨456067477201899216861786289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608089969602532289149048385 456067477201899216861786289)
            ·
              refine ⟨342050607901424412646339717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456067477201899216861786289 342050607901424412646339717)
              ·
                refine ⟨64134488981517077371188697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342050607901424412646339717 64134488981517077371188697)
                ·
                  refine ⟨48100866736137808028391523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64134488981517077371188697 48100866736137808028391523)
                  ·
                    refine ⟨72151300104206712042587285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48100866736137808028391523 72151300104206712042587285)
                    ·
                      refine ⟨3382092192384689626996279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72151300104206712042587285 3382092192384689626996279)
                      ·
                        rfl

theorem cell23_6586601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_6586601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586601 prefixEnd_6586601 := by exact prefixLift 6586601
  have htrace : WordTrace (prefixWord ++ tailWord_6586601) baseStart_6586601 baseEnd_6586601 := by
    simpa [prefixWord, tailWord_6586601, baseEnd_6586601] using wordTrace_append hprefix tailTrace_6586601
  have hstable : (prefixWord ++ tailWord_6586601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586601).length < 2 ^ (prefixWord ++ tailWord_6586601).sum := by decide
  have hdescent : baseEnd_6586601 < baseStart_6586601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586608 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 3]
def baseStart_6586608 : Nat := 118140960795 + 6586608 * 2 ^ 59
def prefixEnd_6586608 : Nat := 4983230072969 + 3 ^ 40 * 6586608 * 2
def baseEnd_6586608 : Nat := 3382095786749271099608747

theorem tailTrace_6586608 : CollatzResearch.WordTrace tailWord_6586608 prefixEnd_6586608 3382095786749271099608747 := by
  unfold tailWord_6586608
  simp only [CollatzResearch.WordTrace]
  refine ⟨120116664860925796966700239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160155553147901062622266985 120116664860925796966700239)
  ·
    refine ⟨180174997291388695450050359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120116664860925796966700239 180174997291388695450050359)
    ·
      refine ⟨270262495937083043175075539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180174997291388695450050359 270262495937083043175075539)
      ·
        refine ⟨405393743905624564762613309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270262495937083043175075539 405393743905624564762613309)
        ·
          refine ⟨152022653964609211785979991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405393743905624564762613309 152022653964609211785979991)
          ·
            refine ⟨228033980946913817678969987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152022653964609211785979991 228033980946913817678969987)
            ·
              refine ⟨342050971420370726518454981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228033980946913817678969987 342050971420370726518454981)
              ·
                refine ⟨64134557141319511222210309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342050971420370726518454981 64134557141319511222210309)
                ·
                  refine ⟨12025229463997408354164433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64134557141319511222210309 12025229463997408354164433)
                  ·
                    refine ⟨9018922097998056265623325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12025229463997408354164433 9018922097998056265623325)
                    ·
                      refine ⟨3382095786749271099608747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9018922097998056265623325 3382095786749271099608747)
                      ·
                        rfl

theorem cell23_6586608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_6586608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586608 prefixEnd_6586608 := by exact prefixLift 6586608
  have htrace : WordTrace (prefixWord ++ tailWord_6586608) baseStart_6586608 baseEnd_6586608 := by
    simpa [prefixWord, tailWord_6586608, baseEnd_6586608] using wordTrace_append hprefix tailTrace_6586608
  have hstable : (prefixWord ++ tailWord_6586608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586608).length < 2 ^ (prefixWord ++ tailWord_6586608).sum := by decide
  have hdescent : baseEnd_6586608 < baseStart_6586608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586632 : List Nat := [2, 1, 3, 2, 3, 1, 1, 5, 1, 4]
def baseStart_6586632 : Nat := 118140960795 + 6586632 * 2 ^ 59
def prefixEnd_6586632 : Nat := 4983230072969 + 3 ^ 40 * 6586632 * 2
def baseEnd_6586632 : Nat := 1127369370094993001902879

theorem tailTrace_6586632 : CollatzResearch.WordTrace tailWord_6586632 prefixEnd_6586632 1127369370094993001902879 := by
  unfold tailWord_6586632
  simp only [CollatzResearch.WordTrace]
  refine ⟨120117102536882323016137075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160156136715843097354849433 120117102536882323016137075)
  ·
    refine ⟨180175653805323484524205613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120117102536882323016137075 180175653805323484524205613)
    ·
      refine ⟨67565870176996306696577105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180175653805323484524205613 67565870176996306696577105)
      ·
        refine ⟨50674402632747230022432829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67565870176996306696577105 50674402632747230022432829)
        ·
          refine ⟨19002900987280211258412311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50674402632747230022432829 19002900987280211258412311)
          ·
            refine ⟨28504351480920316887618467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19002900987280211258412311 28504351480920316887618467)
            ·
              refine ⟨42756527221380475331427701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28504351480920316887618467 42756527221380475331427701)
              ·
                refine ⟨4008424427004419562321347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42756527221380475331427701 4008424427004419562321347)
                ·
                  refine ⟨6012636640506629343482021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4008424427004419562321347 6012636640506629343482021)
                  ·
                    refine ⟨1127369370094993001902879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6012636640506629343482021 1127369370094993001902879)
                    ·
                      rfl

theorem cell23_6586632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_6586632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586632 prefixEnd_6586632 := by exact prefixLift 6586632
  have htrace : WordTrace (prefixWord ++ tailWord_6586632) baseStart_6586632 baseEnd_6586632 := by
    simpa [prefixWord, tailWord_6586632, baseEnd_6586632] using wordTrace_append hprefix tailTrace_6586632
  have hstable : (prefixWord ++ tailWord_6586632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586632).length < 2 ^ (prefixWord ++ tailWord_6586632).sum := by decide
  have hdescent : baseEnd_6586632 < baseStart_6586632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586675 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 1, 5]
def baseStart_6586675 : Nat := 118140960795 + 6586675 * 2 ^ 59
def prefixEnd_6586675 : Nat := 4983230072969 + 3 ^ 40 * 6586675 * 2
def baseEnd_6586675 : Nat := 1127376729984374112490313

theorem tailTrace_6586675 : CollatzResearch.WordTrace tailWord_6586675 prefixEnd_6586675 1127376729984374112490313 := by
  unfold tailWord_6586675
  simp only [CollatzResearch.WordTrace]
  refine ⟨240235773412608864376089479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160157182275072576250726319 240235773412608864376089479)
  ·
    refine ⟨360353660118913296564134219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240235773412608864376089479 360353660118913296564134219)
    ·
      refine ⟨540530490178369944846201329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360353660118913296564134219 540530490178369944846201329)
      ·
        refine ⟨405397867633777458634650997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540530490178369944846201329 405397867633777458634650997)
        ·
          refine ⟨38006050090666636746998531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 405397867633777458634650997 38006050090666636746998531)
          ·
            refine ⟨57009075135999955120497797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38006050090666636746998531 57009075135999955120497797)
            ·
              refine ⟨10689201587999991585093337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57009075135999955120497797 10689201587999991585093337)
              ·
                refine ⟨8016901190999993688820003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10689201587999991585093337 8016901190999993688820003)
                ·
                  refine ⟨12025351786499990533230005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8016901190999993688820003 12025351786499990533230005)
                  ·
                    refine ⟨1127376729984374112490313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12025351786499990533230005 1127376729984374112490313)
                    ·
                      rfl

theorem cell23_6586675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 5].length) (baseStart_6586675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586675 prefixEnd_6586675 := by exact prefixLift 6586675
  have htrace : WordTrace (prefixWord ++ tailWord_6586675) baseStart_6586675 baseEnd_6586675 := by
    simpa [prefixWord, tailWord_6586675, baseEnd_6586675] using wordTrace_append hprefix tailTrace_6586675
  have hstable : (prefixWord ++ tailWord_6586675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586675).length < 2 ^ (prefixWord ++ tailWord_6586675).sum := by decide
  have hdescent : baseEnd_6586675 < baseStart_6586675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586695 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_6586695 : Nat := 118140960795 + 6586695 * 2 ^ 59
def prefixEnd_6586695 : Nat := 4983230072969 + 3 ^ 40 * 6586695 * 2
def baseEnd_6586695 : Nat := 3382140459566212259220847

theorem tailTrace_6586695 : CollatzResearch.WordTrace tailWord_6586695 prefixEnd_6586695 3382140459566212259220847 := by
  unfold tailWord_6586695
  simp only [CollatzResearch.WordTrace]
  refine ⟨240236502872536407791817539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160157668581690938527878359 240236502872536407791817539)
  ·
    refine ⟨360354754308804611687726309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240236502872536407791817539 360354754308804611687726309)
    ·
      refine ⟨67566516432900864691448683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360354754308804611687726309 67566516432900864691448683)
      ·
        refine ⟨101349774649351297037173025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67566516432900864691448683 101349774649351297037173025)
        ·
          refine ⟨76012330987013472777879769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101349774649351297037173025 76012330987013472777879769)
          ·
            refine ⟨57009248240260104583409827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76012330987013472777879769 57009248240260104583409827)
            ·
              refine ⟨85513872360390156875114741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57009248240260104583409827 85513872360390156875114741)
              ·
                refine ⟨8016925533786577207042007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85513872360390156875114741 8016925533786577207042007)
                ·
                  refine ⟨12025388300679865810563011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8016925533786577207042007 12025388300679865810563011)
                  ·
                    refine ⟨18038082451019798715844517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12025388300679865810563011 18038082451019798715844517)
                    ·
                      refine ⟨3382140459566212259220847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18038082451019798715844517 3382140459566212259220847)
                      ·
                        rfl

theorem cell23_6586695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_6586695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586695 prefixEnd_6586695 := by exact prefixLift 6586695
  have htrace : WordTrace (prefixWord ++ tailWord_6586695) baseStart_6586695 baseEnd_6586695 := by
    simpa [prefixWord, tailWord_6586695, baseEnd_6586695] using wordTrace_append hprefix tailTrace_6586695
  have hstable : (prefixWord ++ tailWord_6586695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586695).length < 2 ^ (prefixWord ++ tailWord_6586695).sum := by decide
  have hdescent : baseEnd_6586695 < baseStart_6586695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586705 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 4, 4]
def baseStart_6586705 : Nat := 118140960795 + 6586705 * 2 ^ 59
def prefixEnd_6586705 : Nat := 4983230072969 + 3 ^ 40 * 6586705 * 2
def baseEnd_6586705 : Nat := 1127381864790919073365267

theorem tailTrace_6586705 : CollatzResearch.WordTrace tailWord_6586705 prefixEnd_6586705 1127381864790919073365267 := by
  unfold tailWord_6586705
  simp only [CollatzResearch.WordTrace]
  refine ⟨240236867602500179499681569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160157911735000119666454379 240236867602500179499681569)
  ·
    refine ⟨180177650701875134624761177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240236867602500179499681569 180177650701875134624761177)
    ·
      refine ⟨135133238026406350968570883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180177650701875134624761177 135133238026406350968570883)
      ·
        refine ⟨202699857039609526452856325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135133238026406350968570883 202699857039609526452856325)
        ·
          refine ⟨38006223194926786209910561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202699857039609526452856325 38006223194926786209910561)
          ·
            refine ⟨28504667396195089657432921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38006223194926786209910561 28504667396195089657432921)
            ·
              refine ⟨21378500547146317243074691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28504667396195089657432921 21378500547146317243074691)
              ·
                refine ⟨32067750820719475864612037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21378500547146317243074691 32067750820719475864612037)
                ·
                  refine ⟨6012703278884901724614757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32067750820719475864612037 6012703278884901724614757)
                  ·
                    refine ⟨1127381864790919073365267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6012703278884901724614757 1127381864790919073365267)
                    ·
                      rfl

theorem cell23_6586705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_6586705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586705 prefixEnd_6586705 := by exact prefixLift 6586705
  have htrace : WordTrace (prefixWord ++ tailWord_6586705) baseStart_6586705 baseEnd_6586705 := by
    simpa [prefixWord, tailWord_6586705, baseEnd_6586705] using wordTrace_append hprefix tailTrace_6586705
  have hstable : (prefixWord ++ tailWord_6586705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586705).length < 2 ^ (prefixWord ++ tailWord_6586705).sum := by decide
  have hdescent : baseEnd_6586705 < baseStart_6586705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586712 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 3, 2, 2]
def baseStart_6586712 : Nat := 118140960795 + 6586712 * 2 ^ 59
def prefixEnd_6586712 : Nat := 4983230072969 + 3 ^ 40 * 6586712 * 2
def baseEnd_6586712 : Nat := 3382149188737338692708269

theorem tailTrace_6586712 : CollatzResearch.WordTrace tailWord_6586712 prefixEnd_6586712 3382149188737338692708269 := by
  unfold tailWord_6586712
  simp only [CollatzResearch.WordTrace]
  refine ⟨120118561456737409847593195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160158081942316546463457593 120118561456737409847593195)
  ·
    refine ⟨180177842185106114771389793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120118561456737409847593195 180177842185106114771389793)
    ·
      refine ⟨135133381638829586078542345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180177842185106114771389793 135133381638829586078542345)
      ·
        refine ⟨101350036229122189558906759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135133381638829586078542345 101350036229122189558906759)
        ·
          refine ⟨152025054343683284338360139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101350036229122189558906759 152025054343683284338360139)
          ·
            refine ⟨228037581515524926507540209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152025054343683284338360139 228037581515524926507540209)
            ·
              refine ⟨171028186136643694880655157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228037581515524926507540209 171028186136643694880655157)
              ·
                refine ⟨16033892450310346395061421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171028186136643694880655157 16033892450310346395061421)
                ·
                  refine ⟨6012709668866379898148033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16033892450310346395061421 6012709668866379898148033)
                  ·
                    refine ⟨4509532251649784923611025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6012709668866379898148033 4509532251649784923611025)
                    ·
                      refine ⟨3382149188737338692708269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4509532251649784923611025 3382149188737338692708269)
                      ·
                        rfl

theorem cell23_6586712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_6586712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586712 prefixEnd_6586712 := by exact prefixLift 6586712
  have htrace : WordTrace (prefixWord ++ tailWord_6586712) baseStart_6586712 baseEnd_6586712 := by
    simpa [prefixWord, tailWord_6586712, baseEnd_6586712] using wordTrace_append hprefix tailTrace_6586712
  have hstable : (prefixWord ++ tailWord_6586712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586712).length < 2 ^ (prefixWord ++ tailWord_6586712).sum := by decide
  have hdescent : baseEnd_6586712 < baseStart_6586712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586732 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_6586732 : Nat := 118140960795 + 6586732 * 2 ^ 59
def prefixEnd_6586732 : Nat := 4983230072969 + 3 ^ 40 * 6586732 * 2
def baseEnd_6586732 : Nat := 3382159458350428614458177

theorem tailTrace_6586732 : CollatzResearch.WordTrace tailWord_6586732 prefixEnd_6586732 3382159458350428614458177 := by
  unfold tailWord_6586732
  simp only [CollatzResearch.WordTrace]
  refine ⟨120118926186701181555457225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160158568248934908740609633 120118926186701181555457225)
  ·
    refine ⟨90089194640025886166592919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120118926186701181555457225 90089194640025886166592919)
    ·
      refine ⟨135133791960038829249889379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90089194640025886166592919 135133791960038829249889379)
      ·
        refine ⟨202700687940058243874834069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135133791960038829249889379 202700687940058243874834069)
        ·
          refine ⟨9501594747190230181632847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202700687940058243874834069 9501594747190230181632847)
          ·
            refine ⟨14252392120785345272449271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9501594747190230181632847 14252392120785345272449271)
            ·
              refine ⟨21378588181178017908673907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14252392120785345272449271 21378588181178017908673907)
              ·
                refine ⟨32067882271767026863010861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21378588181178017908673907 32067882271767026863010861)
                ·
                  refine ⟨12025455851912635073629073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32067882271767026863010861 12025455851912635073629073)
                  ·
                    refine ⟨9019091888934476305221805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12025455851912635073629073 9019091888934476305221805)
                    ·
                      refine ⟨3382159458350428614458177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9019091888934476305221805 3382159458350428614458177)
                      ·
                        rfl

theorem cell23_6586732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_6586732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586732 prefixEnd_6586732 := by exact prefixLift 6586732
  have htrace : WordTrace (prefixWord ++ tailWord_6586732) baseStart_6586732 baseEnd_6586732 := by
    simpa [prefixWord, tailWord_6586732, baseEnd_6586732] using wordTrace_append hprefix tailTrace_6586732
  have hstable : (prefixWord ++ tailWord_6586732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586732).length < 2 ^ (prefixWord ++ tailWord_6586732).sum := by decide
  have hdescent : baseEnd_6586732 < baseStart_6586732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586749 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_6586749 : Nat := 118140960795 + 6586749 * 2 ^ 59
def prefixEnd_6586749 : Nat := 4983230072969 + 3 ^ 40 * 6586749 * 2
def baseEnd_6586749 : Nat := 3382168187521555047945599

theorem tailTrace_6586749 : CollatzResearch.WordTrace tailWord_6586749 prefixEnd_6586749 3382168187521555047945599 := by
  unfold tailWord_6586749
  simp only [CollatzResearch.WordTrace]
  refine ⟨240238472414340775014283301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160158981609560516676188867 240238472414340775014283301)
  ·
    refine ⟨45044713577688895315178119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240238472414340775014283301 45044713577688895315178119)
    ·
      refine ⟨67567070366533342972767179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45044713577688895315178119 67567070366533342972767179)
      ·
        refine ⟨101350605549800014459150769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67567070366533342972767179 101350605549800014459150769)
        ·
          refine ⟨76012954162350010844363077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101350605549800014459150769 76012954162350010844363077)
          ·
            refine ⟨14252428905440627033318077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76012954162350010844363077 14252428905440627033318077)
            ·
              refine ⟨5344660839540235137494279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14252428905440627033318077 5344660839540235137494279)
              ·
                refine ⟨8016991259310352706241419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344660839540235137494279 8016991259310352706241419)
                ·
                  refine ⟨12025486888965529059362129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8016991259310352706241419 12025486888965529059362129)
                  ·
                    refine ⟨9019115166724146794521597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12025486888965529059362129 9019115166724146794521597)
                    ·
                      refine ⟨3382168187521555047945599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9019115166724146794521597 3382168187521555047945599)
                      ·
                        rfl

theorem cell23_6586749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_6586749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586749 prefixEnd_6586749 := by exact prefixLift 6586749
  have htrace : WordTrace (prefixWord ++ tailWord_6586749) baseStart_6586749 baseEnd_6586749 := by
    simpa [prefixWord, tailWord_6586749, baseEnd_6586749] using wordTrace_append hprefix tailTrace_6586749
  have hstable : (prefixWord ++ tailWord_6586749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586749).length < 2 ^ (prefixWord ++ tailWord_6586749).sum := by decide
  have hdescent : baseEnd_6586749 < baseStart_6586749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586763 : List Nat := [1, 1, 1, 1, 4, 6, 2, 2, 1, 2, 2]
def baseStart_6586763 : Nat := 118140960795 + 6586763 * 2 ^ 59
def prefixEnd_6586763 : Nat := 4983230072969 + 3 ^ 40 * 6586763 * 2
def baseEnd_6586763 : Nat := 3382175376250717993170535

theorem tailTrace_6586763 : CollatzResearch.WordTrace tailWord_6586763 prefixEnd_6586763 3382175376250717993170535 := by
  unfold tailWord_6586763
  simp only [CollatzResearch.WordTrace]
  refine ⟨240238983036290055405292943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160159322024193370270195295 240238983036290055405292943)
  ·
    refine ⟨360358474554435083107939415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240238983036290055405292943 360358474554435083107939415)
    ·
      refine ⟨540537711831652624661909123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360358474554435083107939415 540537711831652624661909123)
      ·
        refine ⟨810806567747478936992863685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540537711831652624661909123 810806567747478936992863685)
        ·
          refine ⟨152026231452652300686161941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 810806567747478936992863685 152026231452652300686161941)
          ·
            refine ⟨7126229599343076594663841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152026231452652300686161941 7126229599343076594663841)
            ·
              refine ⟨5344672199507307445997881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7126229599343076594663841 5344672199507307445997881)
              ·
                refine ⟨4008504149630480584498411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5344672199507307445997881 4008504149630480584498411)
                ·
                  refine ⟨6012756224445720876747617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4008504149630480584498411 6012756224445720876747617)
                  ·
                    refine ⟨4509567168334290657560713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6012756224445720876747617 4509567168334290657560713)
                    ·
                      refine ⟨3382175376250717993170535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4509567168334290657560713 3382175376250717993170535)
                      ·
                        rfl

theorem cell23_6586763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 2, 2].length) (baseStart_6586763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586763 prefixEnd_6586763 := by exact prefixLift 6586763
  have htrace : WordTrace (prefixWord ++ tailWord_6586763) baseStart_6586763 baseEnd_6586763 := by
    simpa [prefixWord, tailWord_6586763, baseEnd_6586763] using wordTrace_append hprefix tailTrace_6586763
  have hstable : (prefixWord ++ tailWord_6586763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586763).length < 2 ^ (prefixWord ++ tailWord_6586763).sum := by decide
  have hdescent : baseEnd_6586763 < baseStart_6586763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586802 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_6586802 : Nat := 118140960795 + 6586802 * 2 ^ 59
def prefixEnd_6586802 : Nat := 4983230072969 + 3 ^ 40 * 6586802 * 2
def baseEnd_6586802 : Nat := 3382195401996243340582855

theorem tailTrace_6586802 : CollatzResearch.WordTrace tailWord_6586802 prefixEnd_6586802 3382195401996243340582855 := by
  unfold tailWord_6586802
  simp only [CollatzResearch.WordTrace]
  refine ⟨60060101370787191266490665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160160270322099176710641773 60060101370787191266490665)
  ·
    refine ⟨45045076028090393449867999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60060101370787191266490665 45045076028090393449867999)
    ·
      refine ⟨67567614042135590174801999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45045076028090393449867999 67567614042135590174801999)
      ·
        refine ⟨101351421063203385262202999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67567614042135590174801999 101351421063203385262202999)
        ·
          refine ⟨152027131594805077893304499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101351421063203385262202999 152027131594805077893304499)
          ·
            refine ⟨228040697392207616839956749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152027131594805077893304499 228040697392207616839956749)
            ·
              refine ⟨85515261522077856314983781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228040697392207616839956749 85515261522077856314983781)
              ·
                refine ⟨16034111535389598059059459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85515261522077856314983781 16034111535389598059059459)
                ·
                  refine ⟨24051167303084397088589189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16034111535389598059059459 24051167303084397088589189)
                  ·
                    refine ⟨4509593869328324454110473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24051167303084397088589189 4509593869328324454110473)
                    ·
                      refine ⟨3382195401996243340582855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4509593869328324454110473 3382195401996243340582855)
                      ·
                        rfl

theorem cell23_6586802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_6586802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586802 prefixEnd_6586802 := by exact prefixLift 6586802
  have htrace : WordTrace (prefixWord ++ tailWord_6586802) baseStart_6586802 baseEnd_6586802 := by
    simpa [prefixWord, tailWord_6586802, baseEnd_6586802] using wordTrace_append hprefix tailTrace_6586802
  have hstable : (prefixWord ++ tailWord_6586802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586802).length < 2 ^ (prefixWord ++ tailWord_6586802).sum := by decide
  have hdescent : baseEnd_6586802 < baseStart_6586802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586808 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 11]
def baseStart_6586808 : Nat := 118140960795 + 6586808 * 2 ^ 59
def prefixEnd_6586808 : Nat := 4983230072969 + 3 ^ 40 * 6586808 * 2
def baseEnd_6586808 : Nat := 375799831431130035234203

theorem tailTrace_6586808 : CollatzResearch.WordTrace tailWord_6586808 prefixEnd_6586808 375799831431130035234203 := by
  unfold tailWord_6586808
  simp only [CollatzResearch.WordTrace]
  refine ⟨120120312160563514045340539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160160416214084685393787385 120120312160563514045340539)
  ·
    refine ⟨180180468240845271068010809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120120312160563514045340539 180180468240845271068010809)
    ·
      refine ⟨135135351180633953301008107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180180468240845271068010809 135135351180633953301008107)
      ·
        refine ⟨202703026770950929951512161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135135351180633953301008107 202703026770950929951512161)
        ·
          refine ⟨152027270078213197463634121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202703026770950929951512161 152027270078213197463634121)
          ·
            refine ⟨114020452558659898097725591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152027270078213197463634121 114020452558659898097725591)
            ·
              refine ⟨171030678837989847146588387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114020452558659898097725591 171030678837989847146588387)
              ·
                refine ⟨256546018256984770719882581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171030678837989847146588387 256546018256984770719882581)
                ·
                  refine ⟨375799831431130035234203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 256546018256984770719882581 375799831431130035234203)
                  ·
                    rfl

theorem cell23_6586808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 11].length) (baseStart_6586808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586808 prefixEnd_6586808 := by exact prefixLift 6586808
  have htrace : WordTrace (prefixWord ++ tailWord_6586808) baseStart_6586808 baseEnd_6586808 := by
    simpa [prefixWord, tailWord_6586808, baseEnd_6586808] using wordTrace_append hprefix tailTrace_6586808
  have hstable : (prefixWord ++ tailWord_6586808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586808).length < 2 ^ (prefixWord ++ tailWord_6586808).sum := by decide
  have hdescent : baseEnd_6586808 < baseStart_6586808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586836 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_6586836 : Nat := 118140960795 + 6586836 * 2 ^ 59
def prefixEnd_6586836 : Nat := 4983230072969 + 3 ^ 40 * 6586836 * 2
def baseEnd_6586836 : Nat := 3382212860338496207557699

theorem tailTrace_6586836 : CollatzResearch.WordTrace tailWord_6586836 prefixEnd_6586836 3382212860338496207557699 := by
  unfold tailWord_6586836
  simp only [CollatzResearch.WordTrace]
  refine ⟨120120822782512794436350181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160161097043350392581800241 120120822782512794436350181)
  ·
    refine ⟨22522654271721148956815659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120120822782512794436350181 22522654271721148956815659)
    ·
      refine ⟨33783981407581723435223489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22522654271721148956815659 33783981407581723435223489)
      ·
        refine ⟨25337986055686292576417617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33783981407581723435223489 25337986055686292576417617)
        ·
          refine ⟨19003489541764719432313213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25337986055686292576417617 19003489541764719432313213)
          ·
            refine ⟨7126308578161769787117455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19003489541764719432313213 7126308578161769787117455)
            ·
              refine ⟨10689462867242654680676183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7126308578161769787117455 10689462867242654680676183)
              ·
                refine ⟨16034194300863982021014275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10689462867242654680676183 16034194300863982021014275)
                ·
                  refine ⟨24051291451295973031521413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16034194300863982021014275 24051291451295973031521413)
                  ·
                    refine ⟨4509617147117994943410265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24051291451295973031521413 4509617147117994943410265)
                    ·
                      refine ⟨3382212860338496207557699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4509617147117994943410265 3382212860338496207557699)
                      ·
                        rfl

theorem cell23_6586836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_6586836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586836 prefixEnd_6586836 := by exact prefixLift 6586836
  have htrace : WordTrace (prefixWord ++ tailWord_6586836) baseStart_6586836 baseEnd_6586836 := by
    simpa [prefixWord, tailWord_6586836, baseEnd_6586836] using wordTrace_append hprefix tailTrace_6586836
  have hstable : (prefixWord ++ tailWord_6586836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586836).length < 2 ^ (prefixWord ++ tailWord_6586836).sum := by decide
  have hdescent : baseEnd_6586836 < baseStart_6586836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586855 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 1, 7]
def baseStart_6586855 : Nat := 118140960795 + 6586855 * 2 ^ 59
def prefixEnd_6586855 : Nat := 4983230072969 + 3 ^ 40 * 6586855 * 2
def baseEnd_6586855 : Nat := 1127407538823643877740037

theorem tailTrace_6586855 : CollatzResearch.WordTrace tailWord_6586855 prefixEnd_6586855 1127407538823643877740037 := by
  unfold tailWord_6586855
  simp only [CollatzResearch.WordTrace]
  refine ⟨240242338551956755117642019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160161559034637836745094679 240242338551956755117642019)
  ·
    refine ⟨360363507827935132676463029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240242338551956755117642019 360363507827935132676463029)
    ·
      refine ⟨33784078858868918688418409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 360363507827935132676463029 33784078858868918688418409)
      ·
        refine ⟨25338059144151689016313807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33784078858868918688418409 25338059144151689016313807)
        ·
          refine ⟨38007088716227533524470711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25338059144151689016313807 38007088716227533524470711)
          ·
            refine ⟨57010633074341300286706067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38007088716227533524470711 57010633074341300286706067)
            ·
              refine ⟨85515949611511950430059101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57010633074341300286706067 85515949611511950430059101)
              ·
                refine ⟨32068481104316981411272163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85515949611511950430059101 32068481104316981411272163)
                ·
                  refine ⟨48102721656475472116908245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32068481104316981411272163 48102721656475472116908245)
                  ·
                    refine ⟨1127407538823643877740037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48102721656475472116908245 1127407538823643877740037)
                    ·
                      rfl

theorem cell23_6586855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_6586855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586855 prefixEnd_6586855 := by exact prefixLift 6586855
  have htrace : WordTrace (prefixWord ++ tailWord_6586855) baseStart_6586855 baseEnd_6586855 := by
    simpa [prefixWord, tailWord_6586855, baseEnd_6586855] using wordTrace_append hprefix tailTrace_6586855
  have hstable : (prefixWord ++ tailWord_6586855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586855).length < 2 ^ (prefixWord ++ tailWord_6586855).sum := by decide
  have hdescent : baseEnd_6586855 < baseStart_6586855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586865 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_6586865 : Nat := 118140960795 + 6586865 * 2 ^ 59
def prefixEnd_6586865 : Nat := 4983230072969 + 3 ^ 40 * 6586865 * 2
def baseEnd_6586865 : Nat := 3382227751277476594095065

theorem tailTrace_6586865 : CollatzResearch.WordTrace tailWord_6586865 prefixEnd_6586865 3382227751277476594095065 := by
  unfold tailWord_6586865
  simp only [CollatzResearch.WordTrace]
  refine ⟨240242703281920526825506049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160161802187947017883670699 240242703281920526825506049)
  ·
    refine ⟨180182027461440395119129537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240242703281920526825506049 180182027461440395119129537)
    ·
      refine ⟨135136520596080296339347153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180182027461440395119129537 135136520596080296339347153)
      ·
        refine ⟨101352390447060222254510365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135136520596080296339347153 101352390447060222254510365)
        ·
          refine ⟨38007146417647583345441387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101352390447060222254510365 38007146417647583345441387)
          ·
            refine ⟨57010719626471375018162081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38007146417647583345441387 57010719626471375018162081)
            ·
              refine ⟨42758039719853531263621561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57010719626471375018162081 42758039719853531263621561)
              ·
                refine ⟨32068529789890148447716171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42758039719853531263621561 32068529789890148447716171)
                ·
                  refine ⟨48102794684835222671574257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32068529789890148447716171 48102794684835222671574257)
                  ·
                    refine ⟨36077096013626417003680693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48102794684835222671574257 36077096013626417003680693)
                    ·
                      refine ⟨3382227751277476594095065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36077096013626417003680693 3382227751277476594095065)
                      ·
                        rfl

theorem cell23_6586865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_6586865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586865 prefixEnd_6586865 := by exact prefixLift 6586865
  have htrace : WordTrace (prefixWord ++ tailWord_6586865) baseStart_6586865 baseEnd_6586865 := by
    simpa [prefixWord, tailWord_6586865, baseEnd_6586865] using wordTrace_append hprefix tailTrace_6586865
  have hstable : (prefixWord ++ tailWord_6586865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586865).length < 2 ^ (prefixWord ++ tailWord_6586865).sum := by decide
  have hdescent : baseEnd_6586865 < baseStart_6586865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586909 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_6586909 : Nat := 118140960795 + 6586909 * 2 ^ 59
def prefixEnd_6586909 : Nat := 4983230072969 + 3 ^ 40 * 6586909 * 2
def baseEnd_6586909 : Nat := 3382250344426274421944863

theorem tailTrace_6586909 : CollatzResearch.WordTrace tailWord_6586909 prefixEnd_6586909 3382250344426274421944863 := by
  unfold tailWord_6586909
  simp only [CollatzResearch.WordTrace]
  refine ⟨240244308093761122340107781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160162872062507414893405187 240244308093761122340107781)
  ·
    refine ⟨45045807767580210438770209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240244308093761122340107781 45045807767580210438770209)
    ·
      refine ⟨33784355825685157829077657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45045807767580210438770209 33784355825685157829077657)
      ·
        refine ⟨25338266869263868371808243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33784355825685157829077657 25338266869263868371808243)
        ·
          refine ⟨38007400303895802557712365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25338266869263868371808243 38007400303895802557712365)
          ·
            refine ⟨14252775113960925959142137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38007400303895802557712365 14252775113960925959142137)
            ·
              refine ⟨10689581335470694469356603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14252775113960925959142137 10689581335470694469356603)
              ·
                refine ⟨16034372003206041704034905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10689581335470694469356603 16034372003206041704034905)
                ·
                  refine ⟨12025779002404531278026179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16034372003206041704034905 12025779002404531278026179)
                  ·
                    refine ⟨18038668503606796917039269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12025779002404531278026179 18038668503606796917039269)
                    ·
                      refine ⟨3382250344426274421944863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18038668503606796917039269 3382250344426274421944863)
                      ·
                        rfl

theorem cell23_6586909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_6586909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586909 prefixEnd_6586909 := by exact prefixLift 6586909
  have htrace : WordTrace (prefixWord ++ tailWord_6586909) baseStart_6586909 baseEnd_6586909 := by
    simpa [prefixWord, tailWord_6586909, baseEnd_6586909] using wordTrace_append hprefix tailTrace_6586909
  have hstable : (prefixWord ++ tailWord_6586909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586909).length < 2 ^ (prefixWord ++ tailWord_6586909).sum := by decide
  have hdescent : baseEnd_6586909 < baseStart_6586909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586935 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_6586935 : Nat := 118140960795 + 6586935 * 2 ^ 59
def prefixEnd_6586935 : Nat := 4983230072969 + 3 ^ 40 * 6586935 * 2
def baseEnd_6586935 : Nat := 3382263694923291320219743

theorem tailTrace_6586935 : CollatzResearch.WordTrace tailWord_6586935 prefixEnd_6586935 3382263694923291320219743 := by
  unfold tailWord_6586935
  simp only [CollatzResearch.WordTrace]
  refine ⟨240245256391666928780554259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160163504261111285853702839 240245256391666928780554259)
  ·
    refine ⟨360367884587500393170831389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240245256391666928780554259 360367884587500393170831389)
    ·
      refine ⟨135137956720312647439061771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360367884587500393170831389 135137956720312647439061771)
      ·
        refine ⟨202706935080468971158592657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135137956720312647439061771 202706935080468971158592657)
        ·
          refine ⟨152030201310351728368944493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202706935080468971158592657 152030201310351728368944493)
          ·
            refine ⟨57011325491381898138354185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152030201310351728368944493 57011325491381898138354185)
            ·
              refine ⟨42758494118536423603765639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57011325491381898138354185 42758494118536423603765639)
              ·
                refine ⟨64137741177804635405648459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42758494118536423603765639 64137741177804635405648459)
                ·
                  refine ⟨96206611766706953108472689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64137741177804635405648459 96206611766706953108472689)
                  ·
                    refine ⟨72154958825030214831354517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96206611766706953108472689 72154958825030214831354517)
                    ·
                      refine ⟨3382263694923291320219743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72154958825030214831354517 3382263694923291320219743)
                      ·
                        rfl

theorem cell23_6586935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_6586935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586935 prefixEnd_6586935 := by exact prefixLift 6586935
  have htrace : WordTrace (prefixWord ++ tailWord_6586935) baseStart_6586935 baseEnd_6586935 := by
    simpa [prefixWord, tailWord_6586935, baseEnd_6586935] using wordTrace_append hprefix tailTrace_6586935
  have hstable : (prefixWord ++ tailWord_6586935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586935).length < 2 ^ (prefixWord ++ tailWord_6586935).sum := by decide
  have hdescent : baseEnd_6586935 < baseStart_6586935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586962 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_6586962 : Nat := 118140960795 + 6586962 * 2 ^ 59
def prefixEnd_6586962 : Nat := 4983230072969 + 3 ^ 40 * 6586962 * 2
def baseEnd_6586962 : Nat := 1127425852966987571527373

theorem tailTrace_6586962 : CollatzResearch.WordTrace tailWord_6586962 prefixEnd_6586962 1127425852966987571527373 := by
  unfold tailWord_6586962
  simp only [CollatzResearch.WordTrace]
  refine ⟨60061560290642278097946785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160164160775046074927858093 60061560290642278097946785)
  ·
    refine ⟨45046170217981708573460089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60061560290642278097946785 45046170217981708573460089)
    ·
      refine ⟨33784627663486281430095067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45046170217981708573460089 33784627663486281430095067)
      ·
        refine ⟨50676941495229422145142601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33784627663486281430095067 50676941495229422145142601)
        ·
          refine ⟨38007706121422066608856951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50676941495229422145142601 38007706121422066608856951)
          ·
            refine ⟨57011559182133099913285427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38007706121422066608856951 57011559182133099913285427)
            ·
              refine ⟨85517338773199649869928141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57011559182133099913285427 85517338773199649869928141)
              ·
                refine ⟨32069002039949868701223053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85517338773199649869928141 32069002039949868701223053)
                ·
                  refine ⟨12025875764981200762958645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32069002039949868701223053 12025875764981200762958645)
                  ·
                    refine ⟨1127425852966987571527373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12025875764981200762958645 1127425852966987571527373)
                    ·
                      rfl

theorem cell23_6586962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_6586962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586962 prefixEnd_6586962 := by exact prefixLift 6586962
  have htrace : WordTrace (prefixWord ++ tailWord_6586962) baseStart_6586962 baseEnd_6586962 := by
    simpa [prefixWord, tailWord_6586962, baseEnd_6586962] using wordTrace_append hprefix tailTrace_6586962
  have hstable : (prefixWord ++ tailWord_6586962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586962).length < 2 ^ (prefixWord ++ tailWord_6586962).sum := by decide
  have hdescent : baseEnd_6586962 < baseStart_6586962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6586976 : List Nat := [2, 1, 1, 3, 2, 1, 3, 5, 1, 1, 3]
def baseStart_6586976 : Nat := 118140960795 + 6586976 * 2 ^ 59
def prefixEnd_6586976 : Nat := 4983230072969 + 3 ^ 40 * 6586976 * 2
def baseEnd_6586976 : Nat := 3382284747630125659807055

theorem tailTrace_6586976 : CollatzResearch.WordTrace tailWord_6586976 prefixEnd_6586976 3382284747630125659807055 := by
  unfold tailWord_6586976
  simp only [CollatzResearch.WordTrace]
  refine ⟨120123375892259196391398391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160164501189678928521864521 120123375892259196391398391)
  ·
    refine ⟨180185063838388794587097587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120123375892259196391398391 180185063838388794587097587)
    ·
      refine ⟨270277595757583191880646381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180185063838388794587097587 270277595757583191880646381)
      ·
        refine ⟨101354098409093696955242393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270277595757583191880646381 101354098409093696955242393)
        ·
          refine ⟨76015573806820272716431795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101354098409093696955242393 76015573806820272716431795)
          ·
            refine ⟨114023360710230409074647693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76015573806820272716431795 114023360710230409074647693)
            ·
              refine ⟨42758760266336403402992885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114023360710230409074647693 42758760266336403402992885)
              ·
                refine ⟨4008633774969037819030583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42758760266336403402992885 4008633774969037819030583)
                ·
                  refine ⟨6012950662453556728545875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4008633774969037819030583 6012950662453556728545875)
                  ·
                    refine ⟨9019425993680335092818813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6012950662453556728545875 9019425993680335092818813)
                    ·
                      refine ⟨3382284747630125659807055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9019425993680335092818813 3382284747630125659807055)
                      ·
                        rfl

theorem cell23_6586976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_6586976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6586976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6586976 prefixEnd_6586976 := by exact prefixLift 6586976
  have htrace : WordTrace (prefixWord ++ tailWord_6586976) baseStart_6586976 baseEnd_6586976 := by
    simpa [prefixWord, tailWord_6586976, baseEnd_6586976] using wordTrace_append hprefix tailTrace_6586976
  have hstable : (prefixWord ++ tailWord_6586976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6586976).length < 2 ^ (prefixWord ++ tailWord_6586976).sum := by decide
  have hdescent : baseEnd_6586976 < baseStart_6586976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6586976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587022 : List Nat := [4, 1, 1, 3, 1, 1, 3, 9]
def baseStart_6587022 : Nat := 118140960795 + 6587022 * 2 ^ 59
def prefixEnd_6587022 : Nat := 4983230072969 + 3 ^ 40 * 6587022 * 2
def baseEnd_6587022 : Nat := 125270680286675277030809

theorem tailTrace_6587022 : CollatzResearch.WordTrace tailWord_6587022 prefixEnd_6587022 125270680286675277030809 := by
  unfold tailWord_6587022
  simp only [CollatzResearch.WordTrace]
  refine ⟨30031053692793967829871415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160165619694901161759314213 30031053692793967829871415)
  ·
    refine ⟨45046580539190951744807123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30031053692793967829871415 45046580539190951744807123)
    ·
      refine ⟨67569870808786427617210685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45046580539190951744807123 67569870808786427617210685)
      ·
        refine ⟨25338701553294910356454007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67569870808786427617210685 25338701553294910356454007)
        ·
          refine ⟨38008052329942365534681011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25338701553294910356454007 38008052329942365534681011)
          ·
            refine ⟨57012078494913548302021517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38008052329942365534681011 57012078494913548302021517)
            ·
              refine ⟨21379529435592580613258069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57012078494913548302021517 21379529435592580613258069)
              ·
                refine ⟨125270680286675277030809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21379529435592580613258069 125270680286675277030809)
                ·
                  rfl

theorem cell23_6587022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_6587022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587022 prefixEnd_6587022 := by exact prefixLift 6587022
  have htrace : WordTrace (prefixWord ++ tailWord_6587022) baseStart_6587022 baseEnd_6587022 := by
    simpa [prefixWord, tailWord_6587022, baseEnd_6587022] using wordTrace_append hprefix tailTrace_6587022
  have hstable : (prefixWord ++ tailWord_6587022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587022).length < 2 ^ (prefixWord ++ tailWord_6587022).sum := by decide
  have hdescent : baseEnd_6587022 < baseStart_6587022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587036 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_6587036 : Nat := 118140960795 + 6587036 * 2 ^ 59
def prefixEnd_6587036 : Nat := 4983230072969 + 3 ^ 40 * 6587036 * 2
def baseEnd_6587036 : Nat := 3382315556469395425056779

theorem tailTrace_6587036 : CollatzResearch.WordTrace tailWord_6587036 prefixEnd_6587036 3382315556469395425056779 := by
  unfold tailWord_6587036
  simp only [CollatzResearch.WordTrace]
  refine ⟨120124470082150511514990481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160165960109534015353320641 120124470082150511514990481)
  ·
    refine ⟨90093352561612883636242861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120124470082150511514990481 90093352561612883636242861)
    ·
      refine ⟨33785007210604831363591073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90093352561612883636242861 33785007210604831363591073)
      ·
        refine ⟨25338755407953623522693305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33785007210604831363591073 25338755407953623522693305)
        ·
          refine ⟨19004066555965217642019979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25338755407953623522693305 19004066555965217642019979)
          ·
            refine ⟨28506099833947826463029969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19004066555965217642019979 28506099833947826463029969)
            ·
              refine ⟨21379574875460869847272477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28506099833947826463029969 21379574875460869847272477)
              ·
                refine ⟨8017340578297826192727179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21379574875460869847272477 8017340578297826192727179)
                ·
                  refine ⟨12026010867446739289090769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8017340578297826192727179 12026010867446739289090769)
                  ·
                    refine ⟨9019508150585054466818077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12026010867446739289090769 9019508150585054466818077)
                    ·
                      refine ⟨3382315556469395425056779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9019508150585054466818077 3382315556469395425056779)
                      ·
                        rfl

theorem cell23_6587036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_6587036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587036 prefixEnd_6587036 := by exact prefixLift 6587036
  have htrace : WordTrace (prefixWord ++ tailWord_6587036) baseStart_6587036 baseEnd_6587036 := by
    simpa [prefixWord, tailWord_6587036, baseEnd_6587036] using wordTrace_append hprefix tailTrace_6587036
  have hstable : (prefixWord ++ tailWord_6587036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587036).length < 2 ^ (prefixWord ++ tailWord_6587036).sum := by decide
  have hdescent : baseEnd_6587036 < baseStart_6587036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587066 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_6587066 : Nat := 118140960795 + 6587066 * 2 ^ 59
def prefixEnd_6587066 : Nat := 4983230072969 + 3 ^ 40 * 6587066 * 2
def baseEnd_6587066 : Nat := 3382330960889030307681641

theorem tailTrace_6587066 : CollatzResearch.WordTrace tailWord_6587066 prefixEnd_6587066 3382330960889030307681641 := by
  unfold tailWord_6587066
  simp only [CollatzResearch.WordTrace]
  refine ⟨60062508588548084538393263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160166689569461558769048701 60062508588548084538393263)
  ·
    refine ⟨90093762882822126807589895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60062508588548084538393263 90093762882822126807589895)
    ·
      refine ⟨135140644324233190211384843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90093762882822126807589895 135140644324233190211384843)
      ·
        refine ⟨202710966486349785317077265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135140644324233190211384843 202710966486349785317077265)
        ·
          refine ⟨152033224864762338987807949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202710966486349785317077265 152033224864762338987807949)
          ·
            refine ⟨57012459324285877120427981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152033224864762338987807949 57012459324285877120427981)
            ·
              refine ⟨21379672246607203920160493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57012459324285877120427981 21379672246607203920160493)
              ·
                refine ⟨8017377092477701470060185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21379672246607203920160493 8017377092477701470060185)
                ·
                  refine ⟨6013032819358276102545139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8017377092477701470060185 6013032819358276102545139)
                  ·
                    refine ⟨9019549229037414153817709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6013032819358276102545139 9019549229037414153817709)
                    ·
                      refine ⟨3382330960889030307681641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9019549229037414153817709 3382330960889030307681641)
                      ·
                        rfl

theorem cell23_6587066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_6587066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587066 prefixEnd_6587066 := by exact prefixLift 6587066
  have htrace : WordTrace (prefixWord ++ tailWord_6587066) baseStart_6587066 baseEnd_6587066 := by
    simpa [prefixWord, tailWord_6587066, baseEnd_6587066] using wordTrace_append hprefix tailTrace_6587066
  have hstable : (prefixWord ++ tailWord_6587066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587066).length < 2 ^ (prefixWord ++ tailWord_6587066).sum := by decide
  have hdescent : baseEnd_6587066 < baseStart_6587066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587100 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6587100 : Nat := 118140960795 + 6587100 * 2 ^ 59
def prefixEnd_6587100 : Nat := 4983230072969 + 3 ^ 40 * 6587100 * 2
def baseEnd_6587100 : Nat := 3382348419231283174656485

theorem tailTrace_6587100 : CollatzResearch.WordTrace tailWord_6587100 prefixEnd_6587100 3382348419231283174656485 := by
  unfold tailWord_6587100
  simp only [CollatzResearch.WordTrace]
  refine ⟨120125637218034580980155377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160167516290712774640207169 120125637218034580980155377)
  ·
    refine ⟨90094227913525935735116533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120125637218034580980155377 90094227913525935735116533)
    ·
      refine ⟨8446333866893056475167175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90094227913525935735116533 8446333866893056475167175)
      ·
        refine ⟨12669500800339584712750763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8446333866893056475167175 12669500800339584712750763)
        ·
          refine ⟨19004251200509377069126145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12669500800339584712750763 19004251200509377069126145)
          ·
            refine ⟨14253188400382032801844609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19004251200509377069126145 14253188400382032801844609)
            ·
              refine ⟨10689891300286524601383457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14253188400382032801844609 10689891300286524601383457)
              ·
                refine ⟨8017418475214893451037593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10689891300286524601383457 8017418475214893451037593)
                ·
                  refine ⟨6013063856411170088278195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8017418475214893451037593 6013063856411170088278195)
                  ·
                    refine ⟨9019595784616755132417293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6013063856411170088278195 9019595784616755132417293)
                    ·
                      refine ⟨3382348419231283174656485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9019595784616755132417293 3382348419231283174656485)
                      ·
                        rfl

theorem cell23_6587100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6587100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587100 prefixEnd_6587100 := by exact prefixLift 6587100
  have htrace : WordTrace (prefixWord ++ tailWord_6587100) baseStart_6587100 baseEnd_6587100 := by
    simpa [prefixWord, tailWord_6587100, baseEnd_6587100] using wordTrace_append hprefix tailTrace_6587100
  have hstable : (prefixWord ++ tailWord_6587100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587100).length < 2 ^ (prefixWord ++ tailWord_6587100).sum := by decide
  have hdescent : baseEnd_6587100 < baseStart_6587100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587109 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_6587109 : Nat := 118140960795 + 6587109 * 2 ^ 59
def prefixEnd_6587109 : Nat := 4983230072969 + 3 ^ 40 * 6587109 * 2
def baseEnd_6587109 : Nat := 3382353040557173639443943

theorem tailTrace_6587109 : CollatzResearch.WordTrace tailWord_6587109 prefixEnd_6587109 3382353040557173639443943 := by
  unfold tailWord_6587109
  simp only [CollatzResearch.WordTrace]
  refine ⟨240251602693036556497388381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160167735128691037664925587 240251602693036556497388381)
  ·
    refine ⟨90094351009888708686520643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240251602693036556497388381 90094351009888708686520643)
    ·
      refine ⟨135141526514833063029780965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90094351009888708686520643 135141526514833063029780965)
      ·
        refine ⟨25339036221531199318083931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135141526514833063029780965 25339036221531199318083931)
        ·
          refine ⟨38008554332296798977125897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25339036221531199318083931 38008554332296798977125897)
          ·
            refine ⟨28506415749222599232844423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38008554332296798977125897 28506415749222599232844423)
            ·
              refine ⟨42759623623833898849266635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28506415749222599232844423 42759623623833898849266635)
              ·
                refine ⟨64139435435750848273899953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42759623623833898849266635 64139435435750848273899953)
                ·
                  refine ⟨48104576576813136205424965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64139435435750848273899953 48104576576813136205424965)
                  ·
                    refine ⟨9019608108152463038517181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48104576576813136205424965 9019608108152463038517181)
                    ·
                      refine ⟨3382353040557173639443943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9019608108152463038517181 3382353040557173639443943)
                      ·
                        rfl

theorem cell23_6587109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_6587109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587109 prefixEnd_6587109 := by exact prefixLift 6587109
  have htrace : WordTrace (prefixWord ++ tailWord_6587109) baseStart_6587109 baseEnd_6587109 := by
    simpa [prefixWord, tailWord_6587109, baseEnd_6587109] using wordTrace_append hprefix tailTrace_6587109
  have hstable : (prefixWord ++ tailWord_6587109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587109).length < 2 ^ (prefixWord ++ tailWord_6587109).sum := by decide
  have hdescent : baseEnd_6587109 < baseStart_6587109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587119 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_6587119 : Nat := 118140960795 + 6587119 * 2 ^ 59
def prefixEnd_6587119 : Nat := 4983230072969 + 3 ^ 40 * 6587119 * 2
def baseEnd_6587119 : Nat := 3382358175363718600318897

theorem tailTrace_6587119 : CollatzResearch.WordTrace tailWord_6587119 prefixEnd_6587119 3382358175363718600318897 := by
  unfold tailWord_6587119
  simp only [CollatzResearch.WordTrace]
  refine ⟨240251967423000328205252411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160167978282000218803501607 240251967423000328205252411)
  ·
    refine ⟨360377951134500492307878617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240251967423000328205252411 360377951134500492307878617)
    ·
      refine ⟨270283463350875369230908963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360377951134500492307878617 270283463350875369230908963)
      ·
        refine ⟨405425195026313053846363445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270283463350875369230908963 405425195026313053846363445)
        ·
          refine ⟨38008612033716848798096573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 405425195026313053846363445 38008612033716848798096573)
          ·
            refine ⟨14253229512643818299286215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38008612033716848798096573 14253229512643818299286215)
            ·
              refine ⟨21379844268965727448929323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14253229512643818299286215 21379844268965727448929323)
              ·
                refine ⟨32069766403448591173393985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21379844268965727448929323 32069766403448591173393985)
                ·
                  refine ⟨24052324802586443380045489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32069766403448591173393985 24052324802586443380045489)
                  ·
                    refine ⟨18039243601939832535034117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24052324802586443380045489 18039243601939832535034117)
                    ·
                      refine ⟨3382358175363718600318897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18039243601939832535034117 3382358175363718600318897)
                      ·
                        rfl

theorem cell23_6587119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_6587119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587119 prefixEnd_6587119 := by exact prefixLift 6587119
  have htrace : WordTrace (prefixWord ++ tailWord_6587119) baseStart_6587119 baseEnd_6587119 := by
    simpa [prefixWord, tailWord_6587119, baseEnd_6587119] using wordTrace_append hprefix tailTrace_6587119
  have hstable : (prefixWord ++ tailWord_6587119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587119).length < 2 ^ (prefixWord ++ tailWord_6587119).sum := by decide
  have hdescent : baseEnd_6587119 < baseStart_6587119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587146 : List Nat := [3, 1, 2, 2, 1, 2, 4, 3, 5]
def baseStart_6587146 : Nat := 118140960795 + 6587146 * 2 ^ 59
def prefixEnd_6587146 : Nat := 4983230072969 + 3 ^ 40 * 6587146 * 2
def baseEnd_6587146 : Nat := 375819115482376666075697

theorem tailTrace_6587146 : CollatzResearch.WordTrace tailWord_6587146 prefixEnd_6587146 375819115482376666075697 := by
  unfold tailWord_6587146
  simp only [CollatzResearch.WordTrace]
  refine ⟨60063238048475627954121323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160168634795935007877656861 60063238048475627954121323)
  ·
    refine ⟨90094857072713441931181985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60063238048475627954121323 90094857072713441931181985)
    ·
      refine ⟨67571142804535081448386489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90094857072713441931181985 67571142804535081448386489)
      ·
        refine ⟨50678357103401311086289867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67571142804535081448386489 50678357103401311086289867)
        ·
          refine ⟨76017535655101966629434801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50678357103401311086289867 76017535655101966629434801)
          ·
            refine ⟨57013151741326474972076101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76017535655101966629434801 57013151741326474972076101)
            ·
              refine ⟨10689965951498714057264269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57013151741326474972076101 10689965951498714057264269)
              ·
                refine ⟨4008737231812017771474101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10689965951498714057264269 4008737231812017771474101)
                ·
                  refine ⟨375819115482376666075697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4008737231812017771474101 375819115482376666075697)
                  ·
                    rfl

theorem cell23_6587146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_6587146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587146 prefixEnd_6587146 := by exact prefixLift 6587146
  have htrace : WordTrace (prefixWord ++ tailWord_6587146) baseStart_6587146 baseEnd_6587146 := by
    simpa [prefixWord, tailWord_6587146, baseEnd_6587146] using wordTrace_append hprefix tailTrace_6587146
  have hstable : (prefixWord ++ tailWord_6587146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587146).length < 2 ^ (prefixWord ++ tailWord_6587146).sum := by decide
  have hdescent : baseEnd_6587146 < baseStart_6587146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587223 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 3, 4]
def baseStart_6587223 : Nat := 118140960795 + 6587223 * 2 ^ 59
def prefixEnd_6587223 : Nat := 4983230072969 + 3 ^ 40 * 6587223 * 2
def baseEnd_6587223 : Nat := 1127470525783928731139473

theorem tailTrace_6587223 : CollatzResearch.WordTrace tailWord_6587223 prefixEnd_6587223 1127470525783928731139473 := by
  unfold tailWord_6587223
  simp only [CollatzResearch.WordTrace]
  refine ⟨240255760614623553967038323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160170507076415702644692215 240255760614623553967038323)
  ·
    refine ⟨360383640921935330950557485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240255760614623553967038323 360383640921935330950557485)
    ·
      refine ⟨135143865345725749106459057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360383640921935330950557485 135143865345725749106459057)
      ·
        refine ⟨101357899009294311829844293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135143865345725749106459057 101357899009294311829844293)
        ·
          refine ⟨19004606064242683468095805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101357899009294311829844293 19004606064242683468095805)
          ·
            refine ⟨7126727274091006300535927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19004606064242683468095805 7126727274091006300535927)
            ·
              refine ⟨10690090911136509450803891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7126727274091006300535927 10690090911136509450803891)
              ·
                refine ⟨16035136366704764176205837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10690090911136509450803891 16035136366704764176205837)
                ·
                  refine ⟨6013176137514286566077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16035136366704764176205837 6013176137514286566077189)
                  ·
                    refine ⟨1127470525783928731139473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6013176137514286566077189 1127470525783928731139473)
                    ·
                      rfl

theorem cell23_6587223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_6587223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587223 prefixEnd_6587223 := by exact prefixLift 6587223
  have htrace : WordTrace (prefixWord ++ tailWord_6587223) baseStart_6587223 baseEnd_6587223 := by
    simpa [prefixWord, tailWord_6587223, baseEnd_6587223] using wordTrace_append hprefix tailTrace_6587223
  have hstable : (prefixWord ++ tailWord_6587223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587223).length < 2 ^ (prefixWord ++ tailWord_6587223).sum := by decide
  have hdescent : baseEnd_6587223 < baseStart_6587223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587236 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 6]
def baseStart_6587236 : Nat := 118140960795 + 6587236 * 2 ^ 59
def prefixEnd_6587236 : Nat := 4983230072969 + 3 ^ 40 * 6587236 * 2
def baseEnd_6587236 : Nat := 375824250288921626950651

theorem tailTrace_6587236 : CollatzResearch.WordTrace tailWord_6587236 prefixEnd_6587236 375824250288921626950651 := by
  unfold tailWord_6587236
  simp only [CollatzResearch.WordTrace]
  refine ⟨120128117381788228593630781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160170823175717638124841041 120128117381788228593630781)
  ·
    refine ⟨45048044018170585722611543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120128117381788228593630781 45048044018170585722611543)
    ·
      refine ⟨67572066027255878583917315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45048044018170585722611543 67572066027255878583917315)
      ·
        refine ⟨101358099040883817875875973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67572066027255878583917315 101358099040883817875875973)
        ·
          refine ⟨19004643570165715851726745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101358099040883817875875973 19004643570165715851726745)
          ·
            refine ⟨14253482677624286888795059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19004643570165715851726745 14253482677624286888795059)
            ·
              refine ⟨21380224016436430333192589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14253482677624286888795059 21380224016436430333192589)
              ·
                refine ⟨8017584006163661374947221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21380224016436430333192589 8017584006163661374947221)
                ·
                  refine ⟨375824250288921626950651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8017584006163661374947221 375824250288921626950651)
                  ·
                    rfl

theorem cell23_6587236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_6587236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587236 prefixEnd_6587236 := by exact prefixLift 6587236
  have htrace : WordTrace (prefixWord ++ tailWord_6587236) baseStart_6587236 baseEnd_6587236 := by
    simpa [prefixWord, tailWord_6587236, baseEnd_6587236] using wordTrace_append hprefix tailTrace_6587236
  have hstable : (prefixWord ++ tailWord_6587236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587236).length < 2 ^ (prefixWord ++ tailWord_6587236).sum := by decide
  have hdescent : baseEnd_6587236 < baseStart_6587236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587273 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 2, 3, 2]
def baseStart_6587273 : Nat := 118140960795 + 6587273 * 2 ^ 59
def prefixEnd_6587273 : Nat := 4983230072969 + 3 ^ 40 * 6587273 * 2
def baseEnd_6587273 : Nat := 3382437251384510997793189

theorem tailTrace_6587273 : CollatzResearch.WordTrace tailWord_6587273 prefixEnd_6587273 3382437251384510997793189 := by
  unfold tailWord_6587273
  simp only [CollatzResearch.WordTrace]
  refine ⟨240257584264442412506358473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160171722842961608337572315 240257584264442412506358473)
  ·
    refine ⟨180193188198331809379768855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240257584264442412506358473 180193188198331809379768855)
    ·
      refine ⟨270289782297497714069653283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180193188198331809379768855 270289782297497714069653283)
      ·
        refine ⟨405434673446246571104479925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270289782297497714069653283 405434673446246571104479925)
        ·
          refine ⟨38009500635585616041044993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 405434673446246571104479925 38009500635585616041044993)
          ·
            refine ⟨28507125476689212030783745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38009500635585616041044993 28507125476689212030783745)
            ·
              refine ⟨21380344107516909023087809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28507125476689212030783745 21380344107516909023087809)
              ·
                refine ⟨16035258080637681767315857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21380344107516909023087809 16035258080637681767315857)
                ·
                  refine ⟨12026443560478261325486893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16035258080637681767315857 12026443560478261325486893)
                  ·
                    refine ⟨4509916335179347997057585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12026443560478261325486893 4509916335179347997057585)
                    ·
                      refine ⟨3382437251384510997793189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4509916335179347997057585 3382437251384510997793189)
                      ·
                        rfl

theorem cell23_6587273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 3, 2].length) (baseStart_6587273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587273 prefixEnd_6587273 := by exact prefixLift 6587273
  have htrace : WordTrace (prefixWord ++ tailWord_6587273) baseStart_6587273 baseEnd_6587273 := by
    simpa [prefixWord, tailWord_6587273, baseEnd_6587273] using wordTrace_append hprefix tailTrace_6587273
  have hstable : (prefixWord ++ tailWord_6587273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587273).length < 2 ^ (prefixWord ++ tailWord_6587273).sum := by decide
  have hdescent : baseEnd_6587273 < baseStart_6587273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587289 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_6587289 : Nat := 118140960795 + 6587289 * 2 ^ 59
def prefixEnd_6587289 : Nat := 4983230072969 + 3 ^ 40 * 6587289 * 2
def baseEnd_6587289 : Nat := 3382445467074982935193115

theorem tailTrace_6587289 : CollatzResearch.WordTrace tailWord_6587289 prefixEnd_6587289 3382445467074982935193115 := by
  unfold tailWord_6587289
  simp only [CollatzResearch.WordTrace]
  refine ⟨240258167832384447238940921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160172111888256298159293947 240258167832384447238940921)
  ·
    refine ⟨180193625874288335429205691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240258167832384447238940921 180193625874288335429205691)
    ·
      refine ⟨270290438811432503143808537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180193625874288335429205691 270290438811432503143808537)
      ·
        refine ⟨202717829108574377357856403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270290438811432503143808537 202717829108574377357856403)
        ·
          refine ⟨304076743662861566036784605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202717829108574377357856403 304076743662861566036784605)
          ·
            refine ⟨114028778873573087263794227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304076743662861566036784605 114028778873573087263794227)
            ·
              refine ⟨171043168310359630895691341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114028778873573087263794227 171043168310359630895691341)
              ·
                refine ⟨64141188116384861585884253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171043168310359630895691341 64141188116384861585884253)
                ·
                  refine ⟨24052945543644323094706595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64141188116384861585884253 24052945543644323094706595)
                  ·
                    refine ⟨36079418315466484642059893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24052945543644323094706595 36079418315466484642059893)
                    ·
                      refine ⟨3382445467074982935193115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36079418315466484642059893 3382445467074982935193115)
                      ·
                        rfl

theorem cell23_6587289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_6587289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587289 prefixEnd_6587289 := by exact prefixLift 6587289
  have htrace : WordTrace (prefixWord ++ tailWord_6587289) baseStart_6587289 baseEnd_6587289 := by
    simpa [prefixWord, tailWord_6587289, baseEnd_6587289] using wordTrace_append hprefix tailTrace_6587289
  have hstable : (prefixWord ++ tailWord_6587289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587289).length < 2 ^ (prefixWord ++ tailWord_6587289).sum := by decide
  have hdescent : baseEnd_6587289 < baseStart_6587289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587299 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 6]
def baseStart_6587299 : Nat := 118140960795 + 6587299 * 2 ^ 59
def prefixEnd_6587299 : Nat := 4983230072969 + 3 ^ 40 * 6587299 * 2
def baseEnd_6587299 : Nat := 3382450601881527896068069

theorem tailTrace_6587299 : CollatzResearch.WordTrace tailWord_6587299 prefixEnd_6587299 3382450601881527896068069 := by
  unfold tailWord_6587299
  simp only [CollatzResearch.WordTrace]
  refine ⟨240258532562348218946804951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160172355041565479297869967 240258532562348218946804951)
  ·
    refine ⟨360387798843522328420207427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240258532562348218946804951 360387798843522328420207427)
    ·
      refine ⟨540581698265283492630311141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360387798843522328420207427 540581698265283492630311141)
      ·
        refine ⟨101359068424740654868183339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 540581698265283492630311141 101359068424740654868183339)
        ·
          refine ⟨152038602637110982302275009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101359068424740654868183339 152038602637110982302275009)
          ·
            refine ⟨114028951977833236726706257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152038602637110982302275009 114028951977833236726706257)
            ·
              refine ⟨85521713983374927545029693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114028951977833236726706257 85521713983374927545029693)
              ·
                refine ⟨32070642743765597829386135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85521713983374927545029693 32070642743765597829386135)
                ·
                  refine ⟨48105964115648396744079203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32070642743765597829386135 48105964115648396744079203)
                  ·
                    refine ⟨72158946173472595116118805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48105964115648396744079203 72158946173472595116118805)
                    ·
                      refine ⟨3382450601881527896068069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72158946173472595116118805 3382450601881527896068069)
                      ·
                        rfl

theorem cell23_6587299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_6587299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587299 prefixEnd_6587299 := by exact prefixLift 6587299
  have htrace : WordTrace (prefixWord ++ tailWord_6587299) baseStart_6587299 baseEnd_6587299 := by
    simpa [prefixWord, tailWord_6587299, baseEnd_6587299] using wordTrace_append hprefix tailTrace_6587299
  have hstable : (prefixWord ++ tailWord_6587299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587299).length < 2 ^ (prefixWord ++ tailWord_6587299).sum := by decide
  have hdescent : baseEnd_6587299 < baseStart_6587299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587320 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 1, 1, 4]
def baseStart_6587320 : Nat := 118140960795 + 6587320 * 2 ^ 59
def prefixEnd_6587320 : Nat := 4983230072969 + 3 ^ 40 * 6587320 * 2
def baseEnd_6587320 : Nat := 3382461384975272313905473

theorem tailTrace_6587320 : CollatzResearch.WordTrace tailWord_6587320 prefixEnd_6587320 3382461384975272313905473 := by
  unfold tailWord_6587320
  simp only [CollatzResearch.WordTrace]
  refine ⟨120129649247636069766659707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160172865663514759688879609 120129649247636069766659707)
  ·
    refine ⟨180194473871454104649989561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120129649247636069766659707 180194473871454104649989561)
    ·
      refine ⟨135145855403590578487492171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180194473871454104649989561 135145855403590578487492171)
      ·
        refine ⟨202718783105385867731238257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135145855403590578487492171 202718783105385867731238257)
        ·
          refine ⟨152039087329039400798428693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202718783105385867731238257 152039087329039400798428693)
          ·
            refine ⟨7126832218548721912426345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152039087329039400798428693 7126832218548721912426345)
            ·
              refine ⟨5345124163911541434319759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7126832218548721912426345 5345124163911541434319759)
              ·
                refine ⟨8017686245867312151479639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5345124163911541434319759 8017686245867312151479639)
                ·
                  refine ⟨12026529368800968227219459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8017686245867312151479639 12026529368800968227219459)
                  ·
                    refine ⟨18039794053201452340829189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12026529368800968227219459 18039794053201452340829189)
                    ·
                      refine ⟨3382461384975272313905473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18039794053201452340829189 3382461384975272313905473)
                      ·
                        rfl

theorem cell23_6587320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_6587320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587320 prefixEnd_6587320 := by exact prefixLift 6587320
  have htrace : WordTrace (prefixWord ++ tailWord_6587320) baseStart_6587320 baseEnd_6587320 := by
    simpa [prefixWord, tailWord_6587320, baseEnd_6587320] using wordTrace_append hprefix tailTrace_6587320
  have hstable : (prefixWord ++ tailWord_6587320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587320).length < 2 ^ (prefixWord ++ tailWord_6587320).sum := by decide
  have hdescent : baseEnd_6587320 < baseStart_6587320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587350 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_6587350 : Nat := 118140960795 + 6587350 * 2 ^ 59
def prefixEnd_6587350 : Nat := 4983230072969 + 3 ^ 40 * 6587350 * 2
def baseEnd_6587350 : Nat := 3382476789394907196530335

theorem tailTrace_6587350 : CollatzResearch.WordTrace tailWord_6587350 prefixEnd_6587350 3382476789394907196530335 := by
  unfold tailWord_6587350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15016274542822715916056969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160173595123442303104607669 15016274542822715916056969)
  ·
    refine ⟨11262205907117036937042727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15016274542822715916056969 11262205907117036937042727)
    ·
      refine ⟨16893308860675555405564091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11262205907117036937042727 16893308860675555405564091)
      ·
        refine ⟨25339963291013333108346137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16893308860675555405564091 25339963291013333108346137)
        ·
          refine ⟨19004972468259999831259603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25339963291013333108346137 19004972468259999831259603)
          ·
            refine ⟨28507458702389999746889405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19004972468259999831259603 28507458702389999746889405)
            ·
              refine ⟨10690297013396249905083527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28507458702389999746889405 10690297013396249905083527)
              ·
                refine ⟨16035445520094374857625291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10690297013396249905083527 16035445520094374857625291)
                ·
                  refine ⟨24053168280141562286437937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16035445520094374857625291 24053168280141562286437937)
                  ·
                    refine ⟨18039876210106171714828453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24053168280141562286437937 18039876210106171714828453)
                    ·
                      refine ⟨3382476789394907196530335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18039876210106171714828453 3382476789394907196530335)
                      ·
                        rfl

theorem cell23_6587350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_6587350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587350 prefixEnd_6587350 := by exact prefixLift 6587350
  have htrace : WordTrace (prefixWord ++ tailWord_6587350) baseStart_6587350 baseEnd_6587350 := by
    simpa [prefixWord, tailWord_6587350, baseEnd_6587350] using wordTrace_append hprefix tailTrace_6587350
  have hstable : (prefixWord ++ tailWord_6587350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587350).length < 2 ^ (prefixWord ++ tailWord_6587350).sum := by decide
  have hdescent : baseEnd_6587350 < baseStart_6587350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587353 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 3]
def baseStart_6587353 : Nat := 118140960795 + 6587353 * 2 ^ 59
def prefixEnd_6587353 : Nat := 4983230072969 + 3 ^ 40 * 6587353 * 2
def baseEnd_6587353 : Nat := 3382478329836870684792821

theorem tailTrace_6587353 : CollatzResearch.WordTrace tailWord_6587353 prefixEnd_6587353 3382478329836870684792821 := by
  unfold tailWord_6587353
  simp only [CollatzResearch.WordTrace]
  refine ⟨240260502104152586169270713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160173668069435057446180475 240260502104152586169270713)
  ·
    refine ⟨180195376578114439626953035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240260502104152586169270713 180195376578114439626953035)
    ·
      refine ⟨270293064867171659440429553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180195376578114439626953035 270293064867171659440429553)
      ·
        refine ⟨202719798650378744580322165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270293064867171659440429553 202719798650378744580322165)
        ·
          refine ⟨19004981123473007304405203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202719798650378744580322165 19004981123473007304405203)
          ·
            refine ⟨28507471685209510956607805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19004981123473007304405203 28507471685209510956607805)
            ·
              refine ⟨10690301881953566608727927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28507471685209510956607805 10690301881953566608727927)
              ·
                refine ⟨16035452822930349913091891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10690301881953566608727927 16035452822930349913091891)
                ·
                  refine ⟨24053179234395524869637837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16035452822930349913091891 24053179234395524869637837)
                  ·
                    refine ⟨9019942212898321826114189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24053179234395524869637837 9019942212898321826114189)
                    ·
                      refine ⟨3382478329836870684792821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9019942212898321826114189 3382478329836870684792821)
                      ·
                        rfl

theorem cell23_6587353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_6587353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587353 prefixEnd_6587353 := by exact prefixLift 6587353
  have htrace : WordTrace (prefixWord ++ tailWord_6587353) baseStart_6587353 baseEnd_6587353 := by
    simpa [prefixWord, tailWord_6587353, baseEnd_6587353] using wordTrace_append hprefix tailTrace_6587353
  have hstable : (prefixWord ++ tailWord_6587353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587353).length < 2 ^ (prefixWord ++ tailWord_6587353).sum := by decide
  have hdescent : baseEnd_6587353 < baseStart_6587353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587444 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_6587444 : Nat := 118140960795 + 6587444 * 2 ^ 59
def prefixEnd_6587444 : Nat := 4983230072969 + 3 ^ 40 * 6587444 * 2
def baseEnd_6587444 : Nat := 3382525056576429828754903

theorem tailTrace_6587444 : CollatzResearch.WordTrace tailWord_6587444 prefixEnd_6587444 3382525056576429828754903 := by
  unfold tailWord_6587444
  simp only [CollatzResearch.WordTrace]
  refine ⟨120131910573411454355416693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160175880764548605807222257 120131910573411454355416693)
  ·
    refine ⟨11262366616257323845820315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120131910573411454355416693 11262366616257323845820315)
    ·
      refine ⟨16893549924385985768730473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11262366616257323845820315 16893549924385985768730473)
      ·
        refine ⟨12670162443289489326547855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16893549924385985768730473 12670162443289489326547855)
        ·
          refine ⟨19005243664934233989821783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12670162443289489326547855 19005243664934233989821783)
          ·
            refine ⟨28507865497401350984732675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19005243664934233989821783 28507865497401350984732675)
            ·
              refine ⟨42761798246102026477099013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28507865497401350984732675 42761798246102026477099013)
              ·
                refine ⟨8017837171144129964456065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42761798246102026477099013 8017837171144129964456065)
                ·
                  refine ⟨6013377878358097473342049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8017837171144129964456065 6013377878358097473342049)
                  ·
                    refine ⟨4510033408768573105006537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6013377878358097473342049 4510033408768573105006537)
                    ·
                      refine ⟨3382525056576429828754903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510033408768573105006537 3382525056576429828754903)
                      ·
                        rfl

theorem cell23_6587444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_6587444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587444 prefixEnd_6587444 := by exact prefixLift 6587444
  have htrace : WordTrace (prefixWord ++ tailWord_6587444) baseStart_6587444 baseEnd_6587444 := by
    simpa [prefixWord, tailWord_6587444, baseEnd_6587444] using wordTrace_append hprefix tailTrace_6587444
  have hstable : (prefixWord ++ tailWord_6587444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587444).length < 2 ^ (prefixWord ++ tailWord_6587444).sum := by decide
  have hdescent : baseEnd_6587444 < baseStart_6587444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587450 : List Nat := [3, 1, 1, 1, 3, 1, 6, 2, 5]
def baseStart_6587450 : Nat := 118140960795 + 6587450 * 2 ^ 59
def prefixEnd_6587450 : Nat := 4983230072969 + 3 ^ 40 * 6587450 * 2
def baseEnd_6587450 : Nat := 375836459717817422808875

theorem tailTrace_6587450 : CollatzResearch.WordTrace tailWord_6587450 prefixEnd_6587450 375836459717817422808875 := by
  unfold tailWord_6587450
  simp only [CollatzResearch.WordTrace]
  refine ⟨60066009996200292933887951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160176026656534114490367869 60066009996200292933887951)
  ·
    refine ⟨90099014994300439400831927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60066009996200292933887951 90099014994300439400831927)
    ·
      refine ⟨135148522491450659101247891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90099014994300439400831927 135148522491450659101247891)
      ·
        refine ⟨202722783737175988651871837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135148522491450659101247891 202722783737175988651871837)
        ·
          refine ⟨76021043901440995744451939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202722783737175988651871837 76021043901440995744451939)
          ·
            refine ⟨114031565852161493616677909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76021043901440995744451939 114031565852161493616677909)
            ·
              refine ⟨5345229649320070013281777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114031565852161493616677909 5345229649320070013281777)
              ·
                refine ⟨4008922236990052509961333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5345229649320070013281777 4008922236990052509961333)
                ·
                  refine ⟨375836459717817422808875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4008922236990052509961333 375836459717817422808875)
                  ·
                    rfl

theorem cell23_6587450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_6587450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587450 prefixEnd_6587450 := by exact prefixLift 6587450
  have htrace : WordTrace (prefixWord ++ tailWord_6587450) baseStart_6587450 baseEnd_6587450 := by
    simpa [prefixWord, tailWord_6587450, baseEnd_6587450] using wordTrace_append hprefix tailTrace_6587450
  have hstable : (prefixWord ++ tailWord_6587450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587450).length < 2 ^ (prefixWord ++ tailWord_6587450).sum := by decide
  have hdescent : baseEnd_6587450 < baseStart_6587450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587456 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_6587456 : Nat := 118140960795 + 6587456 * 2 ^ 59
def prefixEnd_6587456 : Nat := 4983230072969 + 3 ^ 40 * 6587456 * 2
def baseEnd_6587456 : Nat := 3382531218344283781804847

theorem tailTrace_6587456 : CollatzResearch.WordTrace tailWord_6587456 prefixEnd_6587456 3382531218344283781804847 := by
  unfold tailWord_6587456
  simp only [CollatzResearch.WordTrace]
  refine ⟨120132129411389717380135111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160176172548519623173513481 120132129411389717380135111)
  ·
    refine ⟨180198194117084576070202667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120132129411389717380135111 180198194117084576070202667)
    ·
      refine ⟨270297291175626864105304001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180198194117084576070202667 270297291175626864105304001)
      ·
        refine ⟨202722968381720148078978001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270297291175626864105304001 202722968381720148078978001)
        ·
          refine ⟨152042226286290111059233501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202722968381720148078978001 152042226286290111059233501)
          ·
            refine ⟨57015834857358791647212563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152042226286290111059233501 57015834857358791647212563)
            ·
              refine ⟨85523752286038187470818845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57015834857358791647212563 85523752286038187470818845)
              ·
                refine ⟨32071407107264320301557067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85523752286038187470818845 32071407107264320301557067)
                ·
                  refine ⟨48107110660896480452335601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32071407107264320301557067 48107110660896480452335601)
                  ·
                    refine ⟨36080332995672360339251701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48107110660896480452335601 36080332995672360339251701)
                    ·
                      refine ⟨3382531218344283781804847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36080332995672360339251701 3382531218344283781804847)
                      ·
                        rfl

theorem cell23_6587456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_6587456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587456 prefixEnd_6587456 := by exact prefixLift 6587456
  have htrace : WordTrace (prefixWord ++ tailWord_6587456) baseStart_6587456 baseEnd_6587456 := by
    simpa [prefixWord, tailWord_6587456, baseEnd_6587456] using wordTrace_append hprefix tailTrace_6587456
  have hstable : (prefixWord ++ tailWord_6587456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587456).length < 2 ^ (prefixWord ++ tailWord_6587456).sum := by decide
  have hdescent : baseEnd_6587456 < baseStart_6587456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587493 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_6587493 : Nat := 118140960795 + 6587493 * 2 ^ 59
def prefixEnd_6587493 : Nat := 4983230072969 + 3 ^ 40 * 6587493 * 2
def baseEnd_6587493 : Nat := 1127516739042833379014059

theorem tailTrace_6587493 : CollatzResearch.WordTrace tailWord_6587493 prefixEnd_6587493 1127516739042833379014059 := by
  unfold tailWord_6587493
  simp only [CollatzResearch.WordTrace]
  refine ⟨240265608323645390079367133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160177072215763593386244755 240265608323645390079367133)
  ·
    refine ⟨90099603121367021279762675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240265608323645390079367133 90099603121367021279762675)
    ·
      refine ⟨135149404682050531919644013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90099603121367021279762675 135149404682050531919644013)
      ·
        refine ⟨50681026755768949469866505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135149404682050531919644013 50681026755768949469866505)
        ·
          refine ⟨38010770066826712102399879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50681026755768949469866505 38010770066826712102399879)
          ·
            refine ⟨57016155100240068153599819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38010770066826712102399879 57016155100240068153599819)
            ·
              refine ⟨85524232650360102230399729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57016155100240068153599819 85524232650360102230399729)
              ·
                refine ⟨64143174487770076672799797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85524232650360102230399729 64143174487770076672799797)
                ·
                  refine ⟨6013422608228444688074981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64143174487770076672799797 6013422608228444688074981)
                  ·
                    refine ⟨1127516739042833379014059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6013422608228444688074981 1127516739042833379014059)
                    ·
                      rfl

theorem cell23_6587493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_6587493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587493 prefixEnd_6587493 := by exact prefixLift 6587493
  have htrace : WordTrace (prefixWord ++ tailWord_6587493) baseStart_6587493 baseEnd_6587493 := by
    simpa [prefixWord, tailWord_6587493, baseEnd_6587493] using wordTrace_append hprefix tailTrace_6587493
  have hstable : (prefixWord ++ tailWord_6587493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587493).length < 2 ^ (prefixWord ++ tailWord_6587493).sum := by decide
  have hdescent : baseEnd_6587493 < baseStart_6587493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587503 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 3]
def baseStart_6587503 : Nat := 118140960795 + 6587503 * 2 ^ 59
def prefixEnd_6587503 : Nat := 4983230072969 + 3 ^ 40 * 6587503 * 2
def baseEnd_6587503 : Nat := 3382555351935045097917131

theorem tailTrace_6587503 : CollatzResearch.WordTrace tailWord_6587503 prefixEnd_6587503 3382555351935045097917131 := by
  unfold tailWord_6587503
  simp only [CollatzResearch.WordTrace]
  refine ⟨240265973053609161787231163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160177315369072774524820775 240265973053609161787231163)
  ·
    refine ⟨360398959580413742680846745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240265973053609161787231163 360398959580413742680846745)
    ·
      refine ⟨270299219685310307010635059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360398959580413742680846745 270299219685310307010635059)
      ·
        refine ⟨405448829527965460515952589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270299219685310307010635059 405448829527965460515952589)
        ·
          refine ⟨152043311072987047693482221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405448829527965460515952589 152043311072987047693482221)
          ·
            refine ⟨57016241652370142885055833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152043311072987047693482221 57016241652370142885055833)
            ·
              refine ⟨42762181239277607163791875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57016241652370142885055833 42762181239277607163791875)
              ·
                refine ⟨64143271858916410745687813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42762181239277607163791875 64143271858916410745687813)
                ·
                  refine ⟨12026863473546827014816465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64143271858916410745687813 12026863473546827014816465)
                  ·
                    refine ⟨9020147605160120261112349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12026863473546827014816465 9020147605160120261112349)
                    ·
                      refine ⟨3382555351935045097917131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9020147605160120261112349 3382555351935045097917131)
                      ·
                        rfl

theorem cell23_6587503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_6587503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587503 prefixEnd_6587503 := by exact prefixLift 6587503
  have htrace : WordTrace (prefixWord ++ tailWord_6587503) baseStart_6587503 baseEnd_6587503 := by
    simpa [prefixWord, tailWord_6587503, baseEnd_6587503] using wordTrace_append hprefix tailTrace_6587503
  have hstable : (prefixWord ++ tailWord_6587503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587503).length < 2 ^ (prefixWord ++ tailWord_6587503).sum := by decide
  have hdescent : baseEnd_6587503 < baseStart_6587503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587544 : List Nat := [2, 1, 2, 4, 2, 3, 1, 3, 1, 4]
def baseStart_6587544 : Nat := 118140960795 + 6587544 * 2 ^ 59
def prefixEnd_6587544 : Nat := 4983230072969 + 3 ^ 40 * 6587544 * 2
def baseEnd_6587544 : Nat := 1127525468213959812501481

theorem tailTrace_6587544 : CollatzResearch.WordTrace tailWord_6587544 prefixEnd_6587544 1127525468213959812501481 := by
  unfold tailWord_6587544
  simp only [CollatzResearch.WordTrace]
  refine ⟨120133734223230312894736843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160178312297640417192982457 120133734223230312894736843)
  ·
    refine ⟨180200601334845469342105265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120133734223230312894736843 180200601334845469342105265)
    ·
      refine ⟨135150451001134102006578949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180200601334845469342105265 135150451001134102006578949)
      ·
        refine ⟨25340709562712644126233553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135150451001134102006578949 25340709562712644126233553)
        ·
          refine ⟨19005532172034483094675165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25340709562712644126233553 19005532172034483094675165)
          ·
            refine ⟨7127074564512931160503187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19005532172034483094675165 7127074564512931160503187)
            ·
              refine ⟨10690611846769396740754781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127074564512931160503187 10690611846769396740754781)
              ·
                refine ⟨4008979442538523777783043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10690611846769396740754781 4008979442538523777783043)
                ·
                  refine ⟨6013469163807785666674565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4008979442538523777783043 6013469163807785666674565)
                  ·
                    refine ⟨1127525468213959812501481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6013469163807785666674565 1127525468213959812501481)
                    ·
                      rfl

theorem cell23_6587544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_6587544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587544 prefixEnd_6587544 := by exact prefixLift 6587544
  have htrace : WordTrace (prefixWord ++ tailWord_6587544) baseStart_6587544 baseEnd_6587544 := by
    simpa [prefixWord, tailWord_6587544, baseEnd_6587544] using wordTrace_append hprefix tailTrace_6587544
  have hstable : (prefixWord ++ tailWord_6587544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587544).length < 2 ^ (prefixWord ++ tailWord_6587544).sum := by decide
  have hdescent : baseEnd_6587544 < baseStart_6587544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587567 : List Nat := [1, 1, 2, 1, 2, 3, 2, 6, 1, 1, 3]
def baseStart_6587567 : Nat := 118140960795 + 6587567 * 2 ^ 59
def prefixEnd_6587567 : Nat := 4983230072969 + 3 ^ 40 * 6587567 * 2
def baseEnd_6587567 : Nat := 3382588214696932847516837

theorem tailTrace_6587567 : CollatzResearch.WordTrace tailWord_6587567 prefixEnd_6587567 3382588214696932847516837 := by
  unfold tailWord_6587567
  simp only [CollatzResearch.WordTrace]
  refine ⟨240268307325377300717560955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160178871550251533811707303 240268307325377300717560955)
  ·
    refine ⟨360402460988065951076341433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240268307325377300717560955 360402460988065951076341433)
    ·
      refine ⟨270301845741049463307256075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360402460988065951076341433 270301845741049463307256075)
      ·
        refine ⟨405452768611574194960884113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270301845741049463307256075 405452768611574194960884113)
        ·
          refine ⟨304089576458680646220663085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405452768611574194960884113 304089576458680646220663085)
          ·
            refine ⟨114033591172005242332748657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304089576458680646220663085 114033591172005242332748657)
            ·
              refine ⟨85525193379003931749561493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114033591172005242332748657 85525193379003931749561493)
              ·
                refine ⟨4008993439640809300760695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85525193379003931749561493 4008993439640809300760695)
                ·
                  refine ⟨6013490159461213951141043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4008993439640809300760695 6013490159461213951141043)
                  ·
                    refine ⟨9020235239191820926711565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6013490159461213951141043 9020235239191820926711565)
                    ·
                      refine ⟨3382588214696932847516837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9020235239191820926711565 3382588214696932847516837)
                      ·
                        rfl

theorem cell23_6587567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 1, 3].length) (baseStart_6587567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587567 prefixEnd_6587567 := by exact prefixLift 6587567
  have htrace : WordTrace (prefixWord ++ tailWord_6587567) baseStart_6587567 baseEnd_6587567 := by
    simpa [prefixWord, tailWord_6587567, baseEnd_6587567] using wordTrace_append hprefix tailTrace_6587567
  have hstable : (prefixWord ++ tailWord_6587567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587567).length < 2 ^ (prefixWord ++ tailWord_6587567).sum := by decide
  have hdescent : baseEnd_6587567 < baseStart_6587567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587574 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_6587574 : Nat := 118140960795 + 6587574 * 2 ^ 59
def prefixEnd_6587574 : Nat := 4983230072969 + 3 ^ 40 * 6587574 * 2
def baseEnd_6587574 : Nat := 375843534340168257792145

theorem tailTrace_6587574 : CollatzResearch.WordTrace tailWord_6587574 prefixEnd_6587574 375843534340168257792145 := by
  unfold tailWord_6587574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15016785164771996307066611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160179041757567960608710517 15016785164771996307066611)
  ·
    refine ⟨22525177747157994460599917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15016785164771996307066611 22525177747157994460599917)
    ·
      refine ⟨8446941655184247922724969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22525177747157994460599917 8446941655184247922724969)
      ·
        refine ⟨6335206241388185942043727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8446941655184247922724969 6335206241388185942043727)
        ·
          refine ⟨9502809362082278913065591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335206241388185942043727 9502809362082278913065591)
          ·
            refine ⟨14254214043123418369598387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9502809362082278913065591 14254214043123418369598387)
            ·
              refine ⟨21381321064685127554397581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14254214043123418369598387 21381321064685127554397581)
              ·
                refine ⟨8017995399256922832899093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21381321064685127554397581 8017995399256922832899093)
                ·
                  refine ⟨375843534340168257792145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8017995399256922832899093 375843534340168257792145)
                  ·
                    rfl

theorem cell23_6587574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_6587574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587574 prefixEnd_6587574 := by exact prefixLift 6587574
  have htrace : WordTrace (prefixWord ++ tailWord_6587574) baseStart_6587574 baseEnd_6587574 := by
    simpa [prefixWord, tailWord_6587574, baseEnd_6587574] using wordTrace_append hprefix tailTrace_6587574
  have hstable : (prefixWord ++ tailWord_6587574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587574).length < 2 ^ (prefixWord ++ tailWord_6587574).sum := by decide
  have hdescent : baseEnd_6587574 < baseStart_6587574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587603 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 4]
def baseStart_6587603 : Nat := 118140960795 + 6587603 * 2 ^ 59
def prefixEnd_6587603 : Nat := 4983230072969 + 3 ^ 40 * 6587603 * 2
def baseEnd_6587603 : Nat := 3382606700000494706666671

theorem tailTrace_6587603 : CollatzResearch.WordTrace tailWord_6587603 prefixEnd_6587603 3382606700000494706666671 := by
  unfold tailWord_6587603
  simp only [CollatzResearch.WordTrace]
  refine ⟨240269620353246878865871463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160179746902164585910580975 240269620353246878865871463)
  ·
    refine ⟨360404430529870318298807195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240269620353246878865871463 360404430529870318298807195)
    ·
      refine ⟨540606645794805477448210793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360404430529870318298807195 540606645794805477448210793)
      ·
        refine ⟨405454984346104108086158095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540606645794805477448210793 405454984346104108086158095)
        ·
          refine ⟨608182476519156162129237143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405454984346104108086158095 608182476519156162129237143)
          ·
            refine ⟨912273714778734243193855715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608182476519156162129237143 912273714778734243193855715)
            ·
              refine ⟨1368410572168101364790783573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912273714778734243193855715 1368410572168101364790783573)
              ·
                refine ⟨16036061392594937868641995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1368410572168101364790783573 16036061392594937868641995)
                ·
                  refine ⟨24054092088892406802962993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16036061392594937868641995 24054092088892406802962993)
                  ·
                    refine ⟨18040569066669305102222245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24054092088892406802962993 18040569066669305102222245)
                    ·
                      refine ⟨3382606700000494706666671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18040569066669305102222245 3382606700000494706666671)
                      ·
                        rfl

theorem cell23_6587603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_6587603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587603 prefixEnd_6587603 := by exact prefixLift 6587603
  have htrace : WordTrace (prefixWord ++ tailWord_6587603) baseStart_6587603 baseEnd_6587603 := by
    simpa [prefixWord, tailWord_6587603, baseEnd_6587603] using wordTrace_append hprefix tailTrace_6587603
  have hstable : (prefixWord ++ tailWord_6587603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587603).length < 2 ^ (prefixWord ++ tailWord_6587603).sum := by decide
  have hdescent : baseEnd_6587603 < baseStart_6587603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587613 : List Nat := [1, 4, 3, 2, 13]
def baseStart_6587613 : Nat := 118140960795 + 6587613 * 2 ^ 59
def prefixEnd_6587613 : Nat := 4983230072969 + 3 ^ 40 * 6587613 * 2
def baseEnd_6587613 : Nat := 4640071103987708734625

theorem tailTrace_6587613 : CollatzResearch.WordTrace tailWord_6587613 prefixEnd_6587613 4640071103987708734625 := by
  unfold tailWord_6587613
  simp only [CollatzResearch.WordTrace]
  refine ⟨240269985083210650573735493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160179990055473767049156995 240269985083210650573735493)
  ·
    refine ⟨45050622203101996982575405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240269985083210650573735493 45050622203101996982575405)
    ·
      refine ⟨16893983326163248868465777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45050622203101996982575405 16893983326163248868465777)
      ·
        refine ⟨12670487494622436651349333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16893983326163248868465777 12670487494622436651349333)
        ·
          refine ⟨4640071103987708734625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12670487494622436651349333 4640071103987708734625)
          ·
            rfl

theorem cell23_6587613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 13].length) (baseStart_6587613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587613 prefixEnd_6587613 := by exact prefixLift 6587613
  have htrace : WordTrace (prefixWord ++ tailWord_6587613) baseStart_6587613 baseEnd_6587613 := by
    simpa [prefixWord, tailWord_6587613, baseEnd_6587613] using wordTrace_append hprefix tailTrace_6587613
  have hstable : (prefixWord ++ tailWord_6587613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587613).length < 2 ^ (prefixWord ++ tailWord_6587613).sum := by decide
  have hdescent : baseEnd_6587613 < baseStart_6587613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587617 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 2, 4]
def baseStart_6587617 : Nat := 118140960795 + 6587617 * 2 ^ 59
def prefixEnd_6587617 : Nat := 4983230072969 + 3 ^ 40 * 6587617 * 2
def baseEnd_6587617 : Nat := 1127537962909885883963869

theorem tailTrace_6587617 : CollatzResearch.WordTrace tailWord_6587617 prefixEnd_6587617 1127537962909885883963869 := by
  unfold tailWord_6587617
  simp only [CollatzResearch.WordTrace]
  refine ⟨240270130975196159256881105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160180087316797439504587403 240270130975196159256881105)
  ·
    refine ⟨180202598231397119442660829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240270130975196159256881105 180202598231397119442660829)
    ·
      refine ⟨67575974336773919790997811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180202598231397119442660829 67575974336773919790997811)
      ·
        refine ⟨101363961505160879686496717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67575974336773919790997811 101363961505160879686496717)
        ·
          refine ⟨38011485564435329882436269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101363961505160879686496717 38011485564435329882436269)
          ·
            refine ⟨14254307086663248705913601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38011485564435329882436269 14254307086663248705913601)
            ·
              refine ⟨10690730314997436529435201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14254307086663248705913601 10690730314997436529435201)
              ·
                refine ⟨8018047736248077397076401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10690730314997436529435201 8018047736248077397076401)
                ·
                  refine ⟨6013535802186058047807301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8018047736248077397076401 6013535802186058047807301)
                  ·
                    refine ⟨1127537962909885883963869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6013535802186058047807301 1127537962909885883963869)
                    ·
                      rfl

theorem cell23_6587617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_6587617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587617 prefixEnd_6587617 := by exact prefixLift 6587617
  have htrace : WordTrace (prefixWord ++ tailWord_6587617) baseStart_6587617 baseEnd_6587617 := by
    simpa [prefixWord, tailWord_6587617, baseEnd_6587617] using wordTrace_append hprefix tailTrace_6587617
  have hstable : (prefixWord ++ tailWord_6587617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587617).length < 2 ^ (prefixWord ++ tailWord_6587617).sum := by decide
  have hdescent : baseEnd_6587617 < baseStart_6587617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587640 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_6587640 : Nat := 118140960795 + 6587640 * 2 ^ 59
def prefixEnd_6587640 : Nat := 4983230072969 + 3 ^ 40 * 6587640 * 2
def baseEnd_6587640 : Nat := 3382625698784711061904001

theorem tailTrace_6587640 : CollatzResearch.WordTrace tailWord_6587640 prefixEnd_6587640 3382625698784711061904001 := by
  unfold tailWord_6587640
  simp only [CollatzResearch.WordTrace]
  refine ⟨120135484927056417092484187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160180646569408556123312249 120135484927056417092484187)
  ·
    refine ⟨180203227390584625638726281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120135484927056417092484187 180203227390584625638726281)
    ·
      refine ⟨135152420542938469229044711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180203227390584625638726281 135152420542938469229044711)
      ·
        refine ⟨202728630814407703843567067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135152420542938469229044711 202728630814407703843567067)
        ·
          refine ⟨304092946221611555765350601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202728630814407703843567067 304092946221611555765350601)
          ·
            refine ⟨228069709666208666824012951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304092946221611555765350601 228069709666208666824012951)
            ·
              refine ⟨342104564499313000236019427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228069709666208666824012951 342104564499313000236019427)
              ·
                refine ⟨513156846748969500354029141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342104564499313000236019427 513156846748969500354029141)
                ·
                  refine ⟨6013556797839486332273779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 513156846748969500354029141 6013556797839486332273779)
                  ·
                    refine ⟨9020335196759229498410669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6013556797839486332273779 9020335196759229498410669)
                    ·
                      refine ⟨3382625698784711061904001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9020335196759229498410669 3382625698784711061904001)
                      ·
                        rfl

theorem cell23_6587640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_6587640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587640 prefixEnd_6587640 := by exact prefixLift 6587640
  have htrace : WordTrace (prefixWord ++ tailWord_6587640) baseStart_6587640 baseEnd_6587640 := by
    simpa [prefixWord, tailWord_6587640, baseEnd_6587640] using wordTrace_append hprefix tailTrace_6587640
  have hstable : (prefixWord ++ tailWord_6587640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587640).length < 2 ^ (prefixWord ++ tailWord_6587640).sum := by decide
  have hdescent : baseEnd_6587640 < baseStart_6587640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587653 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_6587653 : Nat := 118140960795 + 6587653 * 2 ^ 59
def prefixEnd_6587653 : Nat := 4983230072969 + 3 ^ 40 * 6587653 * 2
def baseEnd_6587653 : Nat := 3382632374033219511041441

theorem tailTrace_6587653 : CollatzResearch.WordTrace tailWord_6587653 prefixEnd_6587653 3382632374033219511041441 := by
  unfold tailWord_6587653
  simp only [CollatzResearch.WordTrace]
  refine ⟨240271444003065737405191613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160180962668710491603461075 240271444003065737405191613)
  ·
    refine ⟨90101791501149651526946855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240271444003065737405191613 90101791501149651526946855)
    ·
      refine ⟨135152687251724477290420283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90101791501149651526946855 135152687251724477290420283)
      ·
        refine ⟨202729030877586715935630425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135152687251724477290420283 202729030877586715935630425)
        ·
          refine ⟨152046773158190036951722819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202729030877586715935630425 152046773158190036951722819)
          ·
            refine ⟨228070159737285055427584229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152046773158190036951722819 228070159737285055427584229)
            ·
              refine ⟨42763154950740947892672043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228070159737285055427584229 42763154950740947892672043)
              ·
                refine ⟨64144732426111421839008065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42763154950740947892672043 64144732426111421839008065)
                ·
                  refine ⟨48108549319583566379256049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64144732426111421839008065 48108549319583566379256049)
                  ·
                    refine ⟨36081411989687674784442037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48108549319583566379256049 36081411989687674784442037)
                    ·
                      refine ⟨3382632374033219511041441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36081411989687674784442037 3382632374033219511041441)
                      ·
                        rfl

theorem cell23_6587653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_6587653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587653 prefixEnd_6587653 := by exact prefixLift 6587653
  have htrace : WordTrace (prefixWord ++ tailWord_6587653) baseStart_6587653 baseEnd_6587653 := by
    simpa [prefixWord, tailWord_6587653, baseEnd_6587653] using wordTrace_append hprefix tailTrace_6587653
  have hstable : (prefixWord ++ tailWord_6587653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587653).length < 2 ^ (prefixWord ++ tailWord_6587653).sum := by decide
  have hdescent : baseEnd_6587653 < baseStart_6587653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587674 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_6587674 : Nat := 118140960795 + 6587674 * 2 ^ 59
def prefixEnd_6587674 : Nat := 4983230072969 + 3 ^ 40 * 6587674 * 2
def baseEnd_6587674 : Nat := 3382643157126963928878845

theorem tailTrace_6587674 : CollatzResearch.WordTrace tailWord_6587674 prefixEnd_6587674 3382643157126963928878845 := by
  unfold tailWord_6587674
  simp only [CollatzResearch.WordTrace]
  refine ⟨60068052483997414497926519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160181473290659771994470717 60068052483997414497926519)
  ·
    refine ⟨90102078725996121746889779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60068052483997414497926519 90102078725996121746889779)
    ·
      refine ⟨135153118088994182620334669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90102078725996121746889779 135153118088994182620334669)
      ·
        refine ⟨50682419283372818482625501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135153118088994182620334669 50682419283372818482625501)
        ·
          refine ⟨19005907231264806930984563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50682419283372818482625501 19005907231264806930984563)
          ·
            refine ⟨28508860846897210396476845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19005907231264806930984563 28508860846897210396476845)
            ·
              refine ⟨10690822817586453898678817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28508860846897210396476845 10690822817586453898678817)
              ·
                refine ⟨8018117113189840424009113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10690822817586453898678817 8018117113189840424009113)
                ·
                  refine ⟨6013587834892380318006835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8018117113189840424009113 6013587834892380318006835)
                  ·
                    refine ⟨9020381752338570477010253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6013587834892380318006835 9020381752338570477010253)
                    ·
                      refine ⟨3382643157126963928878845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9020381752338570477010253 3382643157126963928878845)
                      ·
                        rfl

theorem cell23_6587674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_6587674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587674 prefixEnd_6587674 := by exact prefixLift 6587674
  have htrace : WordTrace (prefixWord ++ tailWord_6587674) baseStart_6587674 baseEnd_6587674 := by
    simpa [prefixWord, tailWord_6587674, baseEnd_6587674] using wordTrace_append hprefix tailTrace_6587674
  have hstable : (prefixWord ++ tailWord_6587674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587674).length < 2 ^ (prefixWord ++ tailWord_6587674).sum := by decide
  have hdescent : baseEnd_6587674 < baseStart_6587674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587748 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_6587748 : Nat := 118140960795 + 6587748 * 2 ^ 59
def prefixEnd_6587748 : Nat := 4983230072969 + 3 ^ 40 * 6587748 * 2
def baseEnd_6587748 : Nat := 3382681154695396639353505

theorem tailTrace_6587748 : CollatzResearch.WordTrace tailWord_6587748 prefixEnd_6587748 3382681154695396639353505 := by
  unfold tailWord_6587748
  simp only [CollatzResearch.WordTrace]
  refine ⟨120137454468860784314949949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160183272625147712419933265 120137454468860784314949949)
  ·
    refine ⟨45051545425822794118106231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120137454468860784314949949 45051545425822794118106231)
    ·
      refine ⟨67577318138734191177159347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45051545425822794118106231 67577318138734191177159347)
      ·
        refine ⟨101365977208101286765739021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67577318138734191177159347 101365977208101286765739021)
        ·
          refine ⟨38012241453037982537152133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101365977208101286765739021 38012241453037982537152133)
          ·
            refine ⟨7127295272444621725716025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38012241453037982537152133 7127295272444621725716025)
            ·
              refine ⟨5345471454333466294287019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7127295272444621725716025 5345471454333466294287019)
              ·
                refine ⟨8018207181500199441430529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5345471454333466294287019 8018207181500199441430529)
                ·
                  refine ⟨6013655386125149581072897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8018207181500199441430529 6013655386125149581072897)
                  ·
                    refine ⟨4510241539593862185804673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6013655386125149581072897 4510241539593862185804673)
                    ·
                      refine ⟨3382681154695396639353505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510241539593862185804673 3382681154695396639353505)
                      ·
                        rfl

theorem cell23_6587748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_6587748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587748 prefixEnd_6587748 := by exact prefixLift 6587748
  have htrace : WordTrace (prefixWord ++ tailWord_6587748) baseStart_6587748 baseEnd_6587748 := by
    simpa [prefixWord, tailWord_6587748, baseEnd_6587748] using wordTrace_append hprefix tailTrace_6587748
  have hstable : (prefixWord ++ tailWord_6587748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587748).length < 2 ^ (prefixWord ++ tailWord_6587748).sum := by decide
  have hdescent : baseEnd_6587748 < baseStart_6587748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587770 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_6587770 : Nat := 118140960795 + 6587770 * 2 ^ 59
def prefixEnd_6587770 : Nat := 4983230072969 + 3 ^ 40 * 6587770 * 2
def baseEnd_6587770 : Nat := 3382692451269795553278403

theorem tailTrace_6587770 : CollatzResearch.WordTrace tailWord_6587770 prefixEnd_6587770 3382692451269795553278403 := by
  unfold tailWord_6587770
  simp only [CollatzResearch.WordTrace]
  refine ⟨60068927835910466596800191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160183807562427910924800509 60068927835910466596800191)
  ·
    refine ⟨90103391753865699895200287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60068927835910466596800191 90103391753865699895200287)
    ·
      refine ⟨135155087630798549842800431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90103391753865699895200287 135155087630798549842800431)
      ·
        refine ⟨202732631446197824764200647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135155087630798549842800431 202732631446197824764200647)
        ·
          refine ⟨304098947169296737146300971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202732631446197824764200647 304098947169296737146300971)
          ·
            refine ⟨456148420753945105719451457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304098947169296737146300971 456148420753945105719451457)
            ·
              refine ⟨342111315565458829289588593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456148420753945105719451457 342111315565458829289588593)
              ·
                refine ⟨256583486674094121967191445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342111315565458829289588593 256583486674094121967191445)
                ·
                  refine ⟨12027350937848161967212099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256583486674094121967191445 12027350937848161967212099)
                  ·
                    refine ⟨18041026406772242950818149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12027350937848161967212099 18041026406772242950818149)
                    ·
                      refine ⟨3382692451269795553278403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18041026406772242950818149 3382692451269795553278403)
                      ·
                        rfl

theorem cell23_6587770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_6587770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587770 prefixEnd_6587770 := by exact prefixLift 6587770
  have htrace : WordTrace (prefixWord ++ tailWord_6587770) baseStart_6587770 baseEnd_6587770 := by
    simpa [prefixWord, tailWord_6587770, baseEnd_6587770] using wordTrace_append hprefix tailTrace_6587770
  have hstable : (prefixWord ++ tailWord_6587770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587770).length < 2 ^ (prefixWord ++ tailWord_6587770).sum := by decide
  have hdescent : baseEnd_6587770 < baseStart_6587770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587787 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 2, 4, 2]
def baseStart_6587787 : Nat := 118140960795 + 6587787 * 2 ^ 59
def prefixEnd_6587787 : Nat := 4983230072969 + 3 ^ 40 * 6587787 * 2
def baseEnd_6587787 : Nat := 3382701180440921986765825

theorem tailTrace_6587787 : CollatzResearch.WordTrace tailWord_6587787 prefixEnd_6587787 3382701180440921986765825 := by
  unfold tailWord_6587787
  simp only [CollatzResearch.WordTrace]
  refine ⟨240276331384580278290569615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160184220923053518860379743 240276331384580278290569615)
  ·
    refine ⟨360414497076870417435854423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240276331384580278290569615 360414497076870417435854423)
    ·
      refine ⟨540621745615305626153781635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360414497076870417435854423 540621745615305626153781635)
      ·
        refine ⟨810932618422958439230672453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540621745615305626153781635 810932618422958439230672453)
        ·
          refine ⟨152049865954304707355751085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 810932618422958439230672453 152049865954304707355751085)
          ·
            refine ⟨57018699732864265258406657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152049865954304707355751085 57018699732864265258406657)
            ·
              refine ⟨42764024799648198943804993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57018699732864265258406657 42764024799648198943804993)
              ·
                refine ⟨32073018599736149207853745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42764024799648198943804993 32073018599736149207853745)
                ·
                  refine ⟨24054763949802111905890309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32073018599736149207853745 24054763949802111905890309)
                  ·
                    refine ⟨4510268240587895982354433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24054763949802111905890309 4510268240587895982354433)
                    ·
                      refine ⟨3382701180440921986765825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510268240587895982354433 3382701180440921986765825)
                      ·
                        rfl

theorem cell23_6587787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 4, 2].length) (baseStart_6587787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587787 prefixEnd_6587787 := by exact prefixLift 6587787
  have htrace : WordTrace (prefixWord ++ tailWord_6587787) baseStart_6587787 baseEnd_6587787 := by
    simpa [prefixWord, tailWord_6587787, baseEnd_6587787] using wordTrace_append hprefix tailTrace_6587787
  have hstable : (prefixWord ++ tailWord_6587787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587787).length < 2 ^ (prefixWord ++ tailWord_6587787).sum := by decide
  have hdescent : baseEnd_6587787 < baseStart_6587787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587821 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6587821 : Nat := 118140960795 + 6587821 * 2 ^ 59
def prefixEnd_6587821 : Nat := 4983230072969 + 3 ^ 40 * 6587821 * 2
def baseEnd_6587821 : Nat := 3382718638783174853740669

theorem tailTrace_6587821 : CollatzResearch.WordTrace tailWord_6587821 prefixEnd_6587821 3382718638783174853740669 := by
  unfold tailWord_6587821
  simp only [CollatzResearch.WordTrace]
  refine ⟨240277571466457102097307317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160185047644304734731538211 240277571466457102097307317)
  ·
    refine ⟨22526022324980353321622561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240277571466457102097307317 22526022324980353321622561)
    ·
      refine ⟨16894516743735264991216921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22526022324980353321622561 16894516743735264991216921)
      ·
        refine ⟨12670887557801448743412691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16894516743735264991216921 12670887557801448743412691)
        ·
          refine ⟨19006331336702173115119037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12670887557801448743412691 19006331336702173115119037)
          ·
            refine ⟨7127374251263314918169639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19006331336702173115119037 7127374251263314918169639)
            ·
              refine ⟨10691061376894972377254459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127374251263314918169639 10691061376894972377254459)
              ·
                refine ⟨16036592065342458565881689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10691061376894972377254459 16036592065342458565881689)
                ·
                  refine ⟨12027444049006843924411267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16036592065342458565881689 12027444049006843924411267)
                  ·
                    refine ⟨18041166073510265886616901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12027444049006843924411267 18041166073510265886616901)
                    ·
                      refine ⟨3382718638783174853740669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18041166073510265886616901 3382718638783174853740669)
                      ·
                        rfl

theorem cell23_6587821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6587821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587821 prefixEnd_6587821 := by exact prefixLift 6587821
  have htrace : WordTrace (prefixWord ++ tailWord_6587821) baseStart_6587821 baseEnd_6587821 := by
    simpa [prefixWord, tailWord_6587821, baseEnd_6587821] using wordTrace_append hprefix tailTrace_6587821
  have hstable : (prefixWord ++ tailWord_6587821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587821).length < 2 ^ (prefixWord ++ tailWord_6587821).sum := by decide
  have hdescent : baseEnd_6587821 < baseStart_6587821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587844 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 6]
def baseStart_6587844 : Nat := 118140960795 + 6587844 * 2 ^ 59
def prefixEnd_6587844 : Nat := 4983230072969 + 3 ^ 40 * 6587844 * 2
def baseEnd_6587844 : Nat := 375858938759803140417007

theorem tailTrace_6587844 : CollatzResearch.WordTrace tailWord_6587844 prefixEnd_6587844 375858938759803140417007 := by
  unfold tailWord_6587844
  simp only [CollatzResearch.WordTrace]
  refine ⟨120139205172686888512697293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160185606896915851350263057 120139205172686888512697293)
  ·
    refine ⟨45052201939757583192261485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120139205172686888512697293 45052201939757583192261485)
    ·
      refine ⟨16894575727409093697098057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45052201939757583192261485 16894575727409093697098057)
      ·
        refine ⟨12670931795556820272823543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16894575727409093697098057 12670931795556820272823543)
        ·
          refine ⟨19006397693335230409235315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12670931795556820272823543 19006397693335230409235315)
          ·
            refine ⟨28509596540002845613852973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19006397693335230409235315 28509596540002845613852973)
            ·
              refine ⟨10691098702501067105194865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28509596540002845613852973 10691098702501067105194865)
              ·
                refine ⟨8018324026875800328896149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10691098702501067105194865 8018324026875800328896149)
                ·
                  refine ⟨375858938759803140417007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8018324026875800328896149 375858938759803140417007)
                  ·
                    rfl

theorem cell23_6587844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_6587844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587844 prefixEnd_6587844 := by exact prefixLift 6587844
  have htrace : WordTrace (prefixWord ++ tailWord_6587844) baseStart_6587844 baseEnd_6587844 := by
    simpa [prefixWord, tailWord_6587844, baseEnd_6587844] using wordTrace_append hprefix tailTrace_6587844
  have hstable : (prefixWord ++ tailWord_6587844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587844).length < 2 ^ (prefixWord ++ tailWord_6587844).sum := by decide
  have hdescent : baseEnd_6587844 < baseStart_6587844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587854 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_6587854 : Nat := 118140960795 + 6587854 * 2 ^ 59
def prefixEnd_6587854 : Nat := 4983230072969 + 3 ^ 40 * 6587854 * 2
def baseEnd_6587854 : Nat := 3382735583644773224628017

theorem tailTrace_6587854 : CollatzResearch.WordTrace tailWord_6587854 prefixEnd_6587854 3382735583644773224628017 := by
  unfold tailWord_6587854
  simp only [CollatzResearch.WordTrace]
  refine ⟨30034846884417193591657327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160185850050225032488839077 30034846884417193591657327)
  ·
    refine ⟨45052270326625790387485991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30034846884417193591657327 45052270326625790387485991)
    ·
      refine ⟨67578405489938685581228987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45052270326625790387485991 67578405489938685581228987)
      ·
        refine ⟨101367608234908028371843481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67578405489938685581228987 101367608234908028371843481)
        ·
          refine ⟨76025706176181021278882611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101367608234908028371843481 76025706176181021278882611)
          ·
            refine ⟨114038559264271531918323917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76025706176181021278882611 114038559264271531918323917)
            ·
              refine ⟨42764459724101824469371469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114038559264271531918323917 42764459724101824469371469)
              ·
                refine ⟨16036672396538184176014301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42764459724101824469371469 16036672396538184176014301)
                ·
                  refine ⟨6013752148701819066005363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16036672396538184176014301 6013752148701819066005363)
                  ·
                    refine ⟨9020628223052728599008045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6013752148701819066005363 9020628223052728599008045)
                    ·
                      refine ⟨3382735583644773224628017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9020628223052728599008045 3382735583644773224628017)
                      ·
                        rfl

theorem cell23_6587854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_6587854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587854 prefixEnd_6587854 := by exact prefixLift 6587854
  have htrace : WordTrace (prefixWord ++ tailWord_6587854) baseStart_6587854 baseEnd_6587854 := by
    simpa [prefixWord, tailWord_6587854, baseEnd_6587854] using wordTrace_append hprefix tailTrace_6587854
  have hstable : (prefixWord ++ tailWord_6587854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587854).length < 2 ^ (prefixWord ++ tailWord_6587854).sum := by decide
  have hdescent : baseEnd_6587854 < baseStart_6587854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587887 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 4, 4]
def baseStart_6587887 : Nat := 118140960795 + 6587887 * 2 ^ 59
def prefixEnd_6587887 : Nat := 4983230072969 + 3 ^ 40 * 6587887 * 2
def baseEnd_6587887 : Nat := 1127584176168790531838455

theorem tailTrace_6587887 : CollatzResearch.WordTrace tailWord_6587887 prefixEnd_6587887 1127584176168790531838455 := by
  unfold tailWord_6587887
  simp only [CollatzResearch.WordTrace]
  refine ⟨240279978684217995369209915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160186652456145330246139943 240279978684217995369209915)
  ·
    refine ⟨360419968026326993053814873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240279978684217995369209915 360419968026326993053814873)
    ·
      refine ⟨270314976019745244790361155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360419968026326993053814873 270314976019745244790361155)
      ·
        refine ⟨405472464029617867185541733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270314976019745244790361155 405472464029617867185541733)
        ·
          refine ⟨76026087005553350097289075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405472464029617867185541733 76026087005553350097289075)
          ·
            refine ⟨114039130508330025145933613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76026087005553350097289075 114039130508330025145933613)
            ·
              refine ⟨42764673940623759429725105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114039130508330025145933613 42764673940623759429725105)
              ·
                refine ⟨32073505455467819572293829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42764673940623759429725105 32073505455467819572293829)
                ·
                  refine ⟨6013782272900216169805093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32073505455467819572293829 6013782272900216169805093)
                  ·
                    refine ⟨1127584176168790531838455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6013782272900216169805093 1127584176168790531838455)
                    ·
                      rfl

theorem cell23_6587887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 4].length) (baseStart_6587887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587887 prefixEnd_6587887 := by exact prefixLift 6587887
  have htrace : WordTrace (prefixWord ++ tailWord_6587887) baseStart_6587887 baseEnd_6587887 := by
    simpa [prefixWord, tailWord_6587887, baseEnd_6587887] using wordTrace_append hprefix tailTrace_6587887
  have hstable : (prefixWord ++ tailWord_6587887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587887).length < 2 ^ (prefixWord ++ tailWord_6587887).sum := by decide
  have hdescent : baseEnd_6587887 < baseStart_6587887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587888 : List Nat := [2, 1, 1, 1, 3, 6, 1, 3, 1, 1, 3]
def baseStart_6587888 : Nat := 118140960795 + 6587888 * 2 ^ 59
def prefixEnd_6587888 : Nat := 4983230072969 + 3 ^ 40 * 6587888 * 2
def baseEnd_6587888 : Nat := 3382753041987026091602861

theorem tailTrace_6587888 : CollatzResearch.WordTrace tailWord_6587888 prefixEnd_6587888 3382753041987026091602861 := by
  unfold tailWord_6587888
  simp only [CollatzResearch.WordTrace]
  refine ⟨120140007578607186269998159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160186676771476248359997545 120140007578607186269998159)
  ·
    refine ⟨180210011367910779404997239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120140007578607186269998159 180210011367910779404997239)
    ·
      refine ⟨270315017051866169107495859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180210011367910779404997239 270315017051866169107495859)
      ·
        refine ⟨405472525577799253661243789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270315017051866169107495859 405472525577799253661243789)
        ·
          refine ⟨152052197091674720122966421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405472525577799253661243789 152052197091674720122966421)
          ·
            refine ⟨7127446738672252505764051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152052197091674720122966421 7127446738672252505764051)
            ·
              refine ⟨10691170108008378758646077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127446738672252505764051 10691170108008378758646077)
              ·
                refine ⟨4009188790503142034492279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10691170108008378758646077 4009188790503142034492279)
                ·
                  refine ⟨6013783185754713051738419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009188790503142034492279 6013783185754713051738419)
                  ·
                    refine ⟨9020674778632069577607629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6013783185754713051738419 9020674778632069577607629)
                    ·
                      refine ⟨3382753041987026091602861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9020674778632069577607629 3382753041987026091602861)
                      ·
                        rfl

theorem cell23_6587888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 1, 3].length) (baseStart_6587888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587888 prefixEnd_6587888 := by exact prefixLift 6587888
  have htrace : WordTrace (prefixWord ++ tailWord_6587888) baseStart_6587888 baseEnd_6587888 := by
    simpa [prefixWord, tailWord_6587888, baseEnd_6587888] using wordTrace_append hprefix tailTrace_6587888
  have hstable : (prefixWord ++ tailWord_6587888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587888).length < 2 ^ (prefixWord ++ tailWord_6587888).sum := by decide
  have hdescent : baseEnd_6587888 < baseStart_6587888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587897 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 3]
def baseStart_6587897 : Nat := 118140960795 + 6587897 * 2 ^ 59
def prefixEnd_6587897 : Nat := 4983230072969 + 3 ^ 40 * 6587897 * 2
def baseEnd_6587897 : Nat := 3382757663312916556390319

theorem tailTrace_6587897 : CollatzResearch.WordTrace tailWord_6587897 prefixEnd_6587897 3382757663312916556390319 := by
  unfold tailWord_6587897
  simp only [CollatzResearch.WordTrace]
  refine ⟨240280343414181767077073945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160186895609454511384715963 240280343414181767077073945)
  ·
    refine ⟨180210257560636325307805459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240280343414181767077073945 180210257560636325307805459)
    ·
      refine ⟨270315386340954487961708189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180210257560636325307805459 270315386340954487961708189)
      ·
        refine ⟨101368269877857932985640571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270315386340954487961708189 101368269877857932985640571)
        ·
          refine ⟨152052404816786899478460857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101368269877857932985640571 152052404816786899478460857)
          ·
            refine ⟨114039303612590174608845643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152052404816786899478460857 114039303612590174608845643)
            ·
              refine ⟨171058955418885261913268465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114039303612590174608845643 171058955418885261913268465)
              ·
                refine ⟨128294216564163946434951349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171058955418885261913268465 128294216564163946434951349)
                ·
                  refine ⟨12027582802890369978276689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128294216564163946434951349 12027582802890369978276689)
                  ·
                    refine ⟨9020687102167777483707517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12027582802890369978276689 9020687102167777483707517)
                    ·
                      refine ⟨3382757663312916556390319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9020687102167777483707517 3382757663312916556390319)
                      ·
                        rfl

theorem cell23_6587897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_6587897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587897 prefixEnd_6587897 := by exact prefixLift 6587897
  have htrace : WordTrace (prefixWord ++ tailWord_6587897) baseStart_6587897 baseEnd_6587897 := by
    simpa [prefixWord, tailWord_6587897, baseEnd_6587897] using wordTrace_append hprefix tailTrace_6587897
  have hstable : (prefixWord ++ tailWord_6587897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587897).length < 2 ^ (prefixWord ++ tailWord_6587897).sum := by decide
  have hdescent : baseEnd_6587897 < baseStart_6587897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587900 : List Nat := [2, 2, 2, 1, 2, 1, 13]
def baseStart_6587900 : Nat := 118140960795 + 6587900 * 2 ^ 59
def prefixEnd_6587900 : Nat := 4983230072969 + 3 ^ 40 * 6587900 * 2
def baseEnd_6587900 : Nat := 41762459305615803020405

theorem tailTrace_6587900 : CollatzResearch.WordTrace tailWord_6587900 prefixEnd_6587900 41762459305615803020405 := by
  unfold tailWord_6587900
  simp only [CollatzResearch.WordTrace]
  refine ⟨120140226416585449294716577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160186968555447265726288769 120140226416585449294716577)
  ·
    refine ⟨90105169812439086971037433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120140226416585449294716577 90105169812439086971037433)
    ·
      refine ⟨67578877359329315228278075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90105169812439086971037433 67578877359329315228278075)
      ·
        refine ⟨101368316038993972842417113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67578877359329315228278075 101368316038993972842417113)
        ·
          refine ⟨76026237029245479631812835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101368316038993972842417113 76026237029245479631812835)
          ·
            refine ⟨114039355543868219447719253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76026237029245479631812835 114039355543868219447719253)
            ·
              refine ⟨41762459305615803020405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 114039355543868219447719253 41762459305615803020405)
              ·
                rfl

theorem cell23_6587900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 13].length) (baseStart_6587900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587900 prefixEnd_6587900 := by exact prefixLift 6587900
  have htrace : WordTrace (prefixWord ++ tailWord_6587900) baseStart_6587900 baseEnd_6587900 := by
    simpa [prefixWord, tailWord_6587900, baseEnd_6587900] using wordTrace_append hprefix tailTrace_6587900
  have hstable : (prefixWord ++ tailWord_6587900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587900).length < 2 ^ (prefixWord ++ tailWord_6587900).sum := by decide
  have hdescent : baseEnd_6587900 < baseStart_6587900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587905 : List Nat := [1, 2, 4, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_6587905 : Nat := 118140960795 + 6587905 * 2 ^ 59
def prefixEnd_6587905 : Nat := 4983230072969 + 3 ^ 40 * 6587905 * 2
def baseEnd_6587905 : Nat := 3382761771158152525090283

theorem tailTrace_6587905 : CollatzResearch.WordTrace tailWord_6587905 prefixEnd_6587905 3382761771158152525090283 := by
  unfold tailWord_6587905
  simp only [CollatzResearch.WordTrace]
  refine ⟨240280635198152784443365169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160187090132101856295576779 240280635198152784443365169)
  ·
    refine ⟨180210476398614588332523877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240280635198152784443365169 180210476398614588332523877)
    ·
      refine ⟨33789464324740235312348227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180210476398614588332523877 33789464324740235312348227)
      ·
        refine ⟨50684196487110352968522341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33789464324740235312348227 50684196487110352968522341)
        ·
          refine ⟨9503286841333191181597939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50684196487110352968522341 9503286841333191181597939)
          ·
            refine ⟨14254930261999786772396909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503286841333191181597939 14254930261999786772396909)
            ·
              refine ⟨5345598848249920039648841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14254930261999786772396909 5345598848249920039648841)
              ·
                refine ⟨4009199136187440029736631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5345598848249920039648841 4009199136187440029736631)
                ·
                  refine ⟨6013798704281160044604947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009199136187440029736631 6013798704281160044604947)
                  ·
                    refine ⟨9020698056421740066907421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6013798704281160044604947 9020698056421740066907421)
                    ·
                      refine ⟨3382761771158152525090283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9020698056421740066907421 3382761771158152525090283)
                      ·
                        rfl

theorem cell23_6587905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_6587905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587905 prefixEnd_6587905 := by exact prefixLift 6587905
  have htrace : WordTrace (prefixWord ++ tailWord_6587905) baseStart_6587905 baseEnd_6587905 := by
    simpa [prefixWord, tailWord_6587905, baseEnd_6587905] using wordTrace_append hprefix tailTrace_6587905
  have hstable : (prefixWord ++ tailWord_6587905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587905).length < 2 ^ (prefixWord ++ tailWord_6587905).sum := by decide
  have hdescent : baseEnd_6587905 < baseStart_6587905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587928 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 1, 1, 4]
def baseStart_6587928 : Nat := 118140960795 + 6587928 * 2 ^ 59
def prefixEnd_6587928 : Nat := 4983230072969 + 3 ^ 40 * 6587928 * 2
def baseEnd_6587928 : Nat := 3382773581213205935102677

theorem tailTrace_6587928 : CollatzResearch.WordTrace tailWord_6587928 prefixEnd_6587928 3382773581213205935102677 := by
  unfold tailWord_6587928
  simp only [CollatzResearch.WordTrace]
  refine ⟨120140737038534729685726219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160187649384712972914301625 120140737038534729685726219)
  ·
    refine ⟨180211105557802094528589329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120140737038534729685726219 180211105557802094528589329)
    ·
      refine ⟨135158329168351570896441997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180211105557802094528589329 135158329168351570896441997)
      ·
        refine ⟨50684373438131839086165749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135158329168351570896441997 50684373438131839086165749)
        ·
          refine ⟨4751660009824859914328039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50684373438131839086165749 4751660009824859914328039)
          ·
            refine ⟨7127490014737289871492059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4751660009824859914328039 7127490014737289871492059)
            ·
              refine ⟨10691235022105934807238089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127490014737289871492059 10691235022105934807238089)
              ·
                refine ⟨8018426266579451105428567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10691235022105934807238089 8018426266579451105428567)
                ·
                  refine ⟨12027639399869176658142851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8018426266579451105428567 12027639399869176658142851)
                  ·
                    refine ⟨18041459099803764987214277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12027639399869176658142851 18041459099803764987214277)
                    ·
                      refine ⟨3382773581213205935102677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18041459099803764987214277 3382773581213205935102677)
                      ·
                        rfl

theorem cell23_6587928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_6587928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587928 prefixEnd_6587928 := by exact prefixLift 6587928
  have htrace : WordTrace (prefixWord ++ tailWord_6587928) baseStart_6587928 baseEnd_6587928 := by
    simpa [prefixWord, tailWord_6587928, baseEnd_6587928] using wordTrace_append hprefix tailTrace_6587928
  have hstable : (prefixWord ++ tailWord_6587928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587928).length < 2 ^ (prefixWord ++ tailWord_6587928).sum := by decide
  have hdescent : baseEnd_6587928 < baseStart_6587928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587961 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 3]
def baseStart_6587961 : Nat := 118140960795 + 6587961 * 2 ^ 59
def prefixEnd_6587961 : Nat := 4983230072969 + 3 ^ 40 * 6587961 * 2
def baseEnd_6587961 : Nat := 3382790526074804305990025

theorem tailTrace_6587961 : CollatzResearch.WordTrace tailWord_6587961 prefixEnd_6587961 3382790526074804305990025 := by
  unfold tailWord_6587961
  simp only [CollatzResearch.WordTrace]
  refine ⟨240282677685949906007403737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160188451790633270671602491 240282677685949906007403737)
  ·
    refine ⟨180212008264462429505552803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240282677685949906007403737 180212008264462429505552803)
    ·
      refine ⟨270318012396693644258329205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180212008264462429505552803 270318012396693644258329205)
      ·
        refine ⟨25342313662190029149218363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270318012396693644258329205 25342313662190029149218363)
        ·
          refine ⟨38013470493285043723827545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25342313662190029149218363 38013470493285043723827545)
          ·
            refine ⟨28510102869963782792870659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38013470493285043723827545 28510102869963782792870659)
            ·
              refine ⟨42765154304945674189305989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28510102869963782792870659 42765154304945674189305989)
              ·
                refine ⟨8018466432177313910494873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42765154304945674189305989 8018466432177313910494873)
                ·
                  refine ⟨6013849824132985432871155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8018466432177313910494873 6013849824132985432871155)
                  ·
                    refine ⟨9020774736199478149306733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6013849824132985432871155 9020774736199478149306733)
                    ·
                      refine ⟨3382790526074804305990025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9020774736199478149306733 3382790526074804305990025)
                      ·
                        rfl

theorem cell23_6587961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_6587961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587961 prefixEnd_6587961 := by exact prefixLift 6587961
  have htrace : WordTrace (prefixWord ++ tailWord_6587961) baseStart_6587961 baseEnd_6587961 := by
    simpa [prefixWord, tailWord_6587961, baseEnd_6587961] using wordTrace_append hprefix tailTrace_6587961
  have hstable : (prefixWord ++ tailWord_6587961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587961).length < 2 ^ (prefixWord ++ tailWord_6587961).sum := by decide
  have hdescent : baseEnd_6587961 < baseStart_6587961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6587967 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_6587967 : Nat := 118140960795 + 6587967 * 2 ^ 59
def prefixEnd_6587967 : Nat := 4983230072969 + 3 ^ 40 * 6587967 * 2
def baseEnd_6587967 : Nat := 3382793606958731282514997

theorem tailTrace_6587967 : CollatzResearch.WordTrace tailWord_6587967 prefixEnd_6587967 3382793606958731282514997 := by
  unfold tailWord_6587967
  simp only [CollatzResearch.WordTrace]
  refine ⟨240282896523928169032122155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160188597682618779354748103 240282896523928169032122155)
  ·
    refine ⟨360424344785892253548183233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240282896523928169032122155 360424344785892253548183233)
    ·
      refine ⟨270318258589419190161137425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360424344785892253548183233 270318258589419190161137425)
      ·
        refine ⟨202738693942064392620853069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270318258589419190161137425 202738693942064392620853069)
        ·
          refine ⟨76027010228274147232819901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202738693942064392620853069 76027010228274147232819901)
          ·
            refine ⟨28510128835602805212307463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76027010228274147232819901 28510128835602805212307463)
            ·
              refine ⟨42765193253404207818461195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28510128835602805212307463 42765193253404207818461195)
              ·
                refine ⟨64147789880106311727691793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42765193253404207818461195 64147789880106311727691793)
                ·
                  refine ⟨48110842410079733795768845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64147789880106311727691793 48110842410079733795768845)
                  ·
                    refine ⟨18041565903779900173413317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48110842410079733795768845 18041565903779900173413317)
                    ·
                      refine ⟨3382793606958731282514997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18041565903779900173413317 3382793606958731282514997)
                      ·
                        rfl

theorem cell23_6587967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_6587967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6587967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6587967 prefixEnd_6587967 := by exact prefixLift 6587967
  have htrace : WordTrace (prefixWord ++ tailWord_6587967) baseStart_6587967 baseEnd_6587967 := by
    simpa [prefixWord, tailWord_6587967, baseEnd_6587967] using wordTrace_append hprefix tailTrace_6587967
  have hstable : (prefixWord ++ tailWord_6587967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6587967).length < 2 ^ (prefixWord ++ tailWord_6587967).sum := by decide
  have hdescent : baseEnd_6587967 < baseStart_6587967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6587967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588001 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_6588001 : Nat := 118140960795 + 6588001 * 2 ^ 59
def prefixEnd_6588001 : Nat := 4983230072969 + 3 ^ 40 * 6588001 * 2
def baseEnd_6588001 : Nat := 3382811065300984149489841

theorem tailTrace_6588001 : CollatzResearch.WordTrace tailWord_6588001 prefixEnd_6588001 3382811065300984149489841 := by
  unfold tailWord_6588001
  simp only [CollatzResearch.WordTrace]
  refine ⟨240284136605804992838859857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160189424403869995225906571 240284136605804992838859857)
  ·
    refine ⟨180213102454353744629144893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240284136605804992838859857 180213102454353744629144893)
    ·
      refine ⟨67579913420382654235929335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180213102454353744629144893 67579913420382654235929335)
      ·
        refine ⟨101369870130573981353894003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67579913420382654235929335 101369870130573981353894003)
        ·
          refine ⟨152054805195860972030841005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101369870130573981353894003 152054805195860972030841005)
          ·
            refine ⟨57020551948447864511565377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152054805195860972030841005 57020551948447864511565377)
            ·
              refine ⟨42765413961335898383674033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57020551948447864511565377 42765413961335898383674033)
              ·
                refine ⟨32074060471001923787755525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42765413961335898383674033 32074060471001923787755525)
                ·
                  refine ⟨6013886338312860710204161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32074060471001923787755525 6013886338312860710204161)
                  ·
                    refine ⟨4510414753734645532653121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6013886338312860710204161 4510414753734645532653121)
                    ·
                      refine ⟨3382811065300984149489841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510414753734645532653121 3382811065300984149489841)
                      ·
                        rfl

theorem cell23_6588001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_6588001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588001 prefixEnd_6588001 := by exact prefixLift 6588001
  have htrace : WordTrace (prefixWord ++ tailWord_6588001) baseStart_6588001 baseEnd_6588001 := by
    simpa [prefixWord, tailWord_6588001, baseEnd_6588001] using wordTrace_append hprefix tailTrace_6588001
  have hstable : (prefixWord ++ tailWord_6588001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588001).length < 2 ^ (prefixWord ++ tailWord_6588001).sum := by decide
  have hdescent : baseEnd_6588001 < baseStart_6588001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588005 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 1, 3, 2]
def baseStart_6588005 : Nat := 118140960795 + 6588005 * 2 ^ 59
def prefixEnd_6588005 : Nat := 4983230072969 + 3 ^ 40 * 6588005 * 2
def baseEnd_6588005 : Nat := 3382813119223602133839823

theorem tailTrace_6588005 : CollatzResearch.WordTrace tailWord_6588005 prefixEnd_6588005 3382813119223602133839823 := by
  unfold tailWord_6588005
  simp only [CollatzResearch.WordTrace]
  refine ⟨240284282497790501522005469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160189521665193667681336979 240284282497790501522005469)
  ·
    refine ⟨90106605936671438070752051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240284282497790501522005469 90106605936671438070752051)
    ·
      refine ⟨135159908905007157106128077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90106605936671438070752051 135159908905007157106128077)
      ·
        refine ⟨50684965839377683914798029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135159908905007157106128077 50684965839377683914798029)
        ·
          refine ⟨19006862189766631468049261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50684965839377683914798029 19006862189766631468049261)
          ·
            refine ⟨7127573321162486800518473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19006862189766631468049261 7127573321162486800518473)
            ·
              refine ⟨5345679990871865100388855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7127573321162486800518473 5345679990871865100388855)
              ·
                refine ⟨8018519986307797650583283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5345679990871865100388855 8018519986307797650583283)
                ·
                  refine ⟨12027779979461696475874925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8018519986307797650583283 12027779979461696475874925)
                  ·
                    refine ⟨4510417492298136178453097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12027779979461696475874925 4510417492298136178453097)
                    ·
                      refine ⟨3382813119223602133839823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510417492298136178453097 3382813119223602133839823)
                      ·
                        rfl

theorem cell23_6588005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_6588005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588005 prefixEnd_6588005 := by exact prefixLift 6588005
  have htrace : WordTrace (prefixWord ++ tailWord_6588005) baseStart_6588005 baseEnd_6588005 := by
    simpa [prefixWord, tailWord_6588005, baseEnd_6588005] using wordTrace_append hprefix tailTrace_6588005
  have hstable : (prefixWord ++ tailWord_6588005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588005).length < 2 ^ (prefixWord ++ tailWord_6588005).sum := by decide
  have hdescent : baseEnd_6588005 < baseStart_6588005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588018 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_6588018 : Nat := 118140960795 + 6588018 * 2 ^ 59
def prefixEnd_6588018 : Nat := 4983230072969 + 3 ^ 40 * 6588018 * 2
def baseEnd_6588018 : Nat := 3382819794472110582977263

theorem tailTrace_6588018 : CollatzResearch.WordTrace tailWord_6588018 prefixEnd_6588018 3382819794472110582977263 := by
  unfold tailWord_6588018
  simp only [CollatzResearch.WordTrace]
  refine ⟨60071189161685851185557177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160189837764495603161485805 60071189161685851185557177)
  ·
    refine ⟨45053391871264388389167883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60071189161685851185557177 45053391871264388389167883)
    ·
      refine ⟨67580087806896582583751825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45053391871264388389167883 67580087806896582583751825)
      ·
        refine ⟨50685065855172436937813869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67580087806896582583751825 50685065855172436937813869)
        ·
          refine ⟨19006899695689663851680201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50685065855172436937813869 19006899695689663851680201)
          ·
            refine ⟨14255174771767247888760151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19006899695689663851680201 14255174771767247888760151)
            ·
              refine ⟨21382762157650871833140227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14255174771767247888760151 21382762157650871833140227)
              ·
                refine ⟨32074143236476307749710341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21382762157650871833140227 32074143236476307749710341)
                ·
                  refine ⟨6013901856839307703070689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32074143236476307749710341 6013901856839307703070689)
                  ·
                    refine ⟨4510426392629480777303017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6013901856839307703070689 4510426392629480777303017)
                    ·
                      refine ⟨3382819794472110582977263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510426392629480777303017 3382819794472110582977263)
                      ·
                        rfl

theorem cell23_6588018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_6588018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588018 prefixEnd_6588018 := by exact prefixLift 6588018
  have htrace : WordTrace (prefixWord ++ tailWord_6588018) baseStart_6588018 baseEnd_6588018 := by
    simpa [prefixWord, tailWord_6588018, baseEnd_6588018] using wordTrace_append hprefix tailTrace_6588018
  have hstable : (prefixWord ++ tailWord_6588018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588018).length < 2 ^ (prefixWord ++ tailWord_6588018).sum := by decide
  have hdescent : baseEnd_6588018 < baseStart_6588018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588037 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_6588037 : Nat := 118140960795 + 6588037 * 2 ^ 59
def prefixEnd_6588037 : Nat := 4983230072969 + 3 ^ 40 * 6588037 * 2
def baseEnd_6588037 : Nat := 1127609850201515336213225

theorem tailTrace_6588037 : CollatzResearch.WordTrace tailWord_6588037 prefixEnd_6588037 1127609850201515336213225 := by
  unfold tailWord_6588037
  simp only [CollatzResearch.WordTrace]
  refine ⟨240285449633674570987170365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160190299755783047324780243 240285449633674570987170365)
  ·
    refine ⟨90107043612627964120188887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240285449633674570987170365 90107043612627964120188887)
    ·
      refine ⟨135160565418941946180283331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90107043612627964120188887 135160565418941946180283331)
      ·
        refine ⟨202740848128412919270424997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135160565418941946180283331 202740848128412919270424997)
        ·
          refine ⟨38013909024077422363204687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202740848128412919270424997 38013909024077422363204687)
          ·
            refine ⟨57020863536116133544807031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38013909024077422363204687 57020863536116133544807031)
            ·
              refine ⟨85531295304174200317210547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57020863536116133544807031 85531295304174200317210547)
              ·
                refine ⟨128296942956261300475815821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85531295304174200317210547 128296942956261300475815821)
                ·
                  refine ⟨48111353608597987678430933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128296942956261300475815821 48111353608597987678430933)
                  ·
                    refine ⟨1127609850201515336213225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48111353608597987678430933 1127609850201515336213225)
                    ·
                      rfl

theorem cell23_6588037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_6588037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588037 prefixEnd_6588037 := by exact prefixLift 6588037
  have htrace : WordTrace (prefixWord ++ tailWord_6588037) baseStart_6588037 baseEnd_6588037 := by
    simpa [prefixWord, tailWord_6588037, baseEnd_6588037] using wordTrace_append hprefix tailTrace_6588037
  have hstable : (prefixWord ++ tailWord_6588037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588037).length < 2 ^ (prefixWord ++ tailWord_6588037).sum := by decide
  have hdescent : baseEnd_6588037 < baseStart_6588037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588108 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6588108 : Nat := 118140960795 + 6588108 * 2 ^ 59
def prefixEnd_6588108 : Nat := 4983230072969 + 3 ^ 40 * 6588108 * 2
def baseEnd_6588108 : Nat := 3382866007731015230851849

theorem tailTrace_6588108 : CollatzResearch.WordTrace tailWord_6588108 prefixEnd_6588108 3382866007731015230851849 := by
  unfold tailWord_6588108
  simp only [CollatzResearch.WordTrace]
  refine ⟨120144019608208675056502489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160192026144278233408669985 120144019608208675056502489)
  ·
    refine ⟨90108014706156506292376867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120144019608208675056502489 90108014706156506292376867)
    ·
      refine ⟨135162022059234759438565301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90108014706156506292376867 135162022059234759438565301)
      ·
        refine ⟨12671439568053258697365497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135162022059234759438565301 12671439568053258697365497)
        ·
          refine ⟨9503579676039944023024123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12671439568053258697365497 9503579676039944023024123)
          ·
            refine ⟨14255369514059916034536185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503579676039944023024123 14255369514059916034536185)
            ·
              refine ⟨10691527135544937025902139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14255369514059916034536185 10691527135544937025902139)
              ·
                refine ⟨16037290703317405538853209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10691527135544937025902139 16037290703317405538853209)
                ·
                  refine ⟨12027968027488054154139907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16037290703317405538853209 12027968027488054154139907)
                  ·
                    refine ⟨18041952041232081231209861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12027968027488054154139907 18041952041232081231209861)
                    ·
                      refine ⟨3382866007731015230851849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18041952041232081231209861 3382866007731015230851849)
                      ·
                        rfl

theorem cell23_6588108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6588108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588108 prefixEnd_6588108 := by exact prefixLift 6588108
  have htrace : WordTrace (prefixWord ++ tailWord_6588108) baseStart_6588108 baseEnd_6588108 := by
    simpa [prefixWord, tailWord_6588108, baseEnd_6588108] using wordTrace_append hprefix tailTrace_6588108
  have hstable : (prefixWord ++ tailWord_6588108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588108).length < 2 ^ (prefixWord ++ tailWord_6588108).sum := by decide
  have hdescent : baseEnd_6588108 < baseStart_6588108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588151 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 4, 3, 2]
def baseStart_6588151 : Nat := 118140960795 + 6588151 * 2 ^ 59
def prefixEnd_6588151 : Nat := 4983230072969 + 3 ^ 40 * 6588151 * 2
def baseEnd_6588151 : Nat := 3382888087399158562614151

theorem tailTrace_6588151 : CollatzResearch.WordTrace tailWord_6588151 prefixEnd_6588151 3382888087399158562614151 := by
  unfold tailWord_6588151
  simp only [CollatzResearch.WordTrace]
  refine ⟨240289607555261568456820307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160193071703507712304546871 240289607555261568456820307)
  ·
    refine ⟨360434411332892352685230461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240289607555261568456820307 360434411332892352685230461)
    ·
      refine ⟨135162904249834632256961423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360434411332892352685230461 135162904249834632256961423)
      ·
        refine ⟨202744356374751948385442135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135162904249834632256961423 202744356374751948385442135)
        ·
          refine ⟨304116534562127922578163203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202744356374751948385442135 304116534562127922578163203)
          ·
            refine ⟨456174801843191883867244805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304116534562127922578163203 456174801843191883867244805)
            ·
              refine ⟨85532775345598478225108401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 456174801843191883867244805 85532775345598478225108401)
              ·
                refine ⟨64149581509198858668831301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85532775345598478225108401 64149581509198858668831301)
                ·
                  refine ⟨12028046532974786000405869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64149581509198858668831301 12028046532974786000405869)
                  ·
                    refine ⟨4510517449865544750152201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12028046532974786000405869 4510517449865544750152201)
                    ·
                      refine ⟨3382888087399158562614151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510517449865544750152201 3382888087399158562614151)
                      ·
                        rfl

theorem cell23_6588151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_6588151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588151 prefixEnd_6588151 := by exact prefixLift 6588151
  have htrace : WordTrace (prefixWord ++ tailWord_6588151) baseStart_6588151 baseEnd_6588151 := by
    simpa [prefixWord, tailWord_6588151, baseEnd_6588151] using wordTrace_append hprefix tailTrace_6588151
  have hstable : (prefixWord ++ tailWord_6588151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588151).length < 2 ^ (prefixWord ++ tailWord_6588151).sum := by decide
  have hdescent : baseEnd_6588151 < baseStart_6588151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588191 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 4, 4]
def baseStart_6588191 : Nat := 118140960795 + 6588191 * 2 ^ 59
def prefixEnd_6588191 : Nat := 4983230072969 + 3 ^ 40 * 6588191 * 2
def baseEnd_6588191 : Nat := 1127636208875112802037989

theorem tailTrace_6588191 : CollatzResearch.WordTrace tailWord_6588191 prefixEnd_6588191 1127636208875112802037989 := by
  unfold tailWord_6588191
  simp only [CollatzResearch.WordTrace]
  refine ⟨240291066475116655288276427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160194044316744436858850951 240291066475116655288276427)
  ·
    refine ⟨360436599712674982932414641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240291066475116655288276427 360436599712674982932414641)
    ·
      refine ⟨270327449784506237199310981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360436599712674982932414641 270327449784506237199310981)
      ·
        refine ⟨50686396834594919474870809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270327449784506237199310981 50686396834594919474870809)
        ·
          refine ⟨38014797625946189606153107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50686396834594919474870809 38014797625946189606153107)
          ·
            refine ⟨57022196438919284409229661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38014797625946189606153107 57022196438919284409229661)
            ·
              refine ⟨21383323664594731653461123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57022196438919284409229661 21383323664594731653461123)
              ·
                refine ⟨32074985496892097480191685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21383323664594731653461123 32074985496892097480191685)
                ·
                  refine ⟨6014059780667268277535941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32074985496892097480191685 6014059780667268277535941)
                  ·
                    refine ⟨1127636208875112802037989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6014059780667268277535941 1127636208875112802037989)
                    ·
                      rfl

theorem cell23_6588191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 4].length) (baseStart_6588191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588191 prefixEnd_6588191 := by exact prefixLift 6588191
  have htrace : WordTrace (prefixWord ++ tailWord_6588191) baseStart_6588191 baseEnd_6588191 := by
    simpa [prefixWord, tailWord_6588191, baseEnd_6588191] using wordTrace_append hprefix tailTrace_6588191
  have hstable : (prefixWord ++ tailWord_6588191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588191).length < 2 ^ (prefixWord ++ tailWord_6588191).sum := by decide
  have hdescent : baseEnd_6588191 < baseStart_6588191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588211 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 6]
def baseStart_6588211 : Nat := 118140960795 + 6588211 * 2 ^ 59
def prefixEnd_6588211 : Nat := 4983230072969 + 3 ^ 40 * 6588211 * 2
def baseEnd_6588211 : Nat := 3382918896238428327863875

theorem tailTrace_6588211 : CollatzResearch.WordTrace tailWord_6588211 prefixEnd_6588211 3382918896238428327863875 := by
  unfold tailWord_6588211
  simp only [CollatzResearch.WordTrace]
  refine ⟨240291795935044198704004487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160194530623362799136002991 240291795935044198704004487)
  ·
    refine ⟨360437693902566298056006731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240291795935044198704004487 360437693902566298056006731)
    ·
      refine ⟨540656540853849447084010097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360437693902566298056006731 540656540853849447084010097)
      ·
        refine ⟨405492405640387085313007573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540656540853849447084010097 405492405640387085313007573)
        ·
          refine ⟨9503728257196572312023615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 405492405640387085313007573 9503728257196572312023615)
          ·
            refine ⟨14255592385794858468035423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503728257196572312023615 14255592385794858468035423)
            ·
              refine ⟨21383388578692287702053135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14255592385794858468035423 21383388578692287702053135)
              ·
                refine ⟨32075082868038431553079703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21383388578692287702053135 32075082868038431553079703)
                ·
                  refine ⟨48112624302057647329619555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32075082868038431553079703 48112624302057647329619555)
                  ·
                    refine ⟨72168936453086470994429333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48112624302057647329619555 72168936453086470994429333)
                    ·
                      refine ⟨3382918896238428327863875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72168936453086470994429333 3382918896238428327863875)
                      ·
                        rfl

theorem cell23_6588211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_6588211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588211 prefixEnd_6588211 := by exact prefixLift 6588211
  have htrace : WordTrace (prefixWord ++ tailWord_6588211) baseStart_6588211 baseEnd_6588211 := by
    simpa [prefixWord, tailWord_6588211, baseEnd_6588211] using wordTrace_append hprefix tailTrace_6588211
  have hstable : (prefixWord ++ tailWord_6588211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588211).length < 2 ^ (prefixWord ++ tailWord_6588211).sum := by decide
  have hdescent : baseEnd_6588211 < baseStart_6588211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588218 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_6588218 : Nat := 118140960795 + 6588218 * 2 ^ 59
def prefixEnd_6588218 : Nat := 4983230072969 + 3 ^ 40 * 6588218 * 2
def baseEnd_6588218 : Nat := 3382922490603009800476343

theorem tailTrace_6588218 : CollatzResearch.WordTrace tailWord_6588218 prefixEnd_6588218 3382922490603009800476343 := by
  unfold tailWord_6588218
  simp only [CollatzResearch.WordTrace]
  refine ⟨60073012811504709724877327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160194700830679225933006205 60073012811504709724877327)
  ·
    refine ⟨90109519217257064587315991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60073012811504709724877327 90109519217257064587315991)
    ·
      refine ⟨135164278825885596880973987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90109519217257064587315991 135164278825885596880973987)
      ·
        refine ⟨202746418238828395321460981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135164278825885596880973987 202746418238828395321460981)
        ·
          refine ⟨19007476709890162061386967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202746418238828395321460981 19007476709890162061386967)
          ·
            refine ⟨28511215064835243092080451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19007476709890162061386967 28511215064835243092080451)
            ·
              refine ⟨42766822597252864638120677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28511215064835243092080451 42766822597252864638120677)
              ·
                refine ⟨8018779236984912119647627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42766822597252864638120677 8018779236984912119647627)
                ·
                  refine ⟨12028168855477368179471441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8018779236984912119647627 12028168855477368179471441)
                  ·
                    refine ⟨9021126641608026134603581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12028168855477368179471441 9021126641608026134603581)
                    ·
                      refine ⟨3382922490603009800476343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9021126641608026134603581 3382922490603009800476343)
                      ·
                        rfl

theorem cell23_6588218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_6588218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588218 prefixEnd_6588218 := by exact prefixLift 6588218
  have htrace : WordTrace (prefixWord ++ tailWord_6588218) baseStart_6588218 baseEnd_6588218 := by
    simpa [prefixWord, tailWord_6588218, baseEnd_6588218] using wordTrace_append hprefix tailTrace_6588218
  have hstable : (prefixWord ++ tailWord_6588218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588218).length < 2 ^ (prefixWord ++ tailWord_6588218).sum := by decide
  have hdescent : baseEnd_6588218 < baseStart_6588218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588221 : List Nat := [1, 4, 1, 4, 1, 2, 1, 9]
def baseStart_6588221 : Nat := 118140960795 + 6588221 * 2 ^ 59
def prefixEnd_6588221 : Nat := 4983230072969 + 3 ^ 40 * 6588221 * 2
def baseEnd_6588221 : Nat := 125293482631295306990327

theorem tailTrace_6588221 : CollatzResearch.WordTrace tailWord_6588221 prefixEnd_6588221 125293482631295306990327 := by
  unfold tailWord_6588221
  simp only [CollatzResearch.WordTrace]
  refine ⟨240292160665007970411868517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160194773776671980274579011 240292160665007970411868517)
  ·
    refine ⟨45054780124688994452225347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240292160665007970411868517 45054780124688994452225347)
    ·
      refine ⟨67582170187033491678338021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45054780124688994452225347 67582170187033491678338021)
      ·
        refine ⟨12671656910068779689688379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67582170187033491678338021 12671656910068779689688379)
        ·
          refine ⟨19007485365103169534532569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12671656910068779689688379 19007485365103169534532569)
          ·
            refine ⟨14255614023827377150899427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19007485365103169534532569 14255614023827377150899427)
            ·
              refine ⟨21383421035741065726349141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14255614023827377150899427 21383421035741065726349141)
              ·
                refine ⟨125293482631295306990327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21383421035741065726349141 125293482631295306990327)
                ·
                  rfl

theorem cell23_6588221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 9].length) (baseStart_6588221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588221 prefixEnd_6588221 := by exact prefixLift 6588221
  have htrace : WordTrace (prefixWord ++ tailWord_6588221) baseStart_6588221 baseEnd_6588221 := by
    simpa [prefixWord, tailWord_6588221, baseEnd_6588221] using wordTrace_append hprefix tailTrace_6588221
  have hstable : (prefixWord ++ tailWord_6588221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588221).length < 2 ^ (prefixWord ++ tailWord_6588221).sum := by decide
  have hdescent : baseEnd_6588221 < baseStart_6588221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588231 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_6588231 : Nat := 118140960795 + 6588231 * 2 ^ 59
def prefixEnd_6588231 : Nat := 4983230072969 + 3 ^ 40 * 6588231 * 2
def baseEnd_6588231 : Nat := 3382929165851518249613783

theorem tailTrace_6588231 : CollatzResearch.WordTrace tailWord_6588231 prefixEnd_6588231 3382929165851518249613783 := by
  unfold tailWord_6588231
  simp only [CollatzResearch.WordTrace]
  refine ⟨240292525394971742119732547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160195016929981161413155031 240292525394971742119732547)
  ·
    refine ⟨360438788092457613179598821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240292525394971742119732547 360438788092457613179598821)
    ·
      refine ⟨67582272767335802471174779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360438788092457613179598821 67582272767335802471174779)
      ·
        refine ⟨101373409151003703706762169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67582272767335802471174779 101373409151003703706762169)
        ·
          refine ⟨76030056863252777780071627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101373409151003703706762169 76030056863252777780071627)
          ·
            refine ⟨114045085294879166670107441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76030056863252777780071627 114045085294879166670107441)
            ·
              refine ⟨85533813971159375002580581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114045085294879166670107441 85533813971159375002580581)
              ·
                refine ⟨16037590119592382812983859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85533813971159375002580581 16037590119592382812983859)
                ·
                  refine ⟨24056385179388574219475789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16037590119592382812983859 24056385179388574219475789)
                  ·
                    refine ⟨9021144442270715332303421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24056385179388574219475789 9021144442270715332303421)
                    ·
                      refine ⟨3382929165851518249613783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9021144442270715332303421 3382929165851518249613783)
                      ·
                        rfl

theorem cell23_6588231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_6588231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588231 prefixEnd_6588231 := by exact prefixLift 6588231
  have htrace : WordTrace (prefixWord ++ tailWord_6588231) baseStart_6588231 baseEnd_6588231 := by
    simpa [prefixWord, tailWord_6588231, baseEnd_6588231] using wordTrace_append hprefix tailTrace_6588231
  have hstable : (prefixWord ++ tailWord_6588231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588231).length < 2 ^ (prefixWord ++ tailWord_6588231).sum := by decide
  have hdescent : baseEnd_6588231 < baseStart_6588231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588232 : List Nat := [2, 1, 3, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_6588232 : Nat := 118140960795 + 6588232 * 2 ^ 59
def prefixEnd_6588232 : Nat := 4983230072969 + 3 ^ 40 * 6588232 * 2
def baseEnd_6588232 : Nat := 3382929679332172745701279

theorem tailTrace_6588232 : CollatzResearch.WordTrace tailWord_6588232 prefixEnd_6588232 3382929679332172745701279 := by
  unfold tailWord_6588232
  simp only [CollatzResearch.WordTrace]
  refine ⟨120146280933984059645259475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160195041245312079527012633 120146280933984059645259475)
  ·
    refine ⟨180219421400976089467889213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120146280933984059645259475 180219421400976089467889213)
    ·
      refine ⟨67582283025366033550458455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180219421400976089467889213 67582283025366033550458455)
      ·
        refine ⟨101373424538049050325687683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67582283025366033550458455 101373424538049050325687683)
        ·
          refine ⟨152060136807073575488531525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101373424538049050325687683 152060136807073575488531525)
          ·
            refine ⟨28511275651326295404099661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152060136807073575488531525 28511275651326295404099661)
            ·
              refine ⟨10691728369247360776537373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28511275651326295404099661 10691728369247360776537373)
              ·
                refine ⟨4009398138467760291201515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10691728369247360776537373 4009398138467760291201515)
                ·
                  refine ⟨6014097207701640436802273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009398138467760291201515 6014097207701640436802273)
                  ·
                    refine ⟨4510572905776230327601705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6014097207701640436802273 4510572905776230327601705)
                    ·
                      refine ⟨3382929679332172745701279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510572905776230327601705 3382929679332172745701279)
                      ·
                        rfl

theorem cell23_6588232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_6588232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588232 prefixEnd_6588232 := by exact prefixLift 6588232
  have htrace : WordTrace (prefixWord ++ tailWord_6588232) baseStart_6588232 baseEnd_6588232 := by
    simpa [prefixWord, tailWord_6588232, baseEnd_6588232] using wordTrace_append hprefix tailTrace_6588232
  have hstable : (prefixWord ++ tailWord_6588232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588232).length < 2 ^ (prefixWord ++ tailWord_6588232).sum := by decide
  have hdescent : baseEnd_6588232 < baseStart_6588232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588288 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 1, 4, 2]
def baseStart_6588288 : Nat := 118140960795 + 6588288 * 2 ^ 59
def prefixEnd_6588288 : Nat := 4983230072969 + 3 ^ 40 * 6588288 * 2
def baseEnd_6588288 : Nat := 3382958434248824526601021

theorem tailTrace_6588288 : CollatzResearch.WordTrace tailWord_6588288 prefixEnd_6588288 3382958434248824526601021 := by
  unfold tailWord_6588288
  simp only [CollatzResearch.WordTrace]
  refine ⟨120147302177882620427278759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160196402903843493903038345 120147302177882620427278759)
  ·
    refine ⟨180220953266823930640918139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120147302177882620427278759 180220953266823930640918139)
    ·
      refine ⟨270331429900235895961377209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180220953266823930640918139 270331429900235895961377209)
      ·
        refine ⟨202748572425176921971032907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270331429900235895961377209 202748572425176921971032907)
        ·
          refine ⟨304122858637765382956549361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202748572425176921971032907 304122858637765382956549361)
          ·
            refine ⟨228092143978324037217412021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304122858637765382956549361 228092143978324037217412021)
            ·
              refine ⟨21383638497967878489132377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228092143978324037217412021 21383638497967878489132377)
              ·
                refine ⟨16037728873475908866849283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21383638497967878489132377 16037728873475908866849283)
                ·
                  refine ⟨24056593310213863300273925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16037728873475908866849283 24056593310213863300273925)
                  ·
                    refine ⟨4510611245665099368801361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24056593310213863300273925 4510611245665099368801361)
                    ·
                      refine ⟨3382958434248824526601021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510611245665099368801361 3382958434248824526601021)
                      ·
                        rfl

theorem cell23_6588288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_6588288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588288 prefixEnd_6588288 := by exact prefixLift 6588288
  have htrace : WordTrace (prefixWord ++ tailWord_6588288) baseStart_6588288 baseEnd_6588288 := by
    simpa [prefixWord, tailWord_6588288, baseEnd_6588288] using wordTrace_append hprefix tailTrace_6588288
  have hstable : (prefixWord ++ tailWord_6588288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588288).length < 2 ^ (prefixWord ++ tailWord_6588288).sum := by decide
  have hdescent : baseEnd_6588288 < baseStart_6588288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588291 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 5]
def baseStart_6588291 : Nat := 118140960795 + 6588291 * 2 ^ 59
def prefixEnd_6588291 : Nat := 4983230072969 + 3 ^ 40 * 6588291 * 2
def baseEnd_6588291 : Nat := 3382959974690788014863507

theorem tailTrace_6588291 : CollatzResearch.WordTrace tailWord_6588291 prefixEnd_6588291 3382959974690788014863507 := by
  unfold tailWord_6588291
  simp only [CollatzResearch.WordTrace]
  refine ⟨240294713774754372366916727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160196475849836248244611151 240294713774754372366916727)
  ·
    refine ⟨360442070662131558550375091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240294713774754372366916727 360442070662131558550375091)
    ·
      refine ⟨540663105993197337825562637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360442070662131558550375091 540663105993197337825562637)
      ·
        refine ⟨202748664747449001684585989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540663105993197337825562637 202748664747449001684585989)
        ·
          refine ⟨38015374640146687815859873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202748664747449001684585989 38015374640146687815859873)
          ·
            refine ⟨28511530980110015861894905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38015374640146687815859873 28511530980110015861894905)
            ·
              refine ⟨21383648235082511896421179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28511530980110015861894905 21383648235082511896421179)
              ·
                refine ⟨32075472352623767844631769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21383648235082511896421179 32075472352623767844631769)
                ·
                  refine ⟨24056604264467825883473827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32075472352623767844631769 24056604264467825883473827)
                  ·
                    refine ⟨36084906396701738825210741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24056604264467825883473827 36084906396701738825210741)
                    ·
                      refine ⟨3382959974690788014863507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36084906396701738825210741 3382959974690788014863507)
                      ·
                        rfl

theorem cell23_6588291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_6588291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588291 prefixEnd_6588291 := by exact prefixLift 6588291
  have htrace : WordTrace (prefixWord ++ tailWord_6588291) baseStart_6588291 baseEnd_6588291 := by
    simpa [prefixWord, tailWord_6588291, baseEnd_6588291] using wordTrace_append hprefix tailTrace_6588291
  have hstable : (prefixWord ++ tailWord_6588291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588291).length < 2 ^ (prefixWord ++ tailWord_6588291).sum := by decide
  have hdescent : baseEnd_6588291 < baseStart_6588291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588304 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_6588304 : Nat := 118140960795 + 6588304 * 2 ^ 59
def prefixEnd_6588304 : Nat := 4983230072969 + 3 ^ 40 * 6588304 * 2
def baseEnd_6588304 : Nat := 3382966649939296464000947

theorem tailTrace_6588304 : CollatzResearch.WordTrace tailWord_6588304 prefixEnd_6588304 3382966649939296464000947 := by
  unfold tailWord_6588304
  simp only [CollatzResearch.WordTrace]
  refine ⟨120147593961853637793569983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160196791949138183724759977 120147593961853637793569983)
  ·
    refine ⟨180221390942780456690354975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120147593961853637793569983 180221390942780456690354975)
    ·
      refine ⟨270332086414170685035532463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180221390942780456690354975 270332086414170685035532463)
      ·
        refine ⟨405498129621256027553298695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270332086414170685035532463 405498129621256027553298695)
        ·
          refine ⟨608247194431884041329948043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405498129621256027553298695 608247194431884041329948043)
          ·
            refine ⟨912370791647826061994922065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608247194431884041329948043 912370791647826061994922065)
            ·
              refine ⟨684278093735869546496191549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912370791647826061994922065 684278093735869546496191549)
              ·
                refine ⟨256604285150951079936071831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 684278093735869546496191549 256604285150951079936071831)
                ·
                  refine ⟨384906427726426619904107747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256604285150951079936071831 384906427726426619904107747)
                  ·
                    refine ⟨577359641589639929856161621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 384906427726426619904107747 577359641589639929856161621)
                    ·
                      refine ⟨3382966649939296464000947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 577359641589639929856161621 3382966649939296464000947)
                      ·
                        rfl

theorem cell23_6588304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_6588304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588304 prefixEnd_6588304 := by exact prefixLift 6588304
  have htrace : WordTrace (prefixWord ++ tailWord_6588304) baseStart_6588304 baseEnd_6588304 := by
    simpa [prefixWord, tailWord_6588304, baseEnd_6588304] using wordTrace_append hprefix tailTrace_6588304
  have hstable : (prefixWord ++ tailWord_6588304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588304).length < 2 ^ (prefixWord ++ tailWord_6588304).sum := by decide
  have hdescent : baseEnd_6588304 < baseStart_6588304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588305 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 2, 2, 2]
def baseStart_6588305 : Nat := 118140960795 + 6588305 * 2 ^ 59
def prefixEnd_6588305 : Nat := 4983230072969 + 3 ^ 40 * 6588305 * 2
def baseEnd_6588305 : Nat := 3382967163419950960088443

theorem tailTrace_6588305 : CollatzResearch.WordTrace tailWord_6588305 prefixEnd_6588305 3382967163419950960088443 := by
  unfold tailWord_6588305
  simp only [CollatzResearch.WordTrace]
  refine ⟨240295224396703652757926369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160196816264469101838617579 240295224396703652757926369)
  ·
    refine ⟨180221418297527739568444777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240295224396703652757926369 180221418297527739568444777)
    ·
      refine ⟨135166063723145804676333583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180221418297527739568444777 135166063723145804676333583)
      ·
        refine ⟨202749095584718707014500375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135166063723145804676333583 202749095584718707014500375)
        ·
          refine ⟨304123643377078060521750563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202749095584718707014500375 304123643377078060521750563)
          ·
            refine ⟨456185465065617090782625845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304123643377078060521750563 456185465065617090782625845)
            ·
              refine ⟨42767387349901602260871173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456185465065617090782625845 42767387349901602260871173)
              ·
                refine ⟨8018885128106550423913345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42767387349901602260871173 8018885128106550423913345)
                ·
                  refine ⟨6014163846079912817935009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8018885128106550423913345 6014163846079912817935009)
                  ·
                    refine ⟨4510622884559934613451257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6014163846079912817935009 4510622884559934613451257)
                    ·
                      refine ⟨3382967163419950960088443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510622884559934613451257 3382967163419950960088443)
                      ·
                        rfl

theorem cell23_6588305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_6588305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588305 prefixEnd_6588305 := by exact prefixLift 6588305
  have htrace : WordTrace (prefixWord ++ tailWord_6588305) baseStart_6588305 baseEnd_6588305 := by
    simpa [prefixWord, tailWord_6588305, baseEnd_6588305] using wordTrace_append hprefix tailTrace_6588305
  have hstable : (prefixWord ++ tailWord_6588305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588305).length < 2 ^ (prefixWord ++ tailWord_6588305).sum := by decide
  have hdescent : baseEnd_6588305 < baseStart_6588305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588308 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_6588308 : Nat := 118140960795 + 6588308 * 2 ^ 59
def prefixEnd_6588308 : Nat := 4983230072969 + 3 ^ 40 * 6588308 * 2
def baseEnd_6588308 : Nat := 3382968703861914448350929

theorem tailTrace_6588308 : CollatzResearch.WordTrace tailWord_6588308 prefixEnd_6588308 3382968703861914448350929 := by
  unfold tailWord_6588308
  simp only [CollatzResearch.WordTrace]
  refine ⟨120147666907846392135142789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160196889210461856180190385 120147666907846392135142789)
  ·
    refine ⟨22527687545221198525339273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120147666907846392135142789 22527687545221198525339273)
    ·
      refine ⟨16895765658915898894004455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22527687545221198525339273 16895765658915898894004455)
      ·
        refine ⟨25343648488373848341006683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16895765658915898894004455 25343648488373848341006683)
        ·
          refine ⟨38015472732560772511510025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25343648488373848341006683 38015472732560772511510025)
          ·
            refine ⟨28511604549420579383632519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38015472732560772511510025 28511604549420579383632519)
            ·
              refine ⟨42767406824130869075448779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28511604549420579383632519 42767406824130869075448779)
              ·
                refine ⟨64151110236196303613173169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42767406824130869075448779 64151110236196303613173169)
                ·
                  refine ⟨48113332677147227709879877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64151110236196303613173169 48113332677147227709879877)
                  ·
                    refine ⟨9021249876965105195602477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48113332677147227709879877 9021249876965105195602477)
                    ·
                      refine ⟨3382968703861914448350929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9021249876965105195602477 3382968703861914448350929)
                      ·
                        rfl

theorem cell23_6588308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_6588308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588308 prefixEnd_6588308 := by exact prefixLift 6588308
  have htrace : WordTrace (prefixWord ++ tailWord_6588308) baseStart_6588308 baseEnd_6588308 := by
    simpa [prefixWord, tailWord_6588308, baseEnd_6588308] using wordTrace_append hprefix tailTrace_6588308
  have hstable : (prefixWord ++ tailWord_6588308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588308).length < 2 ^ (prefixWord ++ tailWord_6588308).sum := by decide
  have hdescent : baseEnd_6588308 < baseStart_6588308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588322 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_6588322 : Nat := 118140960795 + 6588322 * 2 ^ 59
def prefixEnd_6588322 : Nat := 4983230072969 + 3 ^ 40 * 6588322 * 2
def baseEnd_6588322 : Nat := 3382975892591077393575865

theorem tailTrace_6588322 : CollatzResearch.WordTrace tailWord_6588322 prefixEnd_6588322 3382975892591077393575865 := by
  unfold tailWord_6588322
  simp only [CollatzResearch.WordTrace]
  refine ⟨60073961109410516165323805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160197229625094709774196813 60073961109410516165323805)
  ·
    refine ⟨22527735416028943561996427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60073961109410516165323805 22527735416028943561996427)
    ·
      refine ⟨33791603124043415342994641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22527735416028943561996427 33791603124043415342994641)
      ·
        refine ⟨25343702343032561507245981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33791603124043415342994641 25343702343032561507245981)
        ·
          refine ⟨9503888378637210565217243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25343702343032561507245981 9503888378637210565217243)
          ·
            refine ⟨14255832567955815847825865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503888378637210565217243 14255832567955815847825865)
            ·
              refine ⟨10691874425966861885869399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14255832567955815847825865 10691874425966861885869399)
              ·
                refine ⟨16037811638950292828804099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10691874425966861885869399 16037811638950292828804099)
                ·
                  refine ⟨24056717458425439243206149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16037811638950292828804099 24056717458425439243206149)
                  ·
                    refine ⟨4510634523454769858101153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24056717458425439243206149 4510634523454769858101153)
                    ·
                      refine ⟨3382975892591077393575865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510634523454769858101153 3382975892591077393575865)
                      ·
                        rfl

theorem cell23_6588322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_6588322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588322 prefixEnd_6588322 := by exact prefixLift 6588322
  have htrace : WordTrace (prefixWord ++ tailWord_6588322) baseStart_6588322 baseEnd_6588322 := by
    simpa [prefixWord, tailWord_6588322, baseEnd_6588322] using wordTrace_append hprefix tailTrace_6588322
  have hstable : (prefixWord ++ tailWord_6588322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588322).length < 2 ^ (prefixWord ++ tailWord_6588322).sum := by decide
  have hdescent : baseEnd_6588322 < baseStart_6588322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588388 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_6588388 : Nat := 118140960795 + 6588388 * 2 ^ 59
def prefixEnd_6588388 : Nat := 4983230072969 + 3 ^ 40 * 6588388 * 2
def baseEnd_6588388 : Nat := 1127669927438091378450187

theorem tailTrace_6588388 : CollatzResearch.WordTrace tailWord_6588388 prefixEnd_6588388 1127669927438091378450187 := by
  unfold tailWord_6588388
  simp only [CollatzResearch.WordTrace]
  refine ⟨120149125827701478966598909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160198834436935305288798545 120149125827701478966598909)
  ·
    refine ⟨45055922185388054612474591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120149125827701478966598909 45055922185388054612474591)
    ·
      refine ⟨67583883278082081918711887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45055922185388054612474591 67583883278082081918711887)
      ·
        refine ⟨101375824917123122878067831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67583883278082081918711887 101375824917123122878067831)
        ·
          refine ⟨152063737375684684317101747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101375824917123122878067831 152063737375684684317101747)
          ·
            refine ⟨228095606063527026475652621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152063737375684684317101747 228095606063527026475652621)
            ·
              refine ⟨85535852273822634928369733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228095606063527026475652621 85535852273822634928369733)
              ·
                refine ⟨16037972301341744049069325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85535852273822634928369733 16037972301341744049069325)
                ·
                  refine ⟨6014239613003154018400997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16037972301341744049069325 6014239613003154018400997)
                  ·
                    refine ⟨1127669927438091378450187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6014239613003154018400997 1127669927438091378450187)
                    ·
                      rfl

theorem cell23_6588388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_6588388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588388 prefixEnd_6588388 := by exact prefixLift 6588388
  have htrace : WordTrace (prefixWord ++ tailWord_6588388) baseStart_6588388 baseEnd_6588388 := by
    simpa [prefixWord, tailWord_6588388, baseEnd_6588388] using wordTrace_append hprefix tailTrace_6588388
  have hstable : (prefixWord ++ tailWord_6588388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588388).length < 2 ^ (prefixWord ++ tailWord_6588388).sum := by decide
  have hdescent : baseEnd_6588388 < baseStart_6588388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588479 : List Nat := [1, 1, 2, 2, 3, 1, 6, 2, 1, 1, 3]
def baseStart_6588479 : Nat := 118140960795 + 6588479 * 2 ^ 59
def prefixEnd_6588479 : Nat := 4983230072969 + 3 ^ 40 * 6588479 * 2
def baseEnd_6588479 : Nat := 3383056509053833279312643

theorem tailTrace_6588479 : CollatzResearch.WordTrace tailWord_6588479 prefixEnd_6588479 3383056509053833279312643 := by
  unfold tailWord_6588479
  simp only [CollatzResearch.WordTrace]
  refine ⟨240301570698073280474760491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160201047132048853649840327 240301570698073280474760491)
  ·
    refine ⟨360452356047109920712140737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240301570698073280474760491 360452356047109920712140737)
    ·
      refine ⟨270339267035332440534105553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360452356047109920712140737 270339267035332440534105553)
      ·
        refine ⟨202754450276499330400579165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270339267035332440534105553 202754450276499330400579165)
        ·
          refine ⟨76032918853687248900217187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202754450276499330400579165 76032918853687248900217187)
          ·
            refine ⟨114049378280530873350325781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76032918853687248900217187 114049378280530873350325781)
            ·
              refine ⟨5346064606899884688296521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114049378280530873350325781 5346064606899884688296521)
              ·
                refine ⟨4009548455174913516222391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5346064606899884688296521 4009548455174913516222391)
                ·
                  refine ⟨6014322682762370274333587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009548455174913516222391 6014322682762370274333587)
                  ·
                    refine ⟨9021484024143555411500381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6014322682762370274333587 9021484024143555411500381)
                    ·
                      refine ⟨3383056509053833279312643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9021484024143555411500381 3383056509053833279312643)
                      ·
                        rfl

theorem cell23_6588479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_6588479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588479 prefixEnd_6588479 := by exact prefixLift 6588479
  have htrace : WordTrace (prefixWord ++ tailWord_6588479) baseStart_6588479 baseEnd_6588479 := by
    simpa [prefixWord, tailWord_6588479, baseEnd_6588479] using wordTrace_append hprefix tailTrace_6588479
  have hstable : (prefixWord ++ tailWord_6588479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588479).length < 2 ^ (prefixWord ++ tailWord_6588479).sum := by decide
  have hdescent : baseEnd_6588479 < baseStart_6588479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588505 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 3]
def baseStart_6588505 : Nat := 118140960795 + 6588505 * 2 ^ 59
def prefixEnd_6588505 : Nat := 4983230072969 + 3 ^ 40 * 6588505 * 2
def baseEnd_6588505 : Nat := 3383069859550850177587523

theorem tailTrace_6588505 : CollatzResearch.WordTrace tailWord_6588505 prefixEnd_6588505 3383069859550850177587523 := by
  unfold tailWord_6588505
  simp only [CollatzResearch.WordTrace]
  refine ⟨240302518995979086915206969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160201679330652724610137979 240302518995979086915206969)
  ·
    refine ⟨180226889246984315186405227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240302518995979086915206969 180226889246984315186405227)
    ·
      refine ⟨270340333870476472779607841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180226889246984315186405227 270340333870476472779607841)
      ·
        refine ⟨202755250402857354584705881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270340333870476472779607841 202755250402857354584705881)
        ·
          refine ⟨152066437802143015938529411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202755250402857354584705881 152066437802143015938529411)
          ·
            refine ⟨228099656703214523907794117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152066437802143015938529411 228099656703214523907794117)
            ·
              refine ⟨42768685631852723232711397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228099656703214523907794117 42768685631852723232711397)
              ·
                refine ⟨8019128555972385606133387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42768685631852723232711397 8019128555972385606133387)
                ·
                  refine ⟨12028692833958578409200081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8019128555972385606133387 12028692833958578409200081)
                  ·
                    refine ⟨9021519625468933806900061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12028692833958578409200081 9021519625468933806900061)
                    ·
                      refine ⟨3383069859550850177587523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9021519625468933806900061 3383069859550850177587523)
                      ·
                        rfl

theorem cell23_6588505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_6588505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588505 prefixEnd_6588505 := by exact prefixLift 6588505
  have htrace : WordTrace (prefixWord ++ tailWord_6588505) baseStart_6588505 baseEnd_6588505 := by
    simpa [prefixWord, tailWord_6588505, baseEnd_6588505] using wordTrace_append hprefix tailTrace_6588505
  have hstable : (prefixWord ++ tailWord_6588505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588505).length < 2 ^ (prefixWord ++ tailWord_6588505).sum := by decide
  have hdescent : baseEnd_6588505 < baseStart_6588505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588552 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6588552 : Nat := 118140960795 + 6588552 * 2 ^ 59
def prefixEnd_6588552 : Nat := 4983230072969 + 3 ^ 40 * 6588552 * 2
def baseEnd_6588552 : Nat := 3383093993141611493699807

theorem tailTrace_6588552 : CollatzResearch.WordTrace tailWord_6588552 prefixEnd_6588552 3383093993141611493699807 := by
  unfold tailWord_6588552
  simp only [CollatzResearch.WordTrace]
  refine ⟨120152116613404406971083955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160202822151205875961445273 120152116613404406971083955)
  ·
    refine ⟨180228174920106610456625933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120152116613404406971083955 180228174920106610456625933)
    ·
      refine ⟨67585565595039978921234725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180228174920106610456625933 67585565595039978921234725)
      ·
        refine ⟨12672293549069996047731511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67585565595039978921234725 12672293549069996047731511)
        ·
          refine ⟨19008440323604994071597267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12672293549069996047731511 19008440323604994071597267)
          ·
            refine ⟨28512660485407491107395901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19008440323604994071597267 28512660485407491107395901)
            ·
              refine ⟨10692247682027809165273463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28512660485407491107395901 10692247682027809165273463)
              ·
                refine ⟨16038371523041713747910195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10692247682027809165273463 16038371523041713747910195)
                ·
                  refine ⟨24057557284562570621865293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16038371523041713747910195 24057557284562570621865293)
                  ·
                    refine ⟨9021583981710963983199485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24057557284562570621865293 9021583981710963983199485)
                    ·
                      refine ⟨3383093993141611493699807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9021583981710963983199485 3383093993141611493699807)
                      ·
                        rfl

theorem cell23_6588552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6588552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588552 prefixEnd_6588552 := by exact prefixLift 6588552
  have htrace : WordTrace (prefixWord ++ tailWord_6588552) baseStart_6588552 baseEnd_6588552 := by
    simpa [prefixWord, tailWord_6588552, baseEnd_6588552] using wordTrace_append hprefix tailTrace_6588552
  have hstable : (prefixWord ++ tailWord_6588552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588552).length < 2 ^ (prefixWord ++ tailWord_6588552).sum := by decide
  have hdescent : baseEnd_6588552 < baseStart_6588552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588570 : List Nat := [3, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6588570 : Nat := 118140960795 + 6588570 * 2 ^ 59
def prefixEnd_6588570 : Nat := 4983230072969 + 3 ^ 40 * 6588570 * 2
def baseEnd_6588570 : Nat := 3383103235793392423274725

theorem tailTrace_6588570 : CollatzResearch.WordTrace tailWord_6588570 prefixEnd_6588570 3383103235793392423274725 := by
  unfold tailWord_6588570
  simp only [CollatzResearch.WordTrace]
  refine ⟨60076222435185900754080791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160203259827162402010882109 60076222435185900754080791)
  ·
    refine ⟨90114333652778851131121187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60076222435185900754080791 90114333652778851131121187)
    ·
      refine ⟨135171500479168276696681781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90114333652778851131121187 135171500479168276696681781)
      ·
        refine ⟨12672328169922025940313917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135171500479168276696681781 12672328169922025940313917)
        ·
          refine ⟨4752123063720759727617719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12672328169922025940313917 4752123063720759727617719)
          ·
            refine ⟨7128184595581139591426579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752123063720759727617719 7128184595581139591426579)
            ·
              refine ⟨10692276893371709387139869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128184595581139591426579 10692276893371709387139869)
              ·
                refine ⟨4009603835014391020177451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10692276893371709387139869 4009603835014391020177451)
                ·
                  refine ⟨6014405752521586530266177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009603835014391020177451 6014405752521586530266177)
                  ·
                    refine ⟨4510804314391189897699633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6014405752521586530266177 4510804314391189897699633)
                    ·
                      refine ⟨3383103235793392423274725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510804314391189897699633 3383103235793392423274725)
                      ·
                        rfl

theorem cell23_6588570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6588570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588570 prefixEnd_6588570 := by exact prefixLift 6588570
  have htrace : WordTrace (prefixWord ++ tailWord_6588570) baseStart_6588570 baseEnd_6588570 := by
    simpa [prefixWord, tailWord_6588570, baseEnd_6588570] using wordTrace_append hprefix tailTrace_6588570
  have hstable : (prefixWord ++ tailWord_6588570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588570).length < 2 ^ (prefixWord ++ tailWord_6588570).sum := by decide
  have hdescent : baseEnd_6588570 < baseStart_6588570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588635 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 1, 7, 2]
def baseStart_6588635 : Nat := 118140960795 + 6588635 * 2 ^ 59
def prefixEnd_6588635 : Nat := 4983230072969 + 3 ^ 40 * 6588635 * 2
def baseEnd_6588635 : Nat := 3383136612035934668961925

theorem tailTrace_6588635 : CollatzResearch.WordTrace tailWord_6588635 prefixEnd_6588635 3383136612035934668961925 := by
  unfold tailWord_6588635
  simp only [CollatzResearch.WordTrace]
  refine ⟨240307260485508119117439359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160204840323672079411626239 240307260485508119117439359)
  ·
    refine ⟨360460890728262178676159039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240307260485508119117439359 360460890728262178676159039)
    ·
      refine ⟨540691336092393268014238559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360460890728262178676159039 540691336092393268014238559)
      ·
        refine ⟨811037004138589902021357839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540691336092393268014238559 811037004138589902021357839)
        ·
          refine ⟨1216555506207884853032036759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811037004138589902021357839 1216555506207884853032036759)
          ·
            refine ⟨1824833259311827279548055139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216555506207884853032036759 1824833259311827279548055139)
            ·
              refine ⟨2737249888967740919322082709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824833259311827279548055139 2737249888967740919322082709)
              ·
                refine ⟨128308588545362855593222627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2737249888967740919322082709 128308588545362855593222627)
                ·
                  refine ⟨192462882818044283389833941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128308588545362855593222627 192462882818044283389833941)
                  ·
                    refine ⟨4510848816047912891949233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 192462882818044283389833941 4510848816047912891949233)
                    ·
                      refine ⟨3383136612035934668961925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510848816047912891949233 3383136612035934668961925)
                      ·
                        rfl

theorem cell23_6588635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 7, 2].length) (baseStart_6588635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588635 prefixEnd_6588635 := by exact prefixLift 6588635
  have htrace : WordTrace (prefixWord ++ tailWord_6588635) baseStart_6588635 baseEnd_6588635 := by
    simpa [prefixWord, tailWord_6588635, baseEnd_6588635] using wordTrace_append hprefix tailTrace_6588635
  have hstable : (prefixWord ++ tailWord_6588635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588635).length < 2 ^ (prefixWord ++ tailWord_6588635).sum := by decide
  have hdescent : baseEnd_6588635 < baseStart_6588635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588643 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6588643 : Nat := 118140960795 + 6588643 * 2 ^ 59
def prefixEnd_6588643 : Nat := 4983230072969 + 3 ^ 40 * 6588643 * 2
def baseEnd_6588643 : Nat := 3383140719881170637661889

theorem tailTrace_6588643 : CollatzResearch.WordTrace tailWord_6588643 prefixEnd_6588643 3383140719881170637661889 := by
  unfold tailWord_6588643
  simp only [CollatzResearch.WordTrace]
  refine ⟨240307552269479136483730583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160205034846319424322487055 240307552269479136483730583)
  ·
    refine ⟨360461328404218704725595875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240307552269479136483730583 360461328404218704725595875)
    ·
      refine ⟨540691992606328057088393813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360461328404218704725595875 540691992606328057088393813)
      ·
        refine ⟨6336234288355406919004615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 540691992606328057088393813 6336234288355406919004615)
        ·
          refine ⟨9504351432533110378506923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6336234288355406919004615 9504351432533110378506923)
          ·
            refine ⟨14256527148799665567760385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9504351432533110378506923 14256527148799665567760385)
            ·
              refine ⟨10692395361599749175820289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14256527148799665567760385 10692395361599749175820289)
              ·
                refine ⟨8019296521199811881865217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10692395361599749175820289 8019296521199811881865217)
                ·
                  refine ⟨6014472390899858911398913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8019296521199811881865217 6014472390899858911398913)
                  ·
                    refine ⟨4510854293174894183549185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6014472390899858911398913 4510854293174894183549185)
                    ·
                      refine ⟨3383140719881170637661889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510854293174894183549185 3383140719881170637661889)
                      ·
                        rfl

theorem cell23_6588643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6588643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588643 prefixEnd_6588643 := by exact prefixLift 6588643
  have htrace : WordTrace (prefixWord ++ tailWord_6588643) baseStart_6588643 baseEnd_6588643 := by
    simpa [prefixWord, tailWord_6588643, baseEnd_6588643] using wordTrace_append hprefix tailTrace_6588643
  have hstable : (prefixWord ++ tailWord_6588643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588643).length < 2 ^ (prefixWord ++ tailWord_6588643).sum := by decide
  have hdescent : baseEnd_6588643 < baseStart_6588643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588655 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_6588655 : Nat := 118140960795 + 6588655 * 2 ^ 59
def prefixEnd_6588655 : Nat := 4983230072969 + 3 ^ 40 * 6588655 * 2
def baseEnd_6588655 : Nat := 3383146881649024590711833

theorem tailTrace_6588655 : CollatzResearch.WordTrace tailWord_6588655 prefixEnd_6588655 3383146881649024590711833 := by
  unfold tailWord_6588655
  simp only [CollatzResearch.WordTrace]
  refine ⟨240307989945435662533167419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160205326630290441688778279 240307989945435662533167419)
  ·
    refine ⟨360461984918153493799751129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240307989945435662533167419 360461984918153493799751129)
    ·
      refine ⟨270346488688615120349813347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360461984918153493799751129 270346488688615120349813347)
      ·
        refine ⟨405519733032922680524720021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270346488688615120349813347 405519733032922680524720021)
        ·
          refine ⟨19008737485918250649596251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 405519733032922680524720021 19008737485918250649596251)
          ·
            refine ⟨28513106228877375974394377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19008737485918250649596251 28513106228877375974394377)
            ·
              refine ⟨21384829671658031980795783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28513106228877375974394377 21384829671658031980795783)
              ·
                refine ⟨32077244507487047971193675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21384829671658031980795783 32077244507487047971193675)
                ·
                  refine ⟨48115866761230571956790513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32077244507487047971193675 48115866761230571956790513)
                  ·
                    refine ⟨36086900070922928967592885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48115866761230571956790513 36086900070922928967592885)
                    ·
                      refine ⟨3383146881649024590711833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36086900070922928967592885 3383146881649024590711833)
                      ·
                        rfl

theorem cell23_6588655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_6588655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588655 prefixEnd_6588655 := by exact prefixLift 6588655
  have htrace : WordTrace (prefixWord ++ tailWord_6588655) baseStart_6588655 baseEnd_6588655 := by
    simpa [prefixWord, tailWord_6588655, baseEnd_6588655] using wordTrace_append hprefix tailTrace_6588655
  have hstable : (prefixWord ++ tailWord_6588655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588655).length < 2 ^ (prefixWord ++ tailWord_6588655).sum := by decide
  have hdescent : baseEnd_6588655 < baseStart_6588655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588682 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_6588682 : Nat := 118140960795 + 6588682 * 2 ^ 59
def prefixEnd_6588682 : Nat := 4983230072969 + 3 ^ 40 * 6588682 * 2
def baseEnd_6588682 : Nat := 3383160745626695985074209

theorem tailTrace_6588682 : CollatzResearch.WordTrace tailWord_6588682 prefixEnd_6588682 3383160745626695985074209 := by
  unfold tailWord_6588682
  simp only [CollatzResearch.WordTrace]
  refine ⟨60077243679084461536100075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160205983144225230762933533 60077243679084461536100075)
  ·
    refine ⟨90115865518626692304150113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60077243679084461536100075 90115865518626692304150113)
    ·
      refine ⟨67586899138970019228112585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90115865518626692304150113 67586899138970019228112585)
      ·
        refine ⟨50690174354227514421084439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67586899138970019228112585 50690174354227514421084439)
        ·
          refine ⟨76035261531341271631626659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50690174354227514421084439 76035261531341271631626659)
          ·
            refine ⟨114052892297011907447439989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76035261531341271631626659 114052892297011907447439989)
            ·
              refine ⟨10692458652844866323197499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114052892297011907447439989 10692458652844866323197499)
              ·
                refine ⟨16038687979267299484796249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10692458652844866323197499 16038687979267299484796249)
                ·
                  refine ⟨12029015984450474613597187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16038687979267299484796249 12029015984450474613597187)
                  ·
                    refine ⟨18043523976675711920395781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12029015984450474613597187 18043523976675711920395781)
                    ·
                      refine ⟨3383160745626695985074209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18043523976675711920395781 3383160745626695985074209)
                      ·
                        rfl

theorem cell23_6588682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_6588682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588682 prefixEnd_6588682 := by exact prefixLift 6588682
  have htrace : WordTrace (prefixWord ++ tailWord_6588682) baseStart_6588682 baseEnd_6588682 := by
    simpa [prefixWord, tailWord_6588682, baseEnd_6588682] using wordTrace_append hprefix tailTrace_6588682
  have hstable : (prefixWord ++ tailWord_6588682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588682).length < 2 ^ (prefixWord ++ tailWord_6588682).sum := by decide
  have hdescent : baseEnd_6588682 < baseStart_6588682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588695 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_6588695 : Nat := 118140960795 + 6588695 * 2 ^ 59
def prefixEnd_6588695 : Nat := 4983230072969 + 3 ^ 40 * 6588695 * 2
def baseEnd_6588695 : Nat := 3383167420875204434211649

theorem tailTrace_6588695 : CollatzResearch.WordTrace tailWord_6588695 prefixEnd_6588695 3383167420875204434211649 := by
  unfold tailWord_6588695
  simp only [CollatzResearch.WordTrace]
  refine ⟨240309448865290749364623539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160206299243527166243082359 240309448865290749364623539)
  ·
    refine ⟨360464173297936124046935309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240309448865290749364623539 360464173297936124046935309)
    ·
      refine ⟨135174064986726046517600741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360464173297936124046935309 135174064986726046517600741)
      ·
        refine ⟨25345137185011133722050139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135174064986726046517600741 25345137185011133722050139)
        ·
          refine ⟨38017705777516700583075209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25345137185011133722050139 38017705777516700583075209)
          ·
            refine ⟨28513279333137525437306407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38017705777516700583075209 28513279333137525437306407)
            ·
              refine ⟨42769918999706288155959611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28513279333137525437306407 42769918999706288155959611)
              ·
                refine ⟨64154878499559432233939417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42769918999706288155959611 64154878499559432233939417)
                ·
                  refine ⟨48116158874669574175454563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64154878499559432233939417 48116158874669574175454563)
                  ·
                    refine ⟨72174238312004361263181845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48116158874669574175454563 72174238312004361263181845)
                    ·
                      refine ⟨3383167420875204434211649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72174238312004361263181845 3383167420875204434211649)
                      ·
                        rfl

theorem cell23_6588695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_6588695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588695 prefixEnd_6588695 := by exact prefixLift 6588695
  have htrace : WordTrace (prefixWord ++ tailWord_6588695) baseStart_6588695 baseEnd_6588695 := by
    simpa [prefixWord, tailWord_6588695, baseEnd_6588695] using wordTrace_append hprefix tailTrace_6588695
  have hstable : (prefixWord ++ tailWord_6588695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588695).length < 2 ^ (prefixWord ++ tailWord_6588695).sum := by decide
  have hdescent : baseEnd_6588695 < baseStart_6588695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588709 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_6588709 : Nat := 118140960795 + 6588709 * 2 ^ 59
def prefixEnd_6588709 : Nat := 4983230072969 + 3 ^ 40 * 6588709 * 2
def baseEnd_6588709 : Nat := 1127724869868122459812195

theorem tailTrace_6588709 : CollatzResearch.WordTrace tailWord_6588709 prefixEnd_6588709 1127724869868122459812195 := by
  unfold tailWord_6588709
  simp only [CollatzResearch.WordTrace]
  refine ⟨240309959487240029755633181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160206639658160019837088787 240309959487240029755633181)
  ·
    refine ⟨90116234807715011158362443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240309959487240029755633181 90116234807715011158362443)
    ·
      refine ⟨135174352211572516737543665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90116234807715011158362443 135174352211572516737543665)
      ·
        refine ⟨101380764158679387553157749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135174352211572516737543665 101380764158679387553157749)
        ·
          refine ⟨9504446639876192583108539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101380764158679387553157749 9504446639876192583108539)
          ·
            refine ⟨14256669959814288874662809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9504446639876192583108539 14256669959814288874662809)
            ·
              refine ⟨10692502469860716655997107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14256669959814288874662809 10692502469860716655997107)
              ·
                refine ⟨16038753704791074983995661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10692502469860716655997107 16038753704791074983995661)
                ·
                  refine ⟨6014532639296653118998373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16038753704791074983995661 6014532639296653118998373)
                  ·
                    refine ⟨1127724869868122459812195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6014532639296653118998373 1127724869868122459812195)
                    ·
                      rfl

theorem cell23_6588709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_6588709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588709 prefixEnd_6588709 := by exact prefixLift 6588709
  have htrace : WordTrace (prefixWord ++ tailWord_6588709) baseStart_6588709 baseEnd_6588709 := by
    simpa [prefixWord, tailWord_6588709, baseEnd_6588709] using wordTrace_append hprefix tailTrace_6588709
  have hstable : (prefixWord ++ tailWord_6588709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588709).length < 2 ^ (prefixWord ++ tailWord_6588709).sum := by decide
  have hdescent : baseEnd_6588709 < baseStart_6588709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588725 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_6588725 : Nat := 118140960795 + 6588725 * 2 ^ 59
def prefixEnd_6588725 : Nat := 4983230072969 + 3 ^ 40 * 6588725 * 2
def baseEnd_6588725 : Nat := 3383182825294839316836511

theorem tailTrace_6588725 : CollatzResearch.WordTrace tailWord_6588725 prefixEnd_6588725 3383182825294839316836511 := by
  unfold tailWord_6588725
  simp only [CollatzResearch.WordTrace]
  refine ⟨240310543055182064488215629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160207028703454709658810419 240310543055182064488215629)
  ·
    refine ⟨90116453645693274183080861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240310543055182064488215629 90116453645693274183080861)
    ·
      refine ⟨33793670117134977818655323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90116453645693274183080861 33793670117134977818655323)
      ·
        refine ⟨50690505175702466727982985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33793670117134977818655323 50690505175702466727982985)
        ·
          refine ⟨38017878881776850045987239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50690505175702466727982985 38017878881776850045987239)
          ·
            refine ⟨57026818322665275068980859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38017878881776850045987239 57026818322665275068980859)
            ·
              refine ⟨85540227483997912603471289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57026818322665275068980859 85540227483997912603471289)
              ·
                refine ⟨64155170612998434452603467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85540227483997912603471289 64155170612998434452603467)
                ·
                  refine ⟨96232755919497651678905201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64155170612998434452603467 96232755919497651678905201)
                  ·
                    refine ⟨72174566939623238759178901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96232755919497651678905201 72174566939623238759178901)
                    ·
                      refine ⟨3383182825294839316836511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72174566939623238759178901 3383182825294839316836511)
                      ·
                        rfl

theorem cell23_6588725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_6588725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588725 prefixEnd_6588725 := by exact prefixLift 6588725
  have htrace : WordTrace (prefixWord ++ tailWord_6588725) baseStart_6588725 baseEnd_6588725 := by
    simpa [prefixWord, tailWord_6588725, baseEnd_6588725] using wordTrace_append hprefix tailTrace_6588725
  have hstable : (prefixWord ++ tailWord_6588725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588725).length < 2 ^ (prefixWord ++ tailWord_6588725).sum := by decide
  have hdescent : baseEnd_6588725 < baseStart_6588725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588752 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 1, 5]
def baseStart_6588752 : Nat := 118140960795 + 6588752 * 2 ^ 59
def prefixEnd_6588752 : Nat := 4983230072969 + 3 ^ 40 * 6588752 * 2
def baseEnd_6588752 : Nat := 1127732229757503570399629

theorem tailTrace_6588752 : CollatzResearch.WordTrace tailWord_6588752 prefixEnd_6588752 1127732229757503570399629 := by
  unfold tailWord_6588752
  simp only [CollatzResearch.WordTrace]
  refine ⟨120155763913042124049724255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160207685217389498732965673 120155763913042124049724255)
  ·
    refine ⟨180233645869563186074586383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120155763913042124049724255 180233645869563186074586383)
    ·
      refine ⟨270350468804344779111879575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180233645869563186074586383 270350468804344779111879575)
      ·
        refine ⟨405525703206517168667819363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270350468804344779111879575 405525703206517168667819363)
        ·
          refine ⟨608288554809775753001729045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405525703206517168667819363 608288554809775753001729045)
          ·
            refine ⟨28513526006708238421956049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 608288554809775753001729045 28513526006708238421956049)
            ·
              refine ⟨21385144505031178816467037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28513526006708238421956049 21385144505031178816467037)
              ·
                refine ⟨8019429189386692056175139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21385144505031178816467037 8019429189386692056175139)
                ·
                  refine ⟨12029143784080038084262709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8019429189386692056175139 12029143784080038084262709)
                  ·
                    refine ⟨1127732229757503570399629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12029143784080038084262709 1127732229757503570399629)
                    ·
                      rfl

theorem cell23_6588752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_6588752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588752 prefixEnd_6588752 := by exact prefixLift 6588752
  have htrace : WordTrace (prefixWord ++ tailWord_6588752) baseStart_6588752 baseEnd_6588752 := by
    simpa [prefixWord, tailWord_6588752, baseEnd_6588752] using wordTrace_append hprefix tailTrace_6588752
  have hstable : (prefixWord ++ tailWord_6588752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588752).length < 2 ^ (prefixWord ++ tailWord_6588752).sum := by decide
  have hdescent : baseEnd_6588752 < baseStart_6588752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588759 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 2, 3, 2]
def baseStart_6588759 : Nat := 118140960795 + 6588759 * 2 ^ 59
def prefixEnd_6588759 : Nat := 4983230072969 + 3 ^ 40 * 6588759 * 2
def baseEnd_6588759 : Nat := 3383200283637092183811355

theorem tailTrace_6588759 : CollatzResearch.WordTrace tailWord_6588759 prefixEnd_6588759 3383200283637092183811355 := by
  unfold tailWord_6588759
  simp only [CollatzResearch.WordTrace]
  refine ⟨240311783137058888294953331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160207855424705925529968887 240311783137058888294953331)
  ·
    refine ⟨360467674705588332442429997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240311783137058888294953331 360467674705588332442429997)
    ·
      refine ⟨135175378014595624665911249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360467674705588332442429997 135175378014595624665911249)
      ·
        refine ⟨101381533510946718499433437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135175378014595624665911249 101381533510946718499433437)
        ·
          refine ⟨38018075066605019437287539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101381533510946718499433437 38018075066605019437287539)
          ·
            refine ⟨57027112599907529155931309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38018075066605019437287539 57027112599907529155931309)
            ·
              refine ⟨21385167224965323433474241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57027112599907529155931309 21385167224965323433474241)
              ·
                refine ⟨16038875418723992575105681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21385167224965323433474241 16038875418723992575105681)
                ·
                  refine ⟨12029156564042994431329261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16038875418723992575105681 12029156564042994431329261)
                  ·
                    refine ⟨4510933711516122911748473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12029156564042994431329261 4510933711516122911748473)
                    ·
                      refine ⟨3383200283637092183811355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4510933711516122911748473 3383200283637092183811355)
                      ·
                        rfl

theorem cell23_6588759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_6588759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588759 prefixEnd_6588759 := by exact prefixLift 6588759
  have htrace : WordTrace (prefixWord ++ tailWord_6588759) baseStart_6588759 baseEnd_6588759 := by
    simpa [prefixWord, tailWord_6588759, baseEnd_6588759] using wordTrace_append hprefix tailTrace_6588759
  have hstable : (prefixWord ++ tailWord_6588759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588759).length < 2 ^ (prefixWord ++ tailWord_6588759).sum := by decide
  have hdescent : baseEnd_6588759 < baseStart_6588759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588772 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_6588772 : Nat := 118140960795 + 6588772 * 2 ^ 59
def prefixEnd_6588772 : Nat := 4983230072969 + 3 ^ 40 * 6588772 * 2
def baseEnd_6588772 : Nat := 3383206958885600632948795

theorem tailTrace_6588772 : CollatzResearch.WordTrace tailWord_6588772 prefixEnd_6588772 3383206958885600632948795 := by
  unfold tailWord_6588772
  simp only [CollatzResearch.WordTrace]
  refine ⟨120156128643005895757588285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160208171524007861010117713 120156128643005895757588285)
  ·
    refine ⟨45058548241127210909095607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120156128643005895757588285 45058548241127210909095607)
    ·
      refine ⟨67587822361690816363643411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45058548241127210909095607 67587822361690816363643411)
      ·
        refine ⟨101381733542536224545465117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67587822361690816363643411 101381733542536224545465117)
        ·
          refine ⟨38018150078451084204549419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101381733542536224545465117 38018150078451084204549419)
          ·
            refine ⟨57027225117676626306824129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38018150078451084204549419 57027225117676626306824129)
            ·
              refine ⟨42770418838257469730118097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57027225117676626306824129 42770418838257469730118097)
              ·
                refine ⟨32077814128693102297588573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42770418838257469730118097 32077814128693102297588573)
                ·
                  refine ⟨12029180298259913361595715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32077814128693102297588573 12029180298259913361595715)
                  ·
                    refine ⟨18043770447389870042393573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12029180298259913361595715 18043770447389870042393573)
                    ·
                      refine ⟨3383206958885600632948795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18043770447389870042393573 3383206958885600632948795)
                      ·
                        rfl

theorem cell23_6588772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_6588772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588772 prefixEnd_6588772 := by exact prefixLift 6588772
  have htrace : WordTrace (prefixWord ++ tailWord_6588772) baseStart_6588772 baseEnd_6588772 := by
    simpa [prefixWord, tailWord_6588772, baseEnd_6588772] using wordTrace_append hprefix tailTrace_6588772
  have hstable : (prefixWord ++ tailWord_6588772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588772).length < 2 ^ (prefixWord ++ tailWord_6588772).sum := by decide
  have hdescent : baseEnd_6588772 < baseStart_6588772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588789 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6588789 : Nat := 118140960795 + 6588789 * 2 ^ 59
def prefixEnd_6588789 : Nat := 4983230072969 + 3 ^ 40 * 6588789 * 2
def baseEnd_6588789 : Nat := 3383215688056727066436217

theorem tailTrace_6588789 : CollatzResearch.WordTrace tailWord_6588789 prefixEnd_6588789 3383215688056727066436217 := by
  unfold tailWord_6588789
  simp only [CollatzResearch.WordTrace]
  refine ⟨240312877326950203418545421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160208584884633468945696947 240312877326950203418545421)
  ·
    refine ⟨90117328997606326281954533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240312877326950203418545421 90117328997606326281954533)
    ·
      refine ⟨16896999187051186177866475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90117328997606326281954533 16896999187051186177866475)
      ·
        refine ⟨25345498780576779266799713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16896999187051186177866475 25345498780576779266799713)
        ·
          refine ⟨19009124085432584450099785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25345498780576779266799713 19009124085432584450099785)
          ·
            refine ⟨14256843064074438337574839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19009124085432584450099785 14256843064074438337574839)
            ·
              refine ⟨21385264596111657506362259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14256843064074438337574839 21385264596111657506362259)
              ·
                refine ⟨32077896894167486259543389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21385264596111657506362259 32077896894167486259543389)
                ·
                  refine ⟨12029211335312807347328771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32077896894167486259543389 12029211335312807347328771)
                  ·
                    refine ⟨18043817002969211020993157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12029211335312807347328771 18043817002969211020993157)
                    ·
                      refine ⟨3383215688056727066436217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18043817002969211020993157 3383215688056727066436217)
                      ·
                        rfl

theorem cell23_6588789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6588789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588789 prefixEnd_6588789 := by exact prefixLift 6588789
  have htrace : WordTrace (prefixWord ++ tailWord_6588789) baseStart_6588789 baseEnd_6588789 := by
    simpa [prefixWord, tailWord_6588789, baseEnd_6588789] using wordTrace_append hprefix tailTrace_6588789
  have hstable : (prefixWord ++ tailWord_6588789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588789).length < 2 ^ (prefixWord ++ tailWord_6588789).sum := by decide
  have hdescent : baseEnd_6588789 < baseStart_6588789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588795 : List Nat := [1, 1, 1, 1, 1, 7, 2, 9]
def baseStart_6588795 : Nat := 118140960795 + 6588795 * 2 ^ 59
def prefixEnd_6588795 : Nat := 4983230072969 + 3 ^ 40 * 6588795 * 2
def baseEnd_6588795 : Nat := 125304398849653853443007

theorem tailTrace_6588795 : CollatzResearch.WordTrace tailWord_6588795 prefixEnd_6588795 125304398849653853443007 := by
  unfold tailWord_6588795
  simp only [CollatzResearch.WordTrace]
  refine ⟨240313096164928466443263839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160208730776618977628842559 240313096164928466443263839)
  ·
    refine ⟨360469644247392699664895759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240313096164928466443263839 360469644247392699664895759)
    ·
      refine ⟨540704466371089049497343639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360469644247392699664895759 540704466371089049497343639)
      ·
        refine ⟨811056699556633574246015459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540704466371089049497343639 811056699556633574246015459)
        ·
          refine ⟨1216585049334950361369023189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811056699556633574246015459 1216585049334950361369023189)
          ·
            refine ⟨28513712093787899094586481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1216585049334950361369023189 28513712093787899094586481)
            ·
              refine ⟨21385284070340924320939861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28513712093787899094586481 21385284070340924320939861)
              ·
                refine ⟨125304398849653853443007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21385284070340924320939861 125304398849653853443007)
                ·
                  rfl

theorem cell23_6588795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 9].length) (baseStart_6588795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588795 prefixEnd_6588795 := by exact prefixLift 6588795
  have htrace : WordTrace (prefixWord ++ tailWord_6588795) baseStart_6588795 baseEnd_6588795 := by
    simpa [prefixWord, tailWord_6588795, baseEnd_6588795] using wordTrace_append hprefix tailTrace_6588795
  have hstable : (prefixWord ++ tailWord_6588795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588795).length < 2 ^ (prefixWord ++ tailWord_6588795).sum := by decide
  have hdescent : baseEnd_6588795 < baseStart_6588795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588809 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 5]
def baseStart_6588809 : Nat := 118140960795 + 6588809 * 2 ^ 59
def prefixEnd_6588809 : Nat := 4983230072969 + 3 ^ 40 * 6588809 * 2
def baseEnd_6588809 : Nat := 3383225957669816988186125

theorem tailTrace_6588809 : CollatzResearch.WordTrace tailWord_6588809 prefixEnd_6588809 3383225957669816988186125 := by
  unfold tailWord_6588809
  simp only [CollatzResearch.WordTrace]
  refine ⟨240313606786877746834273481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160209071191251831222848987 240313606786877746834273481)
  ·
    refine ⟨180235205090158310125705111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240313606786877746834273481 180235205090158310125705111)
    ·
      refine ⟨270352807635237465188557667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180235205090158310125705111 270352807635237465188557667)
      ·
        refine ⟨405529211452856197782836501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270352807635237465188557667 405529211452856197782836501)
        ·
          refine ⟨19009181786852634271070461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 405529211452856197782836501 19009181786852634271070461)
          ·
            refine ⟨7128443170069737851651423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19009181786852634271070461 7128443170069737851651423)
            ·
              refine ⟨10692664755104606777477135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128443170069737851651423 10692664755104606777477135)
              ·
                refine ⟨16038997132656910166215703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10692664755104606777477135 16038997132656910166215703)
                ·
                  refine ⟨24058495698985365249323555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16038997132656910166215703 24058495698985365249323555)
                  ·
                    refine ⟨36087743548478047873985333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24058495698985365249323555 36087743548478047873985333)
                    ·
                      refine ⟨3383225957669816988186125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36087743548478047873985333 3383225957669816988186125)
                      ·
                        rfl

theorem cell23_6588809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 5].length) (baseStart_6588809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588809 prefixEnd_6588809 := by exact prefixLift 6588809
  have htrace : WordTrace (prefixWord ++ tailWord_6588809) baseStart_6588809 baseEnd_6588809 := by
    simpa [prefixWord, tailWord_6588809, baseEnd_6588809] using wordTrace_append hprefix tailTrace_6588809
  have hstable : (prefixWord ++ tailWord_6588809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588809).length < 2 ^ (prefixWord ++ tailWord_6588809).sum := by decide
  have hdescent : baseEnd_6588809 < baseStart_6588809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588825 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 1, 9]
def baseStart_6588825 : Nat := 118140960795 + 6588825 * 2 ^ 59
def prefixEnd_6588825 : Nat := 4983230072969 + 3 ^ 40 * 6588825 * 2
def baseEnd_6588825 : Nat := 1127744724453429641862017

theorem tailTrace_6588825 : CollatzResearch.WordTrace tailWord_6588825 prefixEnd_6588825 1127744724453429641862017 := by
  unfold tailWord_6588825
  simp only [CollatzResearch.WordTrace]
  refine ⟨240314190354819781566855929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160209460236546521044570619 240314190354819781566855929)
  ·
    refine ⟨180235642766114836175141947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240314190354819781566855929 180235642766114836175141947)
    ·
      refine ⟨270353464149172254262712921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180235642766114836175141947 270353464149172254262712921)
      ·
        refine ⟨202765098111879190697034691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270353464149172254262712921 202765098111879190697034691)
        ·
          refine ⟨304147647167818786045552037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202765098111879190697034691 304147647167818786045552037)
          ·
            refine ⟨57027683843966022383541007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304147647167818786045552037 57027683843966022383541007)
            ·
              refine ⟨85541525765949033575311511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57027683843966022383541007 85541525765949033575311511)
              ·
                refine ⟨128312288648923550362967267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85541525765949033575311511 128312288648923550362967267)
                ·
                  refine ⟨192468432973385325544450901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128312288648923550362967267 192468432973385325544450901)
                  ·
                    refine ⟨1127744724453429641862017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192468432973385325544450901 1127744724453429641862017)
                    ·
                      rfl

theorem cell23_6588825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_6588825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588825 prefixEnd_6588825 := by exact prefixLift 6588825
  have htrace : WordTrace (prefixWord ++ tailWord_6588825) baseStart_6588825 baseEnd_6588825 := by
    simpa [prefixWord, tailWord_6588825, baseEnd_6588825] using wordTrace_append hprefix tailTrace_6588825
  have hstable : (prefixWord ++ tailWord_6588825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588825).length < 2 ^ (prefixWord ++ tailWord_6588825).sum := by decide
  have hdescent : baseEnd_6588825 < baseStart_6588825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588829 : List Nat := [1, 4, 2, 1, 4, 2, 1, 8]
def baseStart_6588829 : Nat := 118140960795 + 6588829 * 2 ^ 59
def prefixEnd_6588829 : Nat := 4983230072969 + 3 ^ 40 * 6588829 * 2
def baseEnd_6588829 : Nat := 125305045454922478145779

theorem tailTrace_6588829 : CollatzResearch.WordTrace tailWord_6588829 prefixEnd_6588829 125305045454922478145779 := by
  unfold tailWord_6588829
  simp only [CollatzResearch.WordTrace]
  refine ⟨240314336246805290250001541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160209557497870193500001027 240314336246805290250001541)
  ·
    refine ⟨45058938046275991921875289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240314336246805290250001541 45058938046275991921875289)
    ·
      refine ⟨33794203534706993941406467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45058938046275991921875289 33794203534706993941406467)
      ·
        refine ⟨50691305302060490912109701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33794203534706993941406467 50691305302060490912109701)
        ·
          refine ⟨9504619744136342046020569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50691305302060490912109701 9504619744136342046020569)
          ·
            refine ⟨7128464808102256534515427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9504619744136342046020569 7128464808102256534515427)
            ·
              refine ⟨10692697212153384801773141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128464808102256534515427 10692697212153384801773141)
              ·
                refine ⟨125305045454922478145779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10692697212153384801773141 125305045454922478145779)
                ·
                  rfl

theorem cell23_6588829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 8].length) (baseStart_6588829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588829 prefixEnd_6588829 := by exact prefixLift 6588829
  have htrace : WordTrace (prefixWord ++ tailWord_6588829) baseStart_6588829 baseEnd_6588829 := by
    simpa [prefixWord, tailWord_6588829, baseEnd_6588829] using wordTrace_append hprefix tailTrace_6588829
  have hstable : (prefixWord ++ tailWord_6588829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588829).length < 2 ^ (prefixWord ++ tailWord_6588829).sum := by decide
  have hdescent : baseEnd_6588829 < baseStart_6588829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588839 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_6588839 : Nat := 118140960795 + 6588839 * 2 ^ 59
def prefixEnd_6588839 : Nat := 4983230072969 + 3 ^ 40 * 6588839 * 2
def baseEnd_6588839 : Nat := 3383241362089451870810987

theorem tailTrace_6588839 : CollatzResearch.WordTrace tailWord_6588839 prefixEnd_6588839 3383241362089451870810987 := by
  unfold tailWord_6588839
  simp only [CollatzResearch.WordTrace]
  refine ⟨240314700976769061957865571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160209800651179374638577047 240314700976769061957865571)
  ·
    refine ⟨360472051465153592936798357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240314700976769061957865571 360472051465153592936798357)
    ·
      refine ⟨16897127412429074668912423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 360472051465153592936798357 16897127412429074668912423)
      ·
        refine ⟨25345691118643612003368635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16897127412429074668912423 25345691118643612003368635)
        ·
          refine ⟨38018536677965418005052953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25345691118643612003368635 38018536677965418005052953)
          ·
            refine ⟨28513902508474063503789715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38018536677965418005052953 28513902508474063503789715)
            ·
              refine ⟨42770853762711095255684573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28513902508474063503789715 42770853762711095255684573)
              ·
                refine ⟨16039070161016660720881715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42770853762711095255684573 16039070161016660720881715)
                ·
                  refine ⟨24058605241524991081322573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16039070161016660720881715 24058605241524991081322573)
                  ·
                    refine ⟨9021976965571871655495965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24058605241524991081322573 9021976965571871655495965)
                    ·
                      refine ⟨3383241362089451870810987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9021976965571871655495965 3383241362089451870810987)
                      ·
                        rfl

theorem cell23_6588839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_6588839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588839 prefixEnd_6588839 := by exact prefixLift 6588839
  have htrace : WordTrace (prefixWord ++ tailWord_6588839) baseStart_6588839 baseEnd_6588839 := by
    simpa [prefixWord, tailWord_6588839, baseEnd_6588839] using wordTrace_append hprefix tailTrace_6588839
  have hstable : (prefixWord ++ tailWord_6588839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588839).length < 2 ^ (prefixWord ++ tailWord_6588839).sum := by decide
  have hdescent : baseEnd_6588839 < baseStart_6588839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588872 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 2, 6]
def baseStart_6588872 : Nat := 118140960795 + 6588872 * 2 ^ 59
def prefixEnd_6588872 : Nat := 4983230072969 + 3 ^ 40 * 6588872 * 2
def baseEnd_6588872 : Nat := 1127752768983683413899445

theorem tailTrace_6588872 : CollatzResearch.WordTrace tailWord_6588872 prefixEnd_6588872 1127752768983683413899445 := by
  unfold tailWord_6588872
  simp only [CollatzResearch.WordTrace]
  refine ⟨120157952292824754296908435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160210603057099672395877913 120157952292824754296908435)
  ·
    refine ⟨180236928439237131445362653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120157952292824754296908435 180236928439237131445362653)
    ·
      refine ⟨67588848164713924292010995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180236928439237131445362653 67588848164713924292010995)
      ·
        refine ⟨101383272247070886438016493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67588848164713924292010995 101383272247070886438016493)
        ·
          refine ⟨38018727092651582414256185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101383272247070886438016493 38018727092651582414256185)
          ·
            refine ⟨28514045319488686810692139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38018727092651582414256185 28514045319488686810692139)
            ·
              refine ⟨42771067979233030216038209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28514045319488686810692139 42771067979233030216038209)
              ·
                refine ⟨32078300984424772662028657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42771067979233030216038209 32078300984424772662028657)
                ·
                  refine ⟨24058725738318579496521493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32078300984424772662028657 24058725738318579496521493)
                  ·
                    refine ⟨1127752768983683413899445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24058725738318579496521493 1127752768983683413899445)
                    ·
                      rfl

theorem cell23_6588872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_6588872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588872 prefixEnd_6588872 := by exact prefixLift 6588872
  have htrace : WordTrace (prefixWord ++ tailWord_6588872) baseStart_6588872 baseEnd_6588872 := by
    simpa [prefixWord, tailWord_6588872, baseEnd_6588872] using wordTrace_append hprefix tailTrace_6588872
  have hstable : (prefixWord ++ tailWord_6588872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588872).length < 2 ^ (prefixWord ++ tailWord_6588872).sum := by decide
  have hdescent : baseEnd_6588872 < baseStart_6588872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588992 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 8]
def baseStart_6588992 : Nat := 118140960795 + 6588992 * 2 ^ 59
def prefixEnd_6588992 : Nat := 4983230072969 + 3 ^ 40 * 6588992 * 2
def baseEnd_6588992 : Nat := 375924436069954419133087

theorem tailTrace_6588992 : CollatzResearch.WordTrace tailWord_6588992 prefixEnd_6588992 375924436069954419133087 := by
  unfold tailWord_6588992
  simp only [CollatzResearch.WordTrace]
  refine ⟨120160140672607384544092615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160213520896809846058790153 120160140672607384544092615)
  ·
    refine ⟨180240211008911076816138923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120160140672607384544092615 180240211008911076816138923)
    ·
      refine ⟨270360316513366615224208385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180240211008911076816138923 270360316513366615224208385)
      ·
        refine ⟨202770237385024961418156289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270360316513366615224208385 202770237385024961418156289)
        ·
          refine ⟨152077678038768721063617217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202770237385024961418156289 152077678038768721063617217)
          ·
            refine ⟨114058258529076540797712913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152077678038768721063617217 114058258529076540797712913)
            ·
              refine ⟨85543693896807405598284685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114058258529076540797712913 85543693896807405598284685)
              ·
                refine ⟨32078885211302777099356757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85543693896807405598284685 32078885211302777099356757)
                ·
                  refine ⟨375924436069954419133087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32078885211302777099356757 375924436069954419133087)
                  ·
                    rfl

theorem cell23_6588992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 8].length) (baseStart_6588992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6588992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6588992 prefixEnd_6588992 := by exact prefixLift 6588992
  have htrace : WordTrace (prefixWord ++ tailWord_6588992) baseStart_6588992 baseEnd_6588992 := by
    simpa [prefixWord, tailWord_6588992, baseEnd_6588992] using wordTrace_append hprefix tailTrace_6588992
  have hstable : (prefixWord ++ tailWord_6588992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588992).length < 2 ^ (prefixWord ++ tailWord_6588992).sum := by decide
  have hdescent : baseEnd_6588992 < baseStart_6588992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589009 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 6]
def baseStart_6589009 : Nat := 118140960795 + 6589009 * 2 ^ 59
def prefixEnd_6589009 : Nat := 4983230072969 + 3 ^ 40 * 6589009 * 2
def baseEnd_6589009 : Nat := 375925405977857356187245

theorem tailTrace_6589009 : CollatzResearch.WordTrace tailWord_6589009 prefixEnd_6589009 375925405977857356187245 := by
  unfold tailWord_6589009
  simp only [CollatzResearch.WordTrace]
  refine ⟨240320901386153180991554081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160213934257435453994369387 240320901386153180991554081)
  ·
    refine ⟨180240676039614885743665561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240320901386153180991554081 180240676039614885743665561)
    ·
      refine ⟨135180507029711164307749171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180240676039614885743665561 135180507029711164307749171)
      ·
        refine ⟨202770760544566746461623757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135180507029711164307749171 202770760544566746461623757)
        ·
          refine ⟨76039035204212529923108909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202770760544566746461623757 76039035204212529923108909)
          ·
            refine ⟨28514638201579698721165841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76039035204212529923108909 28514638201579698721165841)
            ·
              refine ⟨21385978651184774040874381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28514638201579698721165841 21385978651184774040874381)
              ·
                refine ⟨8019741994194290265327893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21385978651184774040874381 8019741994194290265327893)
                ·
                  refine ⟨375925405977857356187245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8019741994194290265327893 375925405977857356187245)
                  ·
                    rfl

theorem cell23_6589009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 6].length) (baseStart_6589009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589009 prefixEnd_6589009 := by exact prefixLift 6589009
  have htrace : WordTrace (prefixWord ++ tailWord_6589009) baseStart_6589009 baseEnd_6589009 := by
    simpa [prefixWord, tailWord_6589009, baseEnd_6589009] using wordTrace_append hprefix tailTrace_6589009
  have hstable : (prefixWord ++ tailWord_6589009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589009).length < 2 ^ (prefixWord ++ tailWord_6589009).sum := by decide
  have hdescent : baseEnd_6589009 < baseStart_6589009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589020 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_6589020 : Nat := 118140960795 + 6589020 * 2 ^ 59
def prefixEnd_6589020 : Nat := 4983230072969 + 3 ^ 40 * 6589020 * 2
def baseEnd_6589020 : Nat := 3383334302087915662647655

theorem tailTrace_6589020 : CollatzResearch.WordTrace tailWord_6589020 prefixEnd_6589020 3383334302087915662647655 := by
  unfold tailWord_6589020
  simp only [CollatzResearch.WordTrace]
  refine ⟨120160651294556664935102257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160214201726075553246803009 120160651294556664935102257)
  ·
    refine ⟨90120488470917498701326693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120160651294556664935102257 90120488470917498701326693)
    ·
      refine ⟨16897591588297031006498755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90120488470917498701326693 16897591588297031006498755)
      ·
        refine ⟨25346387382445546509748133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16897591588297031006498755 25346387382445546509748133)
        ·
          refine ⟨4752447634208539970577775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25346387382445546509748133 4752447634208539970577775)
          ·
            refine ⟨7128671451312809955866663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752447634208539970577775 7128671451312809955866663)
            ·
              refine ⟨10693007176969214933799995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128671451312809955866663 10693007176969214933799995)
              ·
                refine ⟨16039510765453822400699993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10693007176969214933799995 16039510765453822400699993)
                ·
                  refine ⟨12029633074090366800524995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16039510765453822400699993 12029633074090366800524995)
                  ·
                    refine ⟨18044449611135550200787493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12029633074090366800524995 18044449611135550200787493)
                    ·
                      refine ⟨3383334302087915662647655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18044449611135550200787493 3383334302087915662647655)
                      ·
                        rfl

theorem cell23_6589020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_6589020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589020 prefixEnd_6589020 := by exact prefixLift 6589020
  have htrace : WordTrace (prefixWord ++ tailWord_6589020) baseStart_6589020 baseEnd_6589020 := by
    simpa [prefixWord, tailWord_6589020, baseEnd_6589020] using wordTrace_append hprefix tailTrace_6589020
  have hstable : (prefixWord ++ tailWord_6589020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589020).length < 2 ^ (prefixWord ++ tailWord_6589020).sum := by decide
  have hdescent : baseEnd_6589020 < baseStart_6589020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589059 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 4]
def baseStart_6589059 : Nat := 118140960795 + 6589059 * 2 ^ 59
def prefixEnd_6589059 : Nat := 4983230072969 + 3 ^ 40 * 6589059 * 2
def baseEnd_6589059 : Nat := 3383354327833441010059975

theorem tailTrace_6589059 : CollatzResearch.WordTrace tailWord_6589059 prefixEnd_6589059 3383354327833441010059975 := by
  unfold tailWord_6589059
  simp only [CollatzResearch.WordTrace]
  refine ⟨240322725035972039530874231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160215150023981359687249487 240322725035972039530874231)
  ·
    refine ⟨360484087553958059296311347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240322725035972039530874231 360484087553958059296311347)
    ·
      refine ⟨540726131330937088944467021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360484087553958059296311347 540726131330937088944467021)
      ·
        refine ⟨202772299249101408354175133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540726131330937088944467021 202772299249101408354175133)
        ·
          refine ⟨76039612218413028132815675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202772299249101408354175133 76039612218413028132815675)
          ·
            refine ⟨114059418327619542199223513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76039612218413028132815675 114059418327619542199223513)
            ·
              refine ⟨85544563745714656649417635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114059418327619542199223513 85544563745714656649417635)
              ·
                refine ⟨128316845618571984974126453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85544563745714656649417635 128316845618571984974126453)
                ·
                  refine ⟨12029704276741123591324355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128316845618571984974126453 12029704276741123591324355)
                  ·
                    refine ⟨18044556415111685386986533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12029704276741123591324355 18044556415111685386986533)
                    ·
                      refine ⟨3383354327833441010059975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18044556415111685386986533 3383354327833441010059975)
                      ·
                        rfl

theorem cell23_6589059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_6589059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589059 prefixEnd_6589059 := by exact prefixLift 6589059
  have htrace : WordTrace (prefixWord ++ tailWord_6589059) baseStart_6589059 baseEnd_6589059 := by
    simpa [prefixWord, tailWord_6589059, baseEnd_6589059] using wordTrace_append hprefix tailTrace_6589059
  have hstable : (prefixWord ++ tailWord_6589059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589059).length < 2 ^ (prefixWord ++ tailWord_6589059).sum := by decide
  have hdescent : baseEnd_6589059 < baseStart_6589059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589079 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_6589079 : Nat := 118140960795 + 6589079 * 2 ^ 59
def prefixEnd_6589079 : Nat := 4983230072969 + 3 ^ 40 * 6589079 * 2
def baseEnd_6589079 : Nat := 3383364597446530931809883

theorem tailTrace_6589079 : CollatzResearch.WordTrace tailWord_6589079 prefixEnd_6589079 3383364597446530931809883 := by
  unfold tailWord_6589079
  simp only [CollatzResearch.WordTrace]
  refine ⟨240323454495899582946602291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160215636330599721964401527 240323454495899582946602291)
  ·
    refine ⟨360485181743849374419903437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240323454495899582946602291 360485181743849374419903437)
    ·
      refine ⟨135181943153943515407463789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360485181743849374419903437 135181943153943515407463789)
      ·
        refine ⟨50693228682728818277798921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135181943153943515407463789 50693228682728818277798921)
        ·
          refine ⟨38019921512046613708349191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50693228682728818277798921 38019921512046613708349191)
          ·
            refine ⟨57029882268069920562523787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38019921512046613708349191 57029882268069920562523787)
            ·
              refine ⟨85544823402104880843785681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57029882268069920562523787 85544823402104880843785681)
              ·
                refine ⟨64158617551578660632839261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85544823402104880843785681 64158617551578660632839261)
                ·
                  refine ⟨24059481581841997737314723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64158617551578660632839261 24059481581841997737314723)
                  ·
                    refine ⟨36089222372762996605972085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24059481581841997737314723 36089222372762996605972085)
                    ·
                      refine ⟨3383364597446530931809883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36089222372762996605972085 3383364597446530931809883)
                      ·
                        rfl

theorem cell23_6589079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_6589079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589079 prefixEnd_6589079 := by exact prefixLift 6589079
  have htrace : WordTrace (prefixWord ++ tailWord_6589079) baseStart_6589079 baseEnd_6589079 := by
    simpa [prefixWord, tailWord_6589079, baseEnd_6589079] using wordTrace_append hprefix tailTrace_6589079
  have hstable : (prefixWord ++ tailWord_6589079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589079).length < 2 ^ (prefixWord ++ tailWord_6589079).sum := by decide
  have hdescent : baseEnd_6589079 < baseStart_6589079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589086 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_6589086 : Nat := 118140960795 + 6589086 * 2 ^ 59
def prefixEnd_6589086 : Nat := 4983230072969 + 3 ^ 40 * 6589086 * 2
def baseEnd_6589086 : Nat := 1127789397270370801474117

theorem tailTrace_6589086 : CollatzResearch.WordTrace tailWord_6589086 prefixEnd_6589086 1127789397270370801474117 := by
  unfold tailWord_6589086
  simp only [CollatzResearch.WordTrace]
  refine ⟨30040463725859277892763389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160215806537916148761404741 30040463725859277892763389)
  ·
    refine ⟨11265173897197229209786271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30040463725859277892763389 11265173897197229209786271)
    ·
      refine ⟨16897760845795843814679407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11265173897197229209786271 16897760845795843814679407)
      ·
        refine ⟨25346641268693765722019111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16897760845795843814679407 25346641268693765722019111)
        ·
          refine ⟨38019961903040648583028667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25346641268693765722019111 38019961903040648583028667)
          ·
            refine ⟨57029942854560972874543001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38019961903040648583028667 57029942854560972874543001)
            ·
              refine ⟨42772457140920729655907251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57029942854560972874543001 42772457140920729655907251)
              ·
                refine ⟨64158685711381094483860877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42772457140920729655907251 64158685711381094483860877)
                ·
                  refine ⟨24059507141767910431447829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64158685711381094483860877 24059507141767910431447829)
                  ·
                    refine ⟨1127789397270370801474117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24059507141767910431447829 1127789397270370801474117)
                    ·
                      rfl

theorem cell23_6589086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_6589086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589086 prefixEnd_6589086 := by exact prefixLift 6589086
  have htrace : WordTrace (prefixWord ++ tailWord_6589086) baseStart_6589086 baseEnd_6589086 := by
    simpa [prefixWord, tailWord_6589086, baseEnd_6589086] using wordTrace_append hprefix tailTrace_6589086
  have hstable : (prefixWord ++ tailWord_6589086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589086).length < 2 ^ (prefixWord ++ tailWord_6589086).sum := by decide
  have hdescent : baseEnd_6589086 < baseStart_6589086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589120 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 2, 4]
def baseStart_6589120 : Nat := 118140960795 + 6589120 * 2 ^ 59
def prefixEnd_6589120 : Nat := 4983230072969 + 3 ^ 40 * 6589120 * 2
def baseEnd_6589120 : Nat := 1127795216717788423799065

theorem tailTrace_6589120 : CollatzResearch.WordTrace tailWord_6589120 prefixEnd_6589120 1127795216717788423799065 := by
  unfold tailWord_6589120
  simp only [CollatzResearch.WordTrace]
  refine ⟨120162474944375523474422407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160216633259167364632563209 120162474944375523474422407)
  ·
    refine ⟨180243712416563285211633611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120162474944375523474422407 180243712416563285211633611)
    ·
      refine ⟨270365568624844927817450417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180243712416563285211633611 270365568624844927817450417)
      ·
        refine ⟨202774176468633695863087813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270365568624844927817450417 202774176468633695863087813)
        ·
          refine ⟨38020158087868817974328965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202774176468633695863087813 38020158087868817974328965)
          ·
            refine ⟨7128779641475403370186681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38020158087868817974328965 7128779641475403370186681)
            ·
              refine ⟨5346584731106552527640011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7128779641475403370186681 5346584731106552527640011)
              ·
                refine ⟨8019877096659828791460017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5346584731106552527640011 8019877096659828791460017)
                ·
                  refine ⟨6014907822494871593595013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8019877096659828791460017 6014907822494871593595013)
                  ·
                    refine ⟨1127795216717788423799065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6014907822494871593595013 1127795216717788423799065)
                    ·
                      rfl

theorem cell23_6589120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 4].length) (baseStart_6589120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589120 prefixEnd_6589120 := by exact prefixLift 6589120
  have htrace : WordTrace (prefixWord ++ tailWord_6589120) baseStart_6589120 baseEnd_6589120 := by
    simpa [prefixWord, tailWord_6589120, baseEnd_6589120] using wordTrace_append hprefix tailTrace_6589120
  have hstable : (prefixWord ++ tailWord_6589120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589120).length < 2 ^ (prefixWord ++ tailWord_6589120).sum := by decide
  have hdescent : baseEnd_6589120 < baseStart_6589120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589130 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_6589130 : Nat := 118140960795 + 6589130 * 2 ^ 59
def prefixEnd_6589130 : Nat := 4983230072969 + 3 ^ 40 * 6589130 * 2
def baseEnd_6589130 : Nat := 3383390784959910232272149

theorem tailTrace_6589130 : CollatzResearch.WordTrace tailWord_6589130 prefixEnd_6589130 3383390784959910232272149 := by
  unfold tailWord_6589130
  simp only [CollatzResearch.WordTrace]
  refine ⟨60081328654678704664177211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160216876412476545771139229 60081328654678704664177211)
  ·
    refine ⟨90121992982018056996265817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60081328654678704664177211 90121992982018056996265817)
    ·
      refine ⟨67591494736513542747199363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90121992982018056996265817 67591494736513542747199363)
      ·
        refine ⟨101387242104770314120799045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67591494736513542747199363 101387242104770314120799045)
        ·
          refine ⟨19010107894644433897649821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101387242104770314120799045 19010107894644433897649821)
          ·
            refine ⟨7128790460491662711618683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19010107894644433897649821 7128790460491662711618683)
            ·
              refine ⟨10693185690737494067428025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128790460491662711618683 10693185690737494067428025)
              ·
                refine ⟨8019889268053120550571019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10693185690737494067428025 8019889268053120550571019)
                ·
                  refine ⟨12029833902079680825856529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8019889268053120550571019 12029833902079680825856529)
                  ·
                    refine ⟨9022375426559760619392397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12029833902079680825856529 9022375426559760619392397)
                    ·
                      refine ⟨3383390784959910232272149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9022375426559760619392397 3383390784959910232272149)
                      ·
                        rfl

theorem cell23_6589130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_6589130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589130 prefixEnd_6589130 := by exact prefixLift 6589130
  have htrace : WordTrace (prefixWord ++ tailWord_6589130) baseStart_6589130 baseEnd_6589130 := by
    simpa [prefixWord, tailWord_6589130, baseEnd_6589130] using wordTrace_append hprefix tailTrace_6589130
  have hstable : (prefixWord ++ tailWord_6589130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589130).length < 2 ^ (prefixWord ++ tailWord_6589130).sum := by decide
  have hdescent : baseEnd_6589130 < baseStart_6589130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589166 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_6589166 : Nat := 118140960795 + 6589166 * 2 ^ 59
def prefixEnd_6589166 : Nat := 4983230072969 + 3 ^ 40 * 6589166 * 2
def baseEnd_6589166 : Nat := 3383409270263472091421983

theorem tailTrace_6589166 : CollatzResearch.WordTrace tailWord_6589166 prefixEnd_6589166 3383409270263472091421983 := by
  unfold tailWord_6589166
  simp only [CollatzResearch.WordTrace]
  refine ⟨30040828455823049600627419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160217751764389597870012901 30040828455823049600627419)
  ·
    refine ⟨45061242683734574400941129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30040828455823049600627419 45061242683734574400941129)
    ·
      refine ⟨33795932012800930800705847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45061242683734574400941129 33795932012800930800705847)
      ·
        refine ⟨50693898019201396201058771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33795932012800930800705847 50693898019201396201058771)
        ·
          refine ⟨76040847028802094301588157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50693898019201396201058771 76040847028802094301588157)
          ·
            refine ⟨28515317635800785363095559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76040847028802094301588157 28515317635800785363095559)
            ·
              refine ⟨42772976453701178044643339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28515317635800785363095559 42772976453701178044643339)
              ·
                refine ⟨64159464680551767066965009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42772976453701178044643339 64159464680551767066965009)
                ·
                  refine ⟨48119598510413825300223757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64159464680551767066965009 48119598510413825300223757)
                  ·
                    refine ⟨18044849441405184487583909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48119598510413825300223757 18044849441405184487583909)
                    ·
                      refine ⟨3383409270263472091421983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18044849441405184487583909 3383409270263472091421983)
                      ·
                        rfl

theorem cell23_6589166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_6589166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589166 prefixEnd_6589166 := by exact prefixLift 6589166
  have htrace : WordTrace (prefixWord ++ tailWord_6589166) baseStart_6589166 baseEnd_6589166 := by
    simpa [prefixWord, tailWord_6589166, baseEnd_6589166] using wordTrace_append hprefix tailTrace_6589166
  have hstable : (prefixWord ++ tailWord_6589166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589166).length < 2 ^ (prefixWord ++ tailWord_6589166).sum := by decide
  have hdescent : baseEnd_6589166 < baseStart_6589166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589183 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 6, 2, 2]
def baseStart_6589183 : Nat := 118140960795 + 6589183 * 2 ^ 59
def prefixEnd_6589183 : Nat := 4983230072969 + 3 ^ 40 * 6589183 * 2
def baseEnd_6589183 : Nat := 3383417999434598524909405

theorem tailTrace_6589183 : CollatzResearch.WordTrace tailWord_6589183 prefixEnd_6589183 3383417999434598524909405 := by
  unfold tailWord_6589183
  simp only [CollatzResearch.WordTrace]
  refine ⟨240327247687522808708388203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160218165125015205805592135 240327247687522808708388203)
  ·
    refine ⟨360490871531284213062582305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240327247687522808708388203 360490871531284213062582305)
    ·
      refine ⟨270368153648463159796936729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360490871531284213062582305 270368153648463159796936729)
      ·
        refine ⟨202776115236347369847702547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270368153648463159796936729 202776115236347369847702547)
        ·
          refine ⟨304164172854521054771553821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202776115236347369847702547 304164172854521054771553821)
          ·
            refine ⟨114061564820445395539332683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304164172854521054771553821 114061564820445395539332683)
            ·
              refine ⟨171092347230668093308999025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114061564820445395539332683 171092347230668093308999025)
              ·
                refine ⟨128319260423001069981749269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171092347230668093308999025 128319260423001069981749269)
                ·
                  refine ⟨6014965332328175155394497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128319260423001069981749269 6014965332328175155394497)
                  ·
                    refine ⟨4511223999246131366545873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6014965332328175155394497 4511223999246131366545873)
                    ·
                      refine ⟨3383417999434598524909405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511223999246131366545873 3383417999434598524909405)
                      ·
                        rfl

theorem cell23_6589183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_6589183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589183 prefixEnd_6589183 := by exact prefixLift 6589183
  have htrace : WordTrace (prefixWord ++ tailWord_6589183) baseStart_6589183 baseEnd_6589183 := by
    simpa [prefixWord, tailWord_6589183, baseEnd_6589183] using wordTrace_append hprefix tailTrace_6589183
  have hstable : (prefixWord ++ tailWord_6589183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589183).length < 2 ^ (prefixWord ++ tailWord_6589183).sum := by decide
  have hdescent : baseEnd_6589183 < baseStart_6589183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589256 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_6589256 : Nat := 118140960795 + 6589256 * 2 ^ 59
def prefixEnd_6589256 : Nat := 4983230072969 + 3 ^ 40 * 6589256 * 2
def baseEnd_6589256 : Nat := 3383455483522376739296569

theorem tailTrace_6589256 : CollatzResearch.WordTrace tailWord_6589256 prefixEnd_6589256 3383455483522376739296569 := by
  unfold tailWord_6589256
  simp only [CollatzResearch.WordTrace]
  refine ⟨120164955108129171087897811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160219940144172228117197081 120164955108129171087897811)
  ·
    refine ⟨180247432662193756631846717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120164955108129171087897811 180247432662193756631846717)
    ·
      refine ⟨67592787248322658736942519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180247432662193756631846717 67592787248322658736942519)
      ·
        refine ⟨101389180872483988105413779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67592787248322658736942519 101389180872483988105413779)
        ·
          refine ⟨152083771308725982158120669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101389180872483988105413779 152083771308725982158120669)
          ·
            refine ⟨57031414240772243309295251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152083771308725982158120669 57031414240772243309295251)
            ·
              refine ⟨85547121361158364963942877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57031414240772243309295251 85547121361158364963942877)
              ·
                refine ⟨32080170510434386861478579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85547121361158364963942877 32080170510434386861478579)
                ·
                  refine ⟨48120255765651580292217869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32080170510434386861478579 48120255765651580292217869)
                  ·
                    refine ⟨18045095912119342609581701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48120255765651580292217869 18045095912119342609581701)
                    ·
                      refine ⟨3383455483522376739296569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18045095912119342609581701 3383455483522376739296569)
                      ·
                        rfl

theorem cell23_6589256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_6589256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589256 prefixEnd_6589256 := by exact prefixLift 6589256
  have htrace : WordTrace (prefixWord ++ tailWord_6589256) baseStart_6589256 baseEnd_6589256 := by
    simpa [prefixWord, tailWord_6589256, baseEnd_6589256] using wordTrace_append hprefix tailTrace_6589256
  have hstable : (prefixWord ++ tailWord_6589256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589256).length < 2 ^ (prefixWord ++ tailWord_6589256).sum := by decide
  have hdescent : baseEnd_6589256 < baseStart_6589256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589273 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_6589273 : Nat := 118140960795 + 6589273 * 2 ^ 59
def prefixEnd_6589273 : Nat := 4983230072969 + 3 ^ 40 * 6589273 * 2
def baseEnd_6589273 : Nat := 3383464212693503172783991

theorem tailTrace_6589273 : CollatzResearch.WordTrace tailWord_6589273 prefixEnd_6589273 3383464212693503172783991 := by
  unfold tailWord_6589273
  simp only [CollatzResearch.WordTrace]
  refine ⟨240330530257196754079164473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160220353504797836052776315 240330530257196754079164473)
  ·
    refine ⟨180247897692897565559373355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240330530257196754079164473 180247897692897565559373355)
    ·
      refine ⟨270371846539346348339060033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180247897692897565559373355 270371846539346348339060033)
      ·
        refine ⟨202778884904509761254295025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270371846539346348339060033 202778884904509761254295025)
        ·
          refine ⟨152084163678382320940721269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202778884904509761254295025 152084163678382320940721269)
          ·
            refine ⟨14257890344848342588192619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152084163678382320940721269 14257890344848342588192619)
            ·
              refine ⟨21386835517272513882288929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14257890344848342588192619 21386835517272513882288929)
              ·
                refine ⟨16040126637954385411716697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21386835517272513882288929 16040126637954385411716697)
                ·
                  refine ⟨12030094978465789058787523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16040126637954385411716697 12030094978465789058787523)
                  ·
                    refine ⟨18045142467698683588181285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12030094978465789058787523 18045142467698683588181285)
                    ·
                      refine ⟨3383464212693503172783991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18045142467698683588181285 3383464212693503172783991)
                      ·
                        rfl

theorem cell23_6589273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_6589273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589273 prefixEnd_6589273 := by exact prefixLift 6589273
  have htrace : WordTrace (prefixWord ++ tailWord_6589273) baseStart_6589273 baseEnd_6589273 := by
    simpa [prefixWord, tailWord_6589273, baseEnd_6589273] using wordTrace_append hprefix tailTrace_6589273
  have hstable : (prefixWord ++ tailWord_6589273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589273).length < 2 ^ (prefixWord ++ tailWord_6589273).sum := by decide
  have hdescent : baseEnd_6589273 < baseStart_6589273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589293 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_6589293 : Nat := 118140960795 + 6589293 * 2 ^ 59
def prefixEnd_6589293 : Nat := 4983230072969 + 3 ^ 40 * 6589293 * 2
def baseEnd_6589293 : Nat := 3383474482306593094533899

theorem tailTrace_6589293 : CollatzResearch.WordTrace tailWord_6589293 prefixEnd_6589293 3383474482306593094533899 := by
  unfold tailWord_6589293
  simp only [CollatzResearch.WordTrace]
  refine ⟨240331259717124297494892533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160220839811416198329928355 240331259717124297494892533)
  ·
    refine ⟨22531055598480402890146175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240331259717124297494892533 22531055598480402890146175)
    ·
      refine ⟨33796583397720604335219263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22531055598480402890146175 33796583397720604335219263)
      ·
        refine ⟨50694875096580906502828895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33796583397720604335219263 50694875096580906502828895)
        ·
          refine ⟨76042312644871359754243343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50694875096580906502828895 76042312644871359754243343)
          ·
            refine ⟨114063468967307039631365015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76042312644871359754243343 114063468967307039631365015)
            ·
              refine ⟨171095203450960559447047523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114063468967307039631365015 171095203450960559447047523)
              ·
                refine ⟨256642805176440839170571285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171095203450960559447047523 256642805176440839170571285)
                ·
                  refine ⟨12030131492645664336120529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256642805176440839170571285 12030131492645664336120529)
                  ·
                    refine ⟨9022598619484248252090397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12030131492645664336120529 9022598619484248252090397)
                    ·
                      refine ⟨3383474482306593094533899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9022598619484248252090397 3383474482306593094533899)
                      ·
                        rfl

theorem cell23_6589293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_6589293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589293 prefixEnd_6589293 := by exact prefixLift 6589293
  have htrace : WordTrace (prefixWord ++ tailWord_6589293) baseStart_6589293 baseEnd_6589293 := by
    simpa [prefixWord, tailWord_6589293, baseEnd_6589293] using wordTrace_append hprefix tailTrace_6589293
  have hstable : (prefixWord ++ tailWord_6589293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589293).length < 2 ^ (prefixWord ++ tailWord_6589293).sum := by decide
  have hdescent : baseEnd_6589293 < baseStart_6589293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589316 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_6589316 : Nat := 118140960795 + 6589316 * 2 ^ 59
def prefixEnd_6589316 : Nat := 4983230072969 + 3 ^ 40 * 6589316 * 2
def baseEnd_6589316 : Nat := 3383486292361646504546293

theorem tailTrace_6589316 : CollatzResearch.WordTrace tailWord_6589316 prefixEnd_6589316 3383486292361646504546293 := by
  unfold tailWord_6589316
  simp only [CollatzResearch.WordTrace]
  refine ⟨120166049298020486211489901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160221399064027314948653201 120166049298020486211489901)
  ·
    refine ⟨45062268486757682329308713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120166049298020486211489901 45062268486757682329308713)
    ·
      refine ⟨33796701365068261746981535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45062268486757682329308713 33796701365068261746981535)
      ·
        refine ⟨50695052047602392620472303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33796701365068261746981535 50695052047602392620472303)
        ·
          refine ⟨76042578071403588930708455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50695052047602392620472303 76042578071403588930708455)
          ·
            refine ⟨114063867107105383396062683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76042578071403588930708455 114063867107105383396062683)
            ·
              refine ⟨171095800660658075094094025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114063867107105383396062683 171095800660658075094094025)
              ·
                refine ⟨128321850495493556320570519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171095800660658075094094025 128321850495493556320570519)
                ·
                  refine ⟨192482775743240334480855779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128321850495493556320570519 192482775743240334480855779)
                  ·
                    refine ⟨288724163614860501721283669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192482775743240334480855779 288724163614860501721283669)
                    ·
                      refine ⟨3383486292361646504546293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 288724163614860501721283669 3383486292361646504546293)
                      ·
                        rfl

theorem cell23_6589316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_6589316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589316 prefixEnd_6589316 := by exact prefixLift 6589316
  have htrace : WordTrace (prefixWord ++ tailWord_6589316) baseStart_6589316 baseEnd_6589316 := by
    simpa [prefixWord, tailWord_6589316, baseEnd_6589316] using wordTrace_append hprefix tailTrace_6589316
  have hstable : (prefixWord ++ tailWord_6589316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589316).length < 2 ^ (prefixWord ++ tailWord_6589316).sum := by decide
  have hdescent : baseEnd_6589316 < baseStart_6589316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589343 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 3, 5]
def baseStart_6589343 : Nat := 118140960795 + 6589343 * 2 ^ 59
def prefixEnd_6589343 : Nat := 4983230072969 + 3 ^ 40 * 6589343 * 2
def baseEnd_6589343 : Nat := 1127833385446439299636223

theorem tailTrace_6589343 : CollatzResearch.WordTrace tailWord_6589343 prefixEnd_6589343 1127833385446439299636223 := by
  unfold tailWord_6589343
  simp only [CollatzResearch.WordTrace]
  refine ⟨240333083366943156034212683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160222055577962104022808455 240333083366943156034212683)
  ·
    refine ⟨360499625050414734051319025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240333083366943156034212683 360499625050414734051319025)
    ·
      refine ⟨270374718787811050538489269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360499625050414734051319025 270374718787811050538489269)
      ·
        refine ⟨25347629886357285987983369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270374718787811050538489269 25347629886357285987983369)
        ·
          refine ⟨19010722414767964490987527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25347629886357285987983369 19010722414767964490987527)
          ·
            refine ⟨28516083622151946736481291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19010722414767964490987527 28516083622151946736481291)
            ·
              refine ⟨42774125433227920104721937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28516083622151946736481291 42774125433227920104721937)
              ·
                refine ⟨32080594074920940078541453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42774125433227920104721937 32080594074920940078541453)
                ·
                  refine ⟨12030222778095352529453045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32080594074920940078541453 12030222778095352529453045)
                  ·
                    refine ⟨1127833385446439299636223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12030222778095352529453045 1127833385446439299636223)
                    ·
                      rfl

theorem cell23_6589343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_6589343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589343 prefixEnd_6589343 := by exact prefixLift 6589343
  have htrace : WordTrace (prefixWord ++ tailWord_6589343) baseStart_6589343 baseEnd_6589343 := by
    simpa [prefixWord, tailWord_6589343, baseEnd_6589343] using wordTrace_append hprefix tailTrace_6589343
  have hstable : (prefixWord ++ tailWord_6589343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589343).length < 2 ^ (prefixWord ++ tailWord_6589343).sum := by decide
  have hdescent : baseEnd_6589343 < baseStart_6589343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589356 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_6589356 : Nat := 118140960795 + 6589356 * 2 ^ 59
def prefixEnd_6589356 : Nat := 4983230072969 + 3 ^ 40 * 6589356 * 2
def baseEnd_6589356 : Nat := 1127835610529275449348703

theorem tailTrace_6589356 : CollatzResearch.WordTrace tailWord_6589356 prefixEnd_6589356 1127835610529275449348703 := by
  unfold tailWord_6589356
  simp only [CollatzResearch.WordTrace]
  refine ⟨120166778757948029627217961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160222371677264039502957281 120166778757948029627217961)
  ·
    refine ⟨90125084068461022220413471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120166778757948029627217961 90125084068461022220413471)
    ·
      refine ⟨135187626102691533330620207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90125084068461022220413471 135187626102691533330620207)
      ·
        refine ⟨202781439154037299995930311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135187626102691533330620207 202781439154037299995930311)
        ·
          refine ⟨304172158731055949993895467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202781439154037299995930311 304172158731055949993895467)
          ·
            refine ⟨456258238096583924990843201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304172158731055949993895467 456258238096583924990843201)
            ·
              refine ⟨342193678572437943743132401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456258238096583924990843201 342193678572437943743132401)
              ·
                refine ⟨256645258929328457807349301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342193678572437943743132401 256645258929328457807349301)
                ·
                  refine ⟨24060493024624542919438997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256645258929328457807349301 24060493024624542919438997)
                  ·
                    refine ⟨1127835610529275449348703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24060493024624542919438997 1127835610529275449348703)
                    ·
                      rfl

theorem cell23_6589356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_6589356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589356 prefixEnd_6589356 := by exact prefixLift 6589356
  have htrace : WordTrace (prefixWord ++ tailWord_6589356) baseStart_6589356 baseEnd_6589356 := by
    simpa [prefixWord, tailWord_6589356, baseEnd_6589356] using wordTrace_append hprefix tailTrace_6589356
  have hstable : (prefixWord ++ tailWord_6589356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589356).length < 2 ^ (prefixWord ++ tailWord_6589356).sum := by decide
  have hdescent : baseEnd_6589356 < baseStart_6589356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589363 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 8, 2]
def baseStart_6589363 : Nat := 118140960795 + 6589363 * 2 ^ 59
def prefixEnd_6589363 : Nat := 4983230072969 + 3 ^ 40 * 6589363 * 2
def baseEnd_6589363 : Nat := 3383510425952407820658577

theorem tailTrace_6589363 : CollatzResearch.WordTrace tailWord_6589363 prefixEnd_6589363 3383510425952407820658577 := by
  unfold tailWord_6589363
  simp only [CollatzResearch.WordTrace]
  refine ⟨240333812826870699449940743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160222541884580466299960495 240333812826870699449940743)
  ·
    refine ⟨360500719240306049174911115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240333812826870699449940743 360500719240306049174911115)
    ·
      refine ⟨540751078860459073762366673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360500719240306049174911115 540751078860459073762366673)
      ·
        refine ⟨405563309145344305321775005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540751078860459073762366673 405563309145344305321775005)
        ·
          refine ⟨152086240929504114495665627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405563309145344305321775005 152086240929504114495665627)
          ·
            refine ⟨228129361394256171743498441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152086240929504114495665627 228129361394256171743498441)
            ·
              refine ⟨171097021045692128807623831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228129361394256171743498441 171097021045692128807623831)
              ·
                refine ⟨256645531568538193211435747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171097021045692128807623831 256645531568538193211435747)
                ·
                  refine ⟨384968297352807289817153621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256645531568538193211435747 384968297352807289817153621)
                  ·
                    refine ⟨4511347234603210427544769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 384968297352807289817153621 4511347234603210427544769)
                    ·
                      refine ⟨3383510425952407820658577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511347234603210427544769 3383510425952407820658577)
                      ·
                        rfl

theorem cell23_6589363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 8, 2].length) (baseStart_6589363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589363 prefixEnd_6589363 := by exact prefixLift 6589363
  have htrace : WordTrace (prefixWord ++ tailWord_6589363) baseStart_6589363 baseEnd_6589363 := by
    simpa [prefixWord, tailWord_6589363, baseEnd_6589363] using wordTrace_append hprefix tailTrace_6589363
  have hstable : (prefixWord ++ tailWord_6589363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589363).length < 2 ^ (prefixWord ++ tailWord_6589363).sum := by decide
  have hdescent : baseEnd_6589363 < baseStart_6589363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589374 : List Nat := [4, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_6589374 : Nat := 118140960795 + 6589374 * 2 ^ 59
def prefixEnd_6589374 : Nat := 4983230072969 + 3 ^ 40 * 6589374 * 2
def baseEnd_6589374 : Nat := 3383516074239607277621027

theorem tailTrace_6589374 : CollatzResearch.WordTrace tailWord_6589374 prefixEnd_6589374 3383516074239607277621027 := by
  unfold tailWord_6589374
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041776753728856041073897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160222809353220565552394117 30041776753728856041073897)
  ·
    refine ⟨22531332565296642030805423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30041776753728856041073897 22531332565296642030805423)
    ·
      refine ⟨33796998847944963046208135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22531332565296642030805423 33796998847944963046208135)
      ·
        refine ⟨50695498271917444569312203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33796998847944963046208135 50695498271917444569312203)
        ·
          refine ⟨76043247407876166853968305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50695498271917444569312203 76043247407876166853968305)
          ·
            refine ⟨57032435555907125140476229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76043247407876166853968305 57032435555907125140476229)
            ·
              refine ⟨10693581666732585963839293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57032435555907125140476229 10693581666732585963839293)
              ·
                refine ⟨4010093125024719736439735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10693581666732585963839293 4010093125024719736439735)
                ·
                  refine ⟨6015139687537079604659603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010093125024719736439735 6015139687537079604659603)
                  ·
                    refine ⟨9022709531305619406989405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6015139687537079604659603 9022709531305619406989405)
                    ·
                      refine ⟨3383516074239607277621027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9022709531305619406989405 3383516074239607277621027)
                      ·
                        rfl

theorem cell23_6589374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_6589374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589374 prefixEnd_6589374 := by exact prefixLift 6589374
  have htrace : WordTrace (prefixWord ++ tailWord_6589374) baseStart_6589374 baseEnd_6589374 := by
    simpa [prefixWord, tailWord_6589374, baseEnd_6589374] using wordTrace_append hprefix tailTrace_6589374
  have hstable : (prefixWord ++ tailWord_6589374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589374).length < 2 ^ (prefixWord ++ tailWord_6589374).sum := by decide
  have hdescent : baseEnd_6589374 < baseStart_6589374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589390 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_6589390 : Nat := 118140960795 + 6589390 * 2 ^ 59
def prefixEnd_6589390 : Nat := 4983230072969 + 3 ^ 40 * 6589390 * 2
def baseEnd_6589390 : Nat := 1127841429976693071673651

theorem tailTrace_6589390 : CollatzResearch.WordTrace tailWord_6589390 prefixEnd_6589390 1127841429976693071673651 := by
  unfold tailWord_6589390
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041849699721610382646703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160223198398515255374115749 30041849699721610382646703)
  ·
    refine ⟨45062774549582415573970055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30041849699721610382646703 45062774549582415573970055)
    ·
      refine ⟨67594161824373623360955083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45062774549582415573970055 67594161824373623360955083)
      ·
        refine ⟨101391242736560435041432625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67594161824373623360955083 101391242736560435041432625)
        ·
          refine ⟨76043432052420326281074469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101391242736560435041432625 76043432052420326281074469)
          ·
            refine ⟨14258143509828811177701463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76043432052420326281074469 14258143509828811177701463)
            ·
              refine ⟨21387215264743216766552195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14258143509828811177701463 21387215264743216766552195)
              ·
                refine ⟨32080822897114825149828293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21387215264743216766552195 32080822897114825149828293)
                ·
                  refine ⟨6015154293209029715592805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32080822897114825149828293 6015154293209029715592805)
                  ·
                    refine ⟨1127841429976693071673651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015154293209029715592805 1127841429976693071673651)
                    ·
                      rfl

theorem cell23_6589390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_6589390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589390 prefixEnd_6589390 := by exact prefixLift 6589390
  have htrace : WordTrace (prefixWord ++ tailWord_6589390) baseStart_6589390 baseEnd_6589390 := by
    simpa [prefixWord, tailWord_6589390, baseEnd_6589390] using wordTrace_append hprefix tailTrace_6589390
  have hstable : (prefixWord ++ tailWord_6589390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589390).length < 2 ^ (prefixWord ++ tailWord_6589390).sum := by decide
  have hdescent : baseEnd_6589390 < baseStart_6589390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589407 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 1, 6]
def baseStart_6589407 : Nat := 118140960795 + 6589407 * 2 ^ 59
def prefixEnd_6589407 : Nat := 4983230072969 + 3 ^ 40 * 6589407 * 2
def baseEnd_6589407 : Nat := 1127844339700401882836125

theorem tailTrace_6589407 : CollatzResearch.WordTrace tailWord_6589407 prefixEnd_6589407 1127844339700401882836125 := by
  unfold tailWord_6589407
  simp only [CollatzResearch.WordTrace]
  refine ⟨240335417638711294964542475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160223611759140863309694983 240335417638711294964542475)
  ·
    refine ⟨360503126458066942446813713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240335417638711294964542475 360503126458066942446813713)
    ·
      refine ⟨270377344843550206835110285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360503126458066942446813713 270377344843550206835110285)
      ·
        refine ⟨101391504316331327563166357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270377344843550206835110285 101391504316331327563166357)
        ·
          refine ⟨4752726764828030979523423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101391504316331327563166357 4752726764828030979523423)
          ·
            refine ⟨7129090147242046469285135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752726764828030979523423 7129090147242046469285135)
            ·
              refine ⟨10693635220863069703927703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129090147242046469285135 10693635220863069703927703)
              ·
                refine ⟨16040452831294604555891555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10693635220863069703927703 16040452831294604555891555)
                ·
                  refine ⟨24060679246941906833837333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16040452831294604555891555 24060679246941906833837333)
                  ·
                    refine ⟨1127844339700401882836125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24060679246941906833837333 1127844339700401882836125)
                    ·
                      rfl

theorem cell23_6589407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 6].length) (baseStart_6589407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589407 prefixEnd_6589407 := by exact prefixLift 6589407
  have htrace : WordTrace (prefixWord ++ tailWord_6589407) baseStart_6589407 baseEnd_6589407 := by
    simpa [prefixWord, tailWord_6589407, baseEnd_6589407] using wordTrace_append hprefix tailTrace_6589407
  have hstable : (prefixWord ++ tailWord_6589407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589407).length < 2 ^ (prefixWord ++ tailWord_6589407).sum := by decide
  have hdescent : baseEnd_6589407 < baseStart_6589407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589447 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_6589447 : Nat := 118140960795 + 6589447 * 2 ^ 59
def prefixEnd_6589447 : Nat := 4983230072969 + 3 ^ 40 * 6589447 * 2
def baseEnd_6589447 : Nat := 3383553558327385492008191

theorem tailTrace_6589447 : CollatzResearch.WordTrace tailWord_6589447 prefixEnd_6589447 3383553558327385492008191 := by
  unfold tailWord_6589447
  simp only [CollatzResearch.WordTrace]
  refine ⟨240336876558566381795998595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160224584372377587863999063 240336876558566381795998595)
  ·
    refine ⟨360505314837849572693997893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240336876558566381795998595 360505314837849572693997893)
    ·
      refine ⟨67594746532096794880124605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360505314837849572693997893 67594746532096794880124605)
      ·
        refine ⟨25348029949536298080046727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67594746532096794880124605 25348029949536298080046727)
        ·
          refine ⟨38022044924304447120070091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25348029949536298080046727 38022044924304447120070091)
          ·
            refine ⟨57033067386456670680105137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38022044924304447120070091 57033067386456670680105137)
            ·
              refine ⟨42774800539842503010078853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57033067386456670680105137 42774800539842503010078853)
              ·
                refine ⟨8020275101220469314389785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42774800539842503010078853 8020275101220469314389785)
                ·
                  refine ⟨6015206325915351985792339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020275101220469314389785 6015206325915351985792339)
                  ·
                    refine ⟨9022809488873027978688509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6015206325915351985792339 9022809488873027978688509)
                    ·
                      refine ⟨3383553558327385492008191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9022809488873027978688509 3383553558327385492008191)
                      ·
                        rfl

theorem cell23_6589447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_6589447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589447 prefixEnd_6589447 := by exact prefixLift 6589447
  have htrace : WordTrace (prefixWord ++ tailWord_6589447) baseStart_6589447 baseEnd_6589447 := by
    simpa [prefixWord, tailWord_6589447, baseEnd_6589447] using wordTrace_append hprefix tailTrace_6589447
  have hstable : (prefixWord ++ tailWord_6589447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589447).length < 2 ^ (prefixWord ++ tailWord_6589447).sum := by decide
  have hdescent : baseEnd_6589447 < baseStart_6589447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589464 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 2, 1, 3]
def baseStart_6589464 : Nat := 118140960795 + 6589464 * 2 ^ 59
def prefixEnd_6589464 : Nat := 4983230072969 + 3 ^ 40 * 6589464 * 2
def baseEnd_6589464 : Nat := 3383562287498511925495613

theorem tailTrace_6589464 : CollatzResearch.WordTrace tailWord_6589464 prefixEnd_6589464 3383562287498511925495613 := by
  unfold tailWord_6589464
  simp only [CollatzResearch.WordTrace]
  refine ⟨120168748299752396849683723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160224997733003195799578297 120168748299752396849683723)
  ·
    refine ⟨180253122449628595274525585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120168748299752396849683723 180253122449628595274525585)
    ·
      refine ⟨135189841837221446455894189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180253122449628595274525585 135189841837221446455894189)
      ·
        refine ⟨50696190688958042420960321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135189841837221446455894189 50696190688958042420960321)
        ·
          refine ⟨38022143016718531815720241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50696190688958042420960321 38022143016718531815720241)
          ·
            refine ⟨28516607262538898861790181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38022143016718531815720241 28516607262538898861790181)
            ·
              refine ⟨5346863861726043536585659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28516607262538898861790181 5346863861726043536585659)
              ·
                refine ⟨8020295792589065304878489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5346863861726043536585659 8020295792589065304878489)
                ·
                  refine ⟨6015221844441798978658867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020295792589065304878489 6015221844441798978658867)
                  ·
                    refine ⟨9022832766662698467988301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6015221844441798978658867 9022832766662698467988301)
                    ·
                      refine ⟨3383562287498511925495613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9022832766662698467988301 3383562287498511925495613)
                      ·
                        rfl

theorem cell23_6589464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_6589464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589464 prefixEnd_6589464 := by exact prefixLift 6589464
  have htrace : WordTrace (prefixWord ++ tailWord_6589464) baseStart_6589464 baseEnd_6589464 := by
    simpa [prefixWord, tailWord_6589464, baseEnd_6589464] using wordTrace_append hprefix tailTrace_6589464
  have hstable : (prefixWord ++ tailWord_6589464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589464).length < 2 ^ (prefixWord ++ tailWord_6589464).sum := by decide
  have hdescent : baseEnd_6589464 < baseStart_6589464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589474 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_6589474 : Nat := 118140960795 + 6589474 * 2 ^ 59
def prefixEnd_6589474 : Nat := 4983230072969 + 3 ^ 40 * 6589474 * 2
def baseEnd_6589474 : Nat := 3383567422305056886370567

theorem tailTrace_6589474 : CollatzResearch.WordTrace tailWord_6589474 prefixEnd_6589474 3383567422305056886370567 := by
  unfold tailWord_6589474
  simp only [CollatzResearch.WordTrace]
  refine ⟨60084465332367141351807869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160225240886312376938154317 60084465332367141351807869)
  ·
    refine ⟨22531674499637678006927951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60084465332367141351807869 22531674499637678006927951)
    ·
      refine ⟨33797511749456517010391927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22531674499637678006927951 33797511749456517010391927)
      ·
        refine ⟨50696267624184775515587891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33797511749456517010391927 50696267624184775515587891)
        ·
          refine ⟨76044401436277163273381837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50696267624184775515587891 76044401436277163273381837)
          ·
            refine ⟨28516650538603936227518189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76044401436277163273381837 28516650538603936227518189)
            ·
              refine ⟨10693743951976476085319321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28516650538603936227518189 10693743951976476085319321)
              ·
                refine ⟨8020307963982357063989491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10693743951976476085319321 8020307963982357063989491)
                ·
                  refine ⟨12030461945973535595984237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8020307963982357063989491 12030461945973535595984237)
                  ·
                    refine ⟨4511423229740075848494089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12030461945973535595984237 4511423229740075848494089)
                    ·
                      refine ⟨3383567422305056886370567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511423229740075848494089 3383567422305056886370567)
                      ·
                        rfl

theorem cell23_6589474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_6589474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589474 prefixEnd_6589474 := by exact prefixLift 6589474
  have htrace : WordTrace (prefixWord ++ tailWord_6589474) baseStart_6589474 baseEnd_6589474 := by
    simpa [prefixWord, tailWord_6589474, baseEnd_6589474] using wordTrace_append hprefix tailTrace_6589474
  have hstable : (prefixWord ++ tailWord_6589474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589474).length < 2 ^ (prefixWord ++ tailWord_6589474).sum := by decide
  have hdescent : baseEnd_6589474 < baseStart_6589474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589504 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 2, 2, 2]
def baseStart_6589504 : Nat := 118140960795 + 6589504 * 2 ^ 59
def prefixEnd_6589504 : Nat := 4983230072969 + 3 ^ 40 * 6589504 * 2
def baseEnd_6589504 : Nat := 3383582826724691768995429

theorem tailTrace_6589504 : CollatzResearch.WordTrace tailWord_6589504 prefixEnd_6589504 3383582826724691768995429 := by
  unfold tailWord_6589504
  simp only [CollatzResearch.WordTrace]
  refine ⟨120169477759679940265411783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160225970346239920353882377 120169477759679940265411783)
  ·
    refine ⟨180254216639519910398117675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120169477759679940265411783 180254216639519910398117675)
    ·
      refine ⟨270381324959279865597176513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180254216639519910398117675 270381324959279865597176513)
      ·
        refine ⟨202785993719459899197882385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270381324959279865597176513 202785993719459899197882385)
        ·
          refine ⟨152089495289594924398411789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202785993719459899197882385 152089495289594924398411789)
          ·
            refine ⟨57033560733598096649404421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152089495289594924398411789 57033560733598096649404421)
            ·
              refine ⟨10693792637549643121763329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57033560733598096649404421 10693792637549643121763329)
              ·
                refine ⟨8020344478162232341322497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10693792637549643121763329 8020344478162232341322497)
                ·
                  refine ⟨6015258358621674255991873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020344478162232341322497 6015258358621674255991873)
                  ·
                    refine ⟨4511443768966255691993905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6015258358621674255991873 4511443768966255691993905)
                    ·
                      refine ⟨3383582826724691768995429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511443768966255691993905 3383582826724691768995429)
                      ·
                        rfl

theorem cell23_6589504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_6589504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589504 prefixEnd_6589504 := by exact prefixLift 6589504
  have htrace : WordTrace (prefixWord ++ tailWord_6589504) baseStart_6589504 baseEnd_6589504 := by
    simpa [prefixWord, tailWord_6589504, baseEnd_6589504] using wordTrace_append hprefix tailTrace_6589504
  have hstable : (prefixWord ++ tailWord_6589504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589504).length < 2 ^ (prefixWord ++ tailWord_6589504).sum := by decide
  have hdescent : baseEnd_6589504 < baseStart_6589504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589517 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_6589517 : Nat := 118140960795 + 6589517 * 2 ^ 59
def prefixEnd_6589517 : Nat := 4983230072969 + 3 ^ 40 * 6589517 * 2
def baseEnd_6589517 : Nat := 3383589501973200218132869

theorem tailTrace_6589517 : CollatzResearch.WordTrace tailWord_6589517 prefixEnd_6589517 3383589501973200218132869 := by
  unfold tailWord_6589517
  simp only [CollatzResearch.WordTrace]
  refine ⟨240339429668312783751046805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160226286445541855834031203 240339429668312783751046805)
  ·
    refine ⟨11265910765702161738330319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240339429668312783751046805 11265910765702161738330319)
    ·
      refine ⟨16898866148553242607495479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11265910765702161738330319 16898866148553242607495479)
      ·
        refine ⟨25348299222829863911243219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16898866148553242607495479 25348299222829863911243219)
        ·
          refine ⟨38022448834244795866864829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25348299222829863911243219 38022448834244795866864829)
          ·
            refine ⟨14258418312841798450074311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38022448834244795866864829 14258418312841798450074311)
            ·
              refine ⟨21387627469262697675111467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14258418312841798450074311 21387627469262697675111467)
              ·
                refine ⟨32081441203894046512667201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21387627469262697675111467 32081441203894046512667201)
                ·
                  refine ⟨24061080902920534884500401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32081441203894046512667201 24061080902920534884500401)
                  ·
                    refine ⟨18045810677190401163375301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24061080902920534884500401 18045810677190401163375301)
                    ·
                      refine ⟨3383589501973200218132869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18045810677190401163375301 3383589501973200218132869)
                      ·
                        rfl

theorem cell23_6589517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_6589517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589517 prefixEnd_6589517 := by exact prefixLift 6589517
  have htrace : WordTrace (prefixWord ++ tailWord_6589517) baseStart_6589517 baseEnd_6589517 := by
    simpa [prefixWord, tailWord_6589517, baseEnd_6589517] using wordTrace_append hprefix tailTrace_6589517
  have hstable : (prefixWord ++ tailWord_6589517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589517).length < 2 ^ (prefixWord ++ tailWord_6589517).sum := by decide
  have hdescent : baseEnd_6589517 < baseStart_6589517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589523 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 6, 5]
def baseStart_6589523 : Nat := 118140960795 + 6589523 * 2 ^ 59
def prefixEnd_6589523 : Nat := 4983230072969 + 3 ^ 40 * 6589523 * 2
def baseEnd_6589523 : Nat := 1127864194285709064885947

theorem tailTrace_6589523 : CollatzResearch.WordTrace tailWord_6589523 prefixEnd_6589523 1127864194285709064885947 := by
  unfold tailWord_6589523
  simp only [CollatzResearch.WordTrace]
  refine ⟨240339648506291046775765223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160226432337527364517176815 240339648506291046775765223)
  ·
    refine ⟨360509472759436570163647835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240339648506291046775765223 360509472759436570163647835)
    ·
      refine ⟨540764209139154855245471753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360509472759436570163647835 540764209139154855245471753)
      ·
        refine ⟨405573156854366141434103815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540764209139154855245471753 405573156854366141434103815)
        ·
          refine ⟨608359735281549212151155723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405573156854366141434103815 608359735281549212151155723)
          ·
            refine ⟨912539602922323818226733585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608359735281549212151155723 912539602922323818226733585)
            ·
              refine ⟨684404702191742863670050189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912539602922323818226733585 684404702191742863670050189)
              ·
                refine ⟨256651763321903573876268821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 684404702191742863670050189 256651763321903573876268821)
                ·
                  refine ⟨12030551405714230025450101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256651763321903573876268821 12030551405714230025450101)
                  ·
                    refine ⟨1127864194285709064885947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12030551405714230025450101 1127864194285709064885947)
                    ·
                      rfl

theorem cell23_6589523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 5].length) (baseStart_6589523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589523 prefixEnd_6589523 := by exact prefixLift 6589523
  have htrace : WordTrace (prefixWord ++ tailWord_6589523) baseStart_6589523 baseEnd_6589523 := by
    simpa [prefixWord, tailWord_6589523, baseEnd_6589523] using wordTrace_append hprefix tailTrace_6589523
  have hstable : (prefixWord ++ tailWord_6589523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589523).length < 2 ^ (prefixWord ++ tailWord_6589523).sum := by decide
  have hdescent : baseEnd_6589523 < baseStart_6589523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589560 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_6589560 : Nat := 118140960795 + 6589560 * 2 ^ 59
def prefixEnd_6589560 : Nat := 4983230072969 + 3 ^ 40 * 6589560 * 2
def baseEnd_6589560 : Nat := 3383611581641343549895171

theorem tailTrace_6589560 : CollatzResearch.WordTrace tailWord_6589560 prefixEnd_6589560 3383611581641343549895171 := by
  unfold tailWord_6589560
  simp only [CollatzResearch.WordTrace]
  refine ⟨120170499003578501047431067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160227332004771334729908089 120170499003578501047431067)
  ·
    refine ⟨180255748505367751571146601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120170499003578501047431067 180255748505367751571146601)
    ·
      refine ⟨135191811379025813678359951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180255748505367751571146601 135191811379025813678359951)
      ·
        refine ⟨202787717068538720517539927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135191811379025813678359951 202787717068538720517539927)
        ·
          refine ⟨304181575602808080776309891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202787717068538720517539927 304181575602808080776309891)
          ·
            refine ⟨456272363404212121164464837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304181575602808080776309891 456272363404212121164464837)
            ·
              refine ⟨85551068138289772718337157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 456272363404212121164464837 85551068138289772718337157)
              ·
                refine ⟨16040825275929332384688217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85551068138289772718337157 16040825275929332384688217)
                ·
                  refine ⟨12030618956946999288516163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16040825275929332384688217 12030618956946999288516163)
                  ·
                    refine ⟨18045928435420498932774245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12030618956946999288516163 18045928435420498932774245)
                    ·
                      refine ⟨3383611581641343549895171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18045928435420498932774245 3383611581641343549895171)
                      ·
                        rfl

theorem cell23_6589560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_6589560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589560 prefixEnd_6589560 := by exact prefixLift 6589560
  have htrace : WordTrace (prefixWord ++ tailWord_6589560) baseStart_6589560 baseEnd_6589560 := by
    simpa [prefixWord, tailWord_6589560, baseEnd_6589560] using wordTrace_append hprefix tailTrace_6589560
  have hstable : (prefixWord ++ tailWord_6589560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589560).length < 2 ^ (prefixWord ++ tailWord_6589560).sum := by decide
  have hdescent : baseEnd_6589560 < baseStart_6589560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589563 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 5]
def baseStart_6589563 : Nat := 118140960795 + 6589563 * 2 ^ 59
def prefixEnd_6589563 : Nat := 4983230072969 + 3 ^ 40 * 6589563 * 2
def baseEnd_6589563 : Nat := 3383613122083307038157657

theorem tailTrace_6589563 : CollatzResearch.WordTrace tailWord_6589563 prefixEnd_6589563 3383613122083307038157657 := by
  unfold tailWord_6589563
  simp only [CollatzResearch.WordTrace]
  refine ⟨240341107426146133607221343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160227404950764089071480895 240341107426146133607221343)
  ·
    refine ⟨360511661139219200410832015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240341107426146133607221343 360511661139219200410832015)
    ·
      refine ⟨540767491708828800616248023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360511661139219200410832015 540767491708828800616248023)
      ·
        refine ⟨811151237563243200924372035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540767491708828800616248023 811151237563243200924372035)
        ·
          refine ⟨1216726856344864801386558053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811151237563243200924372035 1216726856344864801386558053)
          ·
            refine ⟨228136285564662150259979635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1216726856344864801386558053 228136285564662150259979635)
            ·
              refine ⟨342204428346993225389969453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228136285564662150259979635 342204428346993225389969453)
              ·
                refine ⟨128326660630122459521238545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342204428346993225389969453 128326660630122459521238545)
                ·
                  refine ⟨96244995472591844640928909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128326660630122459521238545 96244995472591844640928909)
                  ·
                    refine ⟨36091873302221941740348341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96244995472591844640928909 36091873302221941740348341)
                    ·
                      refine ⟨3383613122083307038157657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36091873302221941740348341 3383613122083307038157657)
                      ·
                        rfl

theorem cell23_6589563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_6589563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589563 prefixEnd_6589563 := by exact prefixLift 6589563
  have htrace : WordTrace (prefixWord ++ tailWord_6589563) baseStart_6589563 baseEnd_6589563 := by
    simpa [prefixWord, tailWord_6589563, baseEnd_6589563] using wordTrace_append hprefix tailTrace_6589563
  have hstable : (prefixWord ++ tailWord_6589563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589563).length < 2 ^ (prefixWord ++ tailWord_6589563).sum := by decide
  have hdescent : baseEnd_6589563 < baseStart_6589563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589577 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 2, 4, 2]
def baseStart_6589577 : Nat := 118140960795 + 6589577 * 2 ^ 59
def prefixEnd_6589577 : Nat := 4983230072969 + 3 ^ 40 * 6589577 * 2
def baseEnd_6589577 : Nat := 3383620310812469983382593

theorem tailTrace_6589577 : CollatzResearch.WordTrace tailWord_6589577 prefixEnd_6589577 3383620310812469983382593 := by
  unfold tailWord_6589577
  simp only [CollatzResearch.WordTrace]
  refine ⟨240341618048095413998230985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160227745365396942665487323 240341618048095413998230985)
  ·
    refine ⟨180256213536071560498673239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240341618048095413998230985 180256213536071560498673239)
    ·
      refine ⟨270384320304107340748009859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180256213536071560498673239 270384320304107340748009859)
      ·
        refine ⟨405576480456161011122014789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270384320304107340748009859 405576480456161011122014789)
        ·
          refine ⟨76045590085530189585377773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405576480456161011122014789 76045590085530189585377773)
          ·
            refine ⟨28517096282073821094516665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76045590085530189585377773 28517096282073821094516665)
            ·
              refine ⟨21387822211555365820887499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28517096282073821094516665 21387822211555365820887499)
              ·
                refine ⟨32081733317333048731331249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21387822211555365820887499 32081733317333048731331249)
                ·
                  refine ⟨24061299987999786548498437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32081733317333048731331249 24061299987999786548498437)
                  ·
                    refine ⟨4511493747749959977843457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24061299987999786548498437 4511493747749959977843457)
                    ·
                      refine ⟨3383620310812469983382593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511493747749959977843457 3383620310812469983382593)
                      ·
                        rfl

theorem cell23_6589577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 4, 2].length) (baseStart_6589577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589577 prefixEnd_6589577 := by exact prefixLift 6589577
  have htrace : WordTrace (prefixWord ++ tailWord_6589577) baseStart_6589577 baseEnd_6589577 := by
    simpa [prefixWord, tailWord_6589577, baseEnd_6589577] using wordTrace_append hprefix tailTrace_6589577
  have hstable : (prefixWord ++ tailWord_6589577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589577).length < 2 ^ (prefixWord ++ tailWord_6589577).sum := by decide
  have hdescent : baseEnd_6589577 < baseStart_6589577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589593 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_6589593 : Nat := 118140960795 + 6589593 * 2 ^ 59
def prefixEnd_6589593 : Nat := 4983230072969 + 3 ^ 40 * 6589593 * 2
def baseEnd_6589593 : Nat := 3383628526502941920782519

theorem tailTrace_6589593 : CollatzResearch.WordTrace tailWord_6589593 prefixEnd_6589593 3383628526502941920782519 := by
  unfold tailWord_6589593
  simp only [CollatzResearch.WordTrace]
  refine ⟨240342201616037448730813433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160228134410691632487208955 240342201616037448730813433)
  ·
    refine ⟨180256651212028086548110075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240342201616037448730813433 180256651212028086548110075)
    ·
      refine ⟨270384976818042129822165113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180256651212028086548110075 270384976818042129822165113)
      ·
        refine ⟨202788732613531597366623835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270384976818042129822165113 202788732613531597366623835)
        ·
          refine ⟨304183098920297396049935753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202788732613531597366623835 304183098920297396049935753)
          ·
            refine ⟨228137324190223047037451815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304183098920297396049935753 228137324190223047037451815)
            ·
              refine ⟨342205986285334570556177723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228137324190223047037451815 342205986285334570556177723)
              ·
                refine ⟨513308979428001855834266585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342205986285334570556177723 513308979428001855834266585)
                ·
                  refine ⟨384981734571001391875699939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513308979428001855834266585 384981734571001391875699939)
                  ·
                    refine ⟨577472601856502087813549909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 384981734571001391875699939 577472601856502087813549909)
                    ·
                      refine ⟨3383628526502941920782519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 577472601856502087813549909 3383628526502941920782519)
                      ·
                        rfl

theorem cell23_6589593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_6589593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589593 prefixEnd_6589593 := by exact prefixLift 6589593
  have htrace : WordTrace (prefixWord ++ tailWord_6589593) baseStart_6589593 baseEnd_6589593 := by
    simpa [prefixWord, tailWord_6589593, baseEnd_6589593] using wordTrace_append hprefix tailTrace_6589593
  have hstable : (prefixWord ++ tailWord_6589593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589593).length < 2 ^ (prefixWord ++ tailWord_6589593).sum := by decide
  have hdescent : baseEnd_6589593 < baseStart_6589593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589597 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_6589597 : Nat := 118140960795 + 6589597 * 2 ^ 59
def prefixEnd_6589597 : Nat := 4983230072969 + 3 ^ 40 * 6589597 * 2
def baseEnd_6589597 : Nat := 3383630580425559905132501

theorem tailTrace_6589597 : CollatzResearch.WordTrace tailWord_6589597 prefixEnd_6589597 3383630580425559905132501 := by
  unfold tailWord_6589597
  simp only [CollatzResearch.WordTrace]
  refine ⟨240342347508022957413959045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160228231672015304942639363 240342347508022957413959045)
  ·
    refine ⟨45064190157754304515117321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240342347508022957413959045 45064190157754304515117321)
    ·
      refine ⟨33798142618315728386337991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45064190157754304515117321 33798142618315728386337991)
      ·
        refine ⟨50697213927473592579506987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33798142618315728386337991 50697213927473592579506987)
        ·
          refine ⟨76045820891210388869260481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50697213927473592579506987 76045820891210388869260481)
          ·
            refine ⟨57034365668407791651945361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76045820891210388869260481 57034365668407791651945361)
            ·
              refine ⟨42775774251305843738959021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57034365668407791651945361 42775774251305843738959021)
              ·
                refine ⟨16040915344239691402109633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42775774251305843738959021 16040915344239691402109633)
                ·
                  refine ⟨12030686508179768551582225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16040915344239691402109633 12030686508179768551582225)
                  ·
                    refine ⟨9023014881134826413686669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12030686508179768551582225 9023014881134826413686669)
                    ·
                      refine ⟨3383630580425559905132501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023014881134826413686669 3383630580425559905132501)
                      ·
                        rfl

theorem cell23_6589597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_6589597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589597 prefixEnd_6589597 := by exact prefixLift 6589597
  have htrace : WordTrace (prefixWord ++ tailWord_6589597) baseStart_6589597 baseEnd_6589597 := by
    simpa [prefixWord, tailWord_6589597, baseEnd_6589597] using wordTrace_append hprefix tailTrace_6589597
  have hstable : (prefixWord ++ tailWord_6589597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589597).length < 2 ^ (prefixWord ++ tailWord_6589597).sum := by decide
  have hdescent : baseEnd_6589597 < baseStart_6589597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589627 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 3]
def baseStart_6589627 : Nat := 118140960795 + 6589627 * 2 ^ 59
def prefixEnd_6589627 : Nat := 4983230072969 + 3 ^ 40 * 6589627 * 2
def baseEnd_6589627 : Nat := 3383645984845194787757363

theorem tailTrace_6589627 : CollatzResearch.WordTrace tailWord_6589627 prefixEnd_6589627 3383645984845194787757363 := by
  unfold tailWord_6589627
  simp only [CollatzResearch.WordTrace]
  refine ⟨240343441697914272537551135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160228961131942848358367423 240343441697914272537551135)
  ·
    refine ⟨360515162546871408806326703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240343441697914272537551135 360515162546871408806326703)
    ·
      refine ⟨540772743820307113209490055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360515162546871408806326703 540772743820307113209490055)
      ·
        refine ⟨811159115730460669814235083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540772743820307113209490055 811159115730460669814235083)
        ·
          refine ⟨1216738673595691004721352625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811159115730460669814235083 1216738673595691004721352625)
          ·
            refine ⟨912554005196768253541014469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1216738673595691004721352625 912554005196768253541014469)
            ·
              refine ⟨171103875974394047538940213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 912554005196768253541014469 171103875974394047538940213)
              ·
                refine ⟨16040988372599441956775645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171103875974394047538940213 16040988372599441956775645)
                ·
                  refine ⟨6015370639724790733790867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16040988372599441956775645 6015370639724790733790867)
                  ·
                    refine ⟨9023055959587186100686301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6015370639724790733790867 9023055959587186100686301)
                    ·
                      refine ⟨3383645984845194787757363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023055959587186100686301 3383645984845194787757363)
                      ·
                        rfl

theorem cell23_6589627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 3].length) (baseStart_6589627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589627 prefixEnd_6589627 := by exact prefixLift 6589627
  have htrace : WordTrace (prefixWord ++ tailWord_6589627) baseStart_6589627 baseEnd_6589627 := by
    simpa [prefixWord, tailWord_6589627, baseEnd_6589627] using wordTrace_append hprefix tailTrace_6589627
  have hstable : (prefixWord ++ tailWord_6589627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589627).length < 2 ^ (prefixWord ++ tailWord_6589627).sum := by decide
  have hdescent : baseEnd_6589627 < baseStart_6589627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589637 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 6, 3, 2]
def baseStart_6589637 : Nat := 118140960795 + 6589637 * 2 ^ 59
def prefixEnd_6589637 : Nat := 4983230072969 + 3 ^ 40 * 6589637 * 2
def baseEnd_6589637 : Nat := 3383651119651739748632317

theorem tailTrace_6589637 : CollatzResearch.WordTrace tailWord_6589637 prefixEnd_6589637 3383651119651739748632317 := by
  unfold tailWord_6589637
  simp only [CollatzResearch.WordTrace]
  refine ⟨240343806427878044245415165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160229204285252029496943443 240343806427878044245415165)
  ·
    refine ⟨90128927410454266592030687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240343806427878044245415165 90128927410454266592030687)
    ·
      refine ⟨135193391115681399888046031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90128927410454266592030687 135193391115681399888046031)
      ·
        refine ⟨202790086673522099832069047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135193391115681399888046031 202790086673522099832069047)
        ·
          refine ⟨304185130010283149748103571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202790086673522099832069047 304185130010283149748103571)
          ·
            refine ⟨456277695015424724622155357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304185130010283149748103571 456277695015424724622155357)
            ·
              refine ⟨171104135630784271733308259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456277695015424724622155357 171104135630784271733308259)
              ·
                refine ⟨256656203446176407599962389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171104135630784271733308259 256656203446176407599962389)
                ·
                  refine ⟨12030759536539519106248237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256656203446176407599962389 12030759536539519106248237)
                  ·
                    refine ⟨4511534826202319664843089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12030759536539519106248237 4511534826202319664843089)
                    ·
                      refine ⟨3383651119651739748632317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511534826202319664843089 3383651119651739748632317)
                      ·
                        rfl

theorem cell23_6589637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_6589637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589637 prefixEnd_6589637 := by exact prefixLift 6589637
  have htrace : WordTrace (prefixWord ++ tailWord_6589637) baseStart_6589637 baseEnd_6589637 := by
    simpa [prefixWord, tailWord_6589637, baseEnd_6589637] using wordTrace_append hprefix tailTrace_6589637
  have hstable : (prefixWord ++ tailWord_6589637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589637).length < 2 ^ (prefixWord ++ tailWord_6589637).sum := by decide
  have hdescent : baseEnd_6589637 < baseStart_6589637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589664 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 1, 5]
def baseStart_6589664 : Nat := 118140960795 + 6589664 * 2 ^ 59
def prefixEnd_6589664 : Nat := 4983230072969 + 3 ^ 40 * 6589664 * 2
def baseEnd_6589664 : Nat := 1127888327876470380998231

theorem tailTrace_6589664 : CollatzResearch.WordTrace tailWord_6589664 prefixEnd_6589664 1127888327876470380998231 := by
  unfold tailWord_6589664
  simp only [CollatzResearch.WordTrace]
  refine ⟨120172395599390113928324023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160229860799186818571098697 120172395599390113928324023)
  ·
    refine ⟨180258593399085170892486035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120172395599390113928324023 180258593399085170892486035)
    ·
      refine ⟨270387890098627756338729053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180258593399085170892486035 270387890098627756338729053)
      ·
        refine ⟨101395458786985408627023395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270387890098627756338729053 101395458786985408627023395)
        ·
          refine ⟨152093188180478112940535093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101395458786985408627023395 152093188180478112940535093)
          ·
            refine ⟨14258736391919823088175165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152093188180478112940535093 14258736391919823088175165)
            ·
              refine ⟨5347026146969933658065687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14258736391919823088175165 5347026146969933658065687)
              ·
                refine ⟨8020539220454900487098531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347026146969933658065687 8020539220454900487098531)
                ·
                  refine ⟨12030808830682350730647797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8020539220454900487098531 12030808830682350730647797)
                  ·
                    refine ⟨1127888327876470380998231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12030808830682350730647797 1127888327876470380998231)
                    ·
                      rfl

theorem cell23_6589664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 5].length) (baseStart_6589664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589664 prefixEnd_6589664 := by exact prefixLift 6589664
  have htrace : WordTrace (prefixWord ++ tailWord_6589664) baseStart_6589664 baseEnd_6589664 := by
    simpa [prefixWord, tailWord_6589664, baseEnd_6589664] using wordTrace_append hprefix tailTrace_6589664
  have hstable : (prefixWord ++ tailWord_6589664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589664).length < 2 ^ (prefixWord ++ tailWord_6589664).sum := by decide
  have hdescent : baseEnd_6589664 < baseStart_6589664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589678 : List Nat := [4, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_6589678 : Nat := 118140960795 + 6589678 * 2 ^ 59
def prefixEnd_6589678 : Nat := 4983230072969 + 3 ^ 40 * 6589678 * 2
def baseEnd_6589678 : Nat := 3383672172358574088219629

theorem tailTrace_6589678 : CollatzResearch.WordTrace tailWord_6589678 prefixEnd_6589678 3383672172358574088219629 := by
  unfold tailWord_6589678
  simp only [CollatzResearch.WordTrace]
  refine ⟨30043162727591188530957211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160230201213819672165105125 30043162727591188530957211)
  ·
    refine ⟨45064744091386782796435817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30043162727591188530957211 45064744091386782796435817)
    ·
      refine ⟨33798558068540087097326863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45064744091386782796435817 33798558068540087097326863)
      ·
        refine ⟨50697837102810130645990295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33798558068540087097326863 50697837102810130645990295)
        ·
          refine ⟨76046755654215195968985443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50697837102810130645990295 76046755654215195968985443)
          ·
            refine ⟨114070133481322793953478165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76046755654215195968985443 114070133481322793953478165)
            ·
              refine ⟨5347037506937005966569289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114070133481322793953478165 5347037506937005966569289)
              ·
                refine ⟨4010278130202754474926967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5347037506937005966569289 4010278130202754474926967)
                ·
                  refine ⟨6015417195304131712390451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010278130202754474926967 6015417195304131712390451)
                  ·
                    refine ⟨9023125792956197568585677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6015417195304131712390451 9023125792956197568585677)
                    ·
                      refine ⟨3383672172358574088219629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023125792956197568585677 3383672172358574088219629)
                      ·
                        rfl

theorem cell23_6589678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_6589678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589678 prefixEnd_6589678 := by exact prefixLift 6589678
  have htrace : WordTrace (prefixWord ++ tailWord_6589678) baseStart_6589678 baseEnd_6589678 := by
    simpa [prefixWord, tailWord_6589678, baseEnd_6589678] using wordTrace_append hprefix tailTrace_6589678
  have hstable : (prefixWord ++ tailWord_6589678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589678).length < 2 ^ (prefixWord ++ tailWord_6589678).sum := by decide
  have hdescent : baseEnd_6589678 < baseStart_6589678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589694 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6589694 : Nat := 118140960795 + 6589694 * 2 ^ 59
def prefixEnd_6589694 : Nat := 4983230072969 + 3 ^ 40 * 6589694 * 2
def baseEnd_6589694 : Nat := 1127893462683015341873185

theorem tailTrace_6589694 : CollatzResearch.WordTrace tailWord_6589694 prefixEnd_6589694 1127893462683015341873185 := by
  unfold tailWord_6589694
  simp only [CollatzResearch.WordTrace]
  refine ⟨30043235673583942872530017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160230590259114361986826757 30043235673583942872530017)
  ·
    refine ⟨22532426755187957154397513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30043235673583942872530017 22532426755187957154397513)
    ·
      refine ⟨16899320066390967865798135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22532426755187957154397513 16899320066390967865798135)
      ·
        refine ⟨25348980099586451798697203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16899320066390967865798135 25348980099586451798697203)
        ·
          refine ⟨38023470149379677698045805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25348980099586451798697203 38023470149379677698045805)
          ·
            refine ⟨14258801306017379136767177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38023470149379677698045805 14258801306017379136767177)
            ·
              refine ⟨10694100979513034352575383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14258801306017379136767177 10694100979513034352575383)
              ·
                refine ⟨16041151469269551528863075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10694100979513034352575383 16041151469269551528863075)
                ·
                  refine ⟨24061727203904327293294613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16041151469269551528863075 24061727203904327293294613)
                  ·
                    refine ⟨1127893462683015341873185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24061727203904327293294613 1127893462683015341873185)
                    ·
                      rfl

theorem cell23_6589694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6589694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589694 prefixEnd_6589694 := by exact prefixLift 6589694
  have htrace : WordTrace (prefixWord ++ tailWord_6589694) baseStart_6589694 baseEnd_6589694 := by
    simpa [prefixWord, tailWord_6589694, baseEnd_6589694] using wordTrace_append hprefix tailTrace_6589694
  have hstable : (prefixWord ++ tailWord_6589694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589694).length < 2 ^ (prefixWord ++ tailWord_6589694).sum := by decide
  have hdescent : baseEnd_6589694 < baseStart_6589694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589697 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_6589697 : Nat := 118140960795 + 6589697 * 2 ^ 59
def prefixEnd_6589697 : Nat := 4983230072969 + 3 ^ 40 * 6589697 * 2
def baseEnd_6589697 : Nat := 3383681928491009513882041

theorem tailTrace_6589697 : CollatzResearch.WordTrace tailWord_6589697 prefixEnd_6589697 3383681928491009513882041 := by
  unfold tailWord_6589697
  simp only [CollatzResearch.WordTrace]
  refine ⟨240345994807660674492599345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160230663205107116328399563 240345994807660674492599345)
  ·
    refine ⟨180259496105745505869449509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240345994807660674492599345 180259496105745505869449509)
    ·
      refine ⟨33798655519827282350521783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180259496105745505869449509 33798655519827282350521783)
      ·
        refine ⟨50697983279740923525782675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33798655519827282350521783 50697983279740923525782675)
        ·
          refine ⟨76046974919611385288674013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50697983279740923525782675 76046974919611385288674013)
          ·
            refine ⟨28517615594854269483252755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76046974919611385288674013 28517615594854269483252755)
            ·
              refine ⟨42776423392281404224879133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28517615594854269483252755 42776423392281404224879133)
              ·
                refine ⟨16041158772105526584329675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42776423392281404224879133 16041158772105526584329675)
                ·
                  refine ⟨24061738158158289876494513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16041158772105526584329675 24061738158158289876494513)
                  ·
                    refine ⟨18046303618618717407370885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24061738158158289876494513 18046303618618717407370885)
                    ·
                      refine ⟨3383681928491009513882041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18046303618618717407370885 3383681928491009513882041)
                      ·
                        rfl

theorem cell23_6589697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_6589697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589697 prefixEnd_6589697 := by exact prefixLift 6589697
  have htrace : WordTrace (prefixWord ++ tailWord_6589697) baseStart_6589697 baseEnd_6589697 := by
    simpa [prefixWord, tailWord_6589697, baseEnd_6589697] using wordTrace_append hprefix tailTrace_6589697
  have hstable : (prefixWord ++ tailWord_6589697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589697).length < 2 ^ (prefixWord ++ tailWord_6589697).sum := by decide
  have hdescent : baseEnd_6589697 < baseStart_6589697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589707 : List Nat := [1, 1, 1, 1, 5, 4, 3, 7]
def baseStart_6589707 : Nat := 118140960795 + 6589707 * 2 ^ 59
def prefixEnd_6589707 : Nat := 4983230072969 + 3 ^ 40 * 6589707 * 2
def baseEnd_6589707 : Nat := 125321743085094610176185

theorem tailTrace_6589707 : CollatzResearch.WordTrace tailWord_6589707 prefixEnd_6589707 125321743085094610176185 := by
  unfold tailWord_6589707
  simp only [CollatzResearch.WordTrace]
  refine ⟨240346359537624446200463375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160230906358416297466975583 240346359537624446200463375)
  ·
    refine ⟨360519539306436669300695063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240346359537624446200463375 360519539306436669300695063)
    ·
      refine ⟨540779308959655003951042595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360519539306436669300695063 540779308959655003951042595)
      ·
        refine ⟨811168963439482505926563893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540779308959655003951042595 811168963439482505926563893)
        ·
          refine ⟨76047090322451484930615365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 811168963439482505926563893 76047090322451484930615365)
          ·
            refine ⟨14258829435459653424490381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76047090322451484930615365 14258829435459653424490381)
            ·
              refine ⟨5347061038297370034183893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14258829435459653424490381 5347061038297370034183893)
              ·
                refine ⟨125321743085094610176185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5347061038297370034183893 125321743085094610176185)
                ·
                  rfl

theorem cell23_6589707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 7].length) (baseStart_6589707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589707 prefixEnd_6589707 := by exact prefixLift 6589707
  have htrace : WordTrace (prefixWord ++ tailWord_6589707) baseStart_6589707 baseEnd_6589707 := by
    simpa [prefixWord, tailWord_6589707, baseEnd_6589707] using wordTrace_append hprefix tailTrace_6589707
  have hstable : (prefixWord ++ tailWord_6589707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589707).length < 2 ^ (prefixWord ++ tailWord_6589707).sum := by decide
  have hdescent : baseEnd_6589707 < baseStart_6589707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589728 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 2, 4]
def baseStart_6589728 : Nat := 118140960795 + 6589728 * 2 ^ 59
def prefixEnd_6589728 : Nat := 4983230072969 + 3 ^ 40 * 6589728 * 2
def baseEnd_6589728 : Nat := 1127899282130432964198133

theorem tailTrace_6589728 : CollatzResearch.WordTrace tailWord_6589728 prefixEnd_6589728 1127899282130432964198133 := by
  unfold tailWord_6589728
  simp only [CollatzResearch.WordTrace]
  refine ⟨120173562735274183393488919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160231416980365577857985225 120173562735274183393488919)
  ·
    refine ⟨180260344102911275090233379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120173562735274183393488919 180260344102911275090233379)
    ·
      refine ⟨270390516154366912635350069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180260344102911275090233379 270390516154366912635350069)
      ·
        refine ⟨25349110889471898059564069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270390516154366912635350069 25349110889471898059564069)
        ·
          refine ⟨4752958291775980886168263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25349110889471898059564069 4752958291775980886168263)
          ·
            refine ⟨7129437437663971329252395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752958291775980886168263 7129437437663971329252395)
            ·
              refine ⟨10694156156495956993878593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129437437663971329252395 10694156156495956993878593)
              ·
                refine ⟨8020617117371967745408945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10694156156495956993878593 8020617117371967745408945)
                ·
                  refine ⟨6015462838028975809056709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020617117371967745408945 6015462838028975809056709)
                  ·
                    refine ⟨1127899282130432964198133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015462838028975809056709 1127899282130432964198133)
                    ·
                      rfl

theorem cell23_6589728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 4].length) (baseStart_6589728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589728 prefixEnd_6589728 := by exact prefixLift 6589728
  have htrace : WordTrace (prefixWord ++ tailWord_6589728) baseStart_6589728 baseEnd_6589728 := by
    simpa [prefixWord, tailWord_6589728, baseEnd_6589728] using wordTrace_append hprefix tailTrace_6589728
  have hstable : (prefixWord ++ tailWord_6589728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589728).length < 2 ^ (prefixWord ++ tailWord_6589728).sum := by decide
  have hdescent : baseEnd_6589728 < baseStart_6589728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589764 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6589764 : Nat := 118140960795 + 6589764 * 2 ^ 59
def prefixEnd_6589764 : Nat := 4983230072969 + 3 ^ 40 * 6589764 * 2
def baseEnd_6589764 : Nat := 3383716331694860751744233

theorem tailTrace_6589764 : CollatzResearch.WordTrace tailWord_6589764 prefixEnd_6589764 3383716331694860751744233 := by
  unfold tailWord_6589764
  simp only [CollatzResearch.WordTrace]
  refine ⟨120174219249208972467644173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160232292332278629956858897 120174219249208972467644173)
  ·
    refine ⟨45065332218453364675366565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120174219249208972467644173 45065332218453364675366565)
    ·
      refine ⟨8449749790960005876631231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45065332218453364675366565 8449749790960005876631231)
      ·
        refine ⟨12674624686440008814946847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8449749790960005876631231 12674624686440008814946847)
        ·
          refine ⟨19011937029660013222420271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12674624686440008814946847 19011937029660013222420271)
          ·
            refine ⟨28517905544490019833630407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19011937029660013222420271 28517905544490019833630407)
            ·
              refine ⟨42776858316735029750445611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28517905544490019833630407 42776858316735029750445611)
              ·
                refine ⟨64165287475102544625668417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42776858316735029750445611 64165287475102544625668417)
                ·
                  refine ⟨48123965606326908469251313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64165287475102544625668417 48123965606326908469251313)
                  ·
                    refine ⟨36092974204745181351938485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48123965606326908469251313 36092974204745181351938485)
                    ·
                      refine ⟨3383716331694860751744233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36092974204745181351938485 3383716331694860751744233)
                      ·
                        rfl

theorem cell23_6589764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6589764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589764 prefixEnd_6589764 := by exact prefixLift 6589764
  have htrace : WordTrace (prefixWord ++ tailWord_6589764) baseStart_6589764 baseEnd_6589764 := by
    simpa [prefixWord, tailWord_6589764, baseEnd_6589764] using wordTrace_append hprefix tailTrace_6589764
  have hstable : (prefixWord ++ tailWord_6589764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589764).length < 2 ^ (prefixWord ++ tailWord_6589764).sum := by decide
  have hdescent : baseEnd_6589764 < baseStart_6589764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589774 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_6589774 : Nat := 118140960795 + 6589774 * 2 ^ 59
def prefixEnd_6589774 : Nat := 4983230072969 + 3 ^ 40 * 6589774 * 2
def baseEnd_6589774 : Nat := 3383721466501405712619187

theorem tailTrace_6589774 : CollatzResearch.WordTrace tailWord_6589774 prefixEnd_6589774 3383721466501405712619187 := by
  unfold tailWord_6589774
  simp only [CollatzResearch.WordTrace]
  refine ⟨30043600403547714580394047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160232535485587811095434917 30043600403547714580394047)
  ·
    refine ⟨45065400605321571870591071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30043600403547714580394047 45065400605321571870591071)
    ·
      refine ⟨67598100907982357805886607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45065400605321571870591071 67598100907982357805886607)
      ·
        refine ⟨101397151361973536708829911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67598100907982357805886607 101397151361973536708829911)
        ·
          refine ⟨152095727042960305063244867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101397151361973536708829911 152095727042960305063244867)
          ·
            refine ⟨228143590564440457594867301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152095727042960305063244867 228143590564440457594867301)
            ·
              refine ⟨42776923230832585799037619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228143590564440457594867301 42776923230832585799037619)
              ·
                refine ⟨64165384846248878698556429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42776923230832585799037619 64165384846248878698556429)
                ·
                  refine ⟨24062019317343329511958661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64165384846248878698556429 24062019317343329511958661)
                  ·
                    refine ⟨4511628622001874283492249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24062019317343329511958661 4511628622001874283492249)
                    ·
                      refine ⟨3383721466501405712619187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511628622001874283492249 3383721466501405712619187)
                      ·
                        rfl

theorem cell23_6589774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_6589774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589774 prefixEnd_6589774 := by exact prefixLift 6589774
  have htrace : WordTrace (prefixWord ++ tailWord_6589774) baseStart_6589774 baseEnd_6589774 := by
    simpa [prefixWord, tailWord_6589774, baseEnd_6589774] using wordTrace_append hprefix tailTrace_6589774
  have hstable : (prefixWord ++ tailWord_6589774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589774).length < 2 ^ (prefixWord ++ tailWord_6589774).sum := by decide
  have hdescent : baseEnd_6589774 < baseStart_6589774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589777 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_6589777 : Nat := 118140960795 + 6589777 * 2 ^ 59
def prefixEnd_6589777 : Nat := 4983230072969 + 3 ^ 40 * 6589777 * 2
def baseEnd_6589777 : Nat := 3383723006943369200881673

theorem tailTrace_6589777 : CollatzResearch.WordTrace tailWord_6589777 prefixEnd_6589777 3383723006943369200881673 := by
  unfold tailWord_6589777
  simp only [CollatzResearch.WordTrace]
  refine ⟨240348912647370848155511585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160232608431580565437007723 240348912647370848155511585)
  ·
    refine ⟨180261684485528136116633689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240348912647370848155511585 180261684485528136116633689)
    ·
      refine ⟨135196263364146102087475267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180261684485528136116633689 135196263364146102087475267)
      ·
        refine ⟨202794395046219153131212901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135196263364146102087475267 202794395046219153131212901)
        ·
          refine ⟨38023949071166091212102419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202794395046219153131212901 38023949071166091212102419)
          ·
            refine ⟨57035923606749136818153629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38023949071166091212102419 57035923606749136818153629)
            ·
              refine ⟨21388471352530926306807611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57035923606749136818153629 21388471352530926306807611)
              ·
                refine ⟨32082707028796389460211417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21388471352530926306807611 32082707028796389460211417)
                ·
                  refine ⟨24062030271597292095158563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32082707028796389460211417 24062030271597292095158563)
                  ·
                    refine ⟨36093045407395938142737845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24062030271597292095158563 36093045407395938142737845)
                    ·
                      refine ⟨3383723006943369200881673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36093045407395938142737845 3383723006943369200881673)
                      ·
                        rfl

theorem cell23_6589777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_6589777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589777 prefixEnd_6589777 := by exact prefixLift 6589777
  have htrace : WordTrace (prefixWord ++ tailWord_6589777) baseStart_6589777 baseEnd_6589777 := by
    simpa [prefixWord, tailWord_6589777, baseEnd_6589777] using wordTrace_append hprefix tailTrace_6589777
  have hstable : (prefixWord ++ tailWord_6589777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589777).length < 2 ^ (prefixWord ++ tailWord_6589777).sum := by decide
  have hdescent : baseEnd_6589777 < baseStart_6589777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589791 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 2, 2, 2]
def baseStart_6589791 : Nat := 118140960795 + 6589791 * 2 ^ 59
def prefixEnd_6589791 : Nat := 4983230072969 + 3 ^ 40 * 6589791 * 2
def baseEnd_6589791 : Nat := 3383730195672532146106609

theorem tailTrace_6589791 : CollatzResearch.WordTrace tailWord_6589791 prefixEnd_6589791 3383730195672532146106609 := by
  unfold tailWord_6589791
  simp only [CollatzResearch.WordTrace]
  refine ⟨240349423269320128546521227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160232948846213419031014151 240349423269320128546521227)
  ·
    refine ⟨360524134903980192819781841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240349423269320128546521227 360524134903980192819781841)
    ·
      refine ⟨270393101177985144614836381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360524134903980192819781841 270393101177985144614836381)
      ·
        refine ⟨101397412941744429230563643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270393101177985144614836381 101397412941744429230563643)
        ·
          refine ⟨152096119412616643845845465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101397412941744429230563643 152096119412616643845845465)
          ·
            refine ⟨114072089559462482884384099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152096119412616643845845465 114072089559462482884384099)
            ·
              refine ⟨171108134339193724326576149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114072089559462482884384099 171108134339193724326576149)
              ·
                refine ⟨8020693797149705827808257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171108134339193724326576149 8020693797149705827808257)
                ·
                  refine ⟨6015520347862279370856193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020693797149705827808257 6015520347862279370856193)
                  ·
                    refine ⟨4511640260896709528142145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6015520347862279370856193 4511640260896709528142145)
                    ·
                      refine ⟨3383730195672532146106609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511640260896709528142145 3383730195672532146106609)
                      ·
                        rfl

theorem cell23_6589791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_6589791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589791 prefixEnd_6589791 := by exact prefixLift 6589791
  have htrace : WordTrace (prefixWord ++ tailWord_6589791) baseStart_6589791 baseEnd_6589791 := by
    simpa [prefixWord, tailWord_6589791, baseEnd_6589791] using wordTrace_append hprefix tailTrace_6589791
  have hstable : (prefixWord ++ tailWord_6589791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589791).length < 2 ^ (prefixWord ++ tailWord_6589791).sum := by decide
  have hdescent : baseEnd_6589791 < baseStart_6589791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589794 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_6589794 : Nat := 118140960795 + 6589794 * 2 ^ 59
def prefixEnd_6589794 : Nat := 4983230072969 + 3 ^ 40 * 6589794 * 2
def baseEnd_6589794 : Nat := 3383731736114495634369095

theorem tailTrace_6589794 : CollatzResearch.WordTrace tailWord_6589794 prefixEnd_6589794 3383731736114495634369095 := by
  unfold tailWord_6589794
  simp only [CollatzResearch.WordTrace]
  refine ⟨60087383172077315014720109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160233021792206173372586957 60087383172077315014720109)
  ·
    refine ⟨22532768689528993130520041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60087383172077315014720109 22532768689528993130520041)
    ·
      refine ⟨16899576517146744847890031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22532768689528993130520041 16899576517146744847890031)
      ·
        refine ⟨25349364775720117271835047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16899576517146744847890031 25349364775720117271835047)
        ·
          refine ⟨38024047163580175907752571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25349364775720117271835047 38024047163580175907752571)
          ·
            refine ⟨57036070745370263861628857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38024047163580175907752571 57036070745370263861628857)
            ·
              refine ⟨42777053059027697896221643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57036070745370263861628857 42777053059027697896221643)
              ·
                refine ⟨64165579588541546844332465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42777053059027697896221643 64165579588541546844332465)
                ·
                  refine ⟨48124184691406160133249349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64165579588541546844332465 48124184691406160133249349)
                  ·
                    refine ⟨9023284629638655024984253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48124184691406160133249349 9023284629638655024984253)
                    ·
                      refine ⟨3383731736114495634369095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023284629638655024984253 3383731736114495634369095)
                      ·
                        rfl

theorem cell23_6589794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_6589794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589794 prefixEnd_6589794 := by exact prefixLift 6589794
  have htrace : WordTrace (prefixWord ++ tailWord_6589794) baseStart_6589794 baseEnd_6589794 := by
    simpa [prefixWord, tailWord_6589794, baseEnd_6589794] using wordTrace_append hprefix tailTrace_6589794
  have hstable : (prefixWord ++ tailWord_6589794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589794).length < 2 ^ (prefixWord ++ tailWord_6589794).sum := by decide
  have hdescent : baseEnd_6589794 < baseStart_6589794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589802 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_6589802 : Nat := 118140960795 + 6589802 * 2 ^ 59
def prefixEnd_6589802 : Nat := 4983230072969 + 3 ^ 40 * 6589802 * 2
def baseEnd_6589802 : Nat := 3383735843959731603069059

theorem tailTrace_6589802 : CollatzResearch.WordTrace tailWord_6589802 prefixEnd_6589802 3383735843959731603069059 := by
  unfold tailWord_6589802
  simp only [CollatzResearch.WordTrace]
  refine ⟨60087456118070069356292915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160233216314853518283447773 60087456118070069356292915)
  ·
    refine ⟨90131184177105104034439373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60087456118070069356292915 90131184177105104034439373)
    ·
      refine ⟨33799194066414414012914765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90131184177105104034439373 33799194066414414012914765)
      ·
        refine ⟨12674697774905405254843037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33799194066414414012914765 12674697774905405254843037)
        ·
          refine ⟨4753011665589526970566139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12674697774905405254843037 4753011665589526970566139)
          ·
            refine ⟨7129517498384290455849209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753011665589526970566139 7129517498384290455849209)
            ·
              refine ⟨5347138123788217841886907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7129517498384290455849209 5347138123788217841886907)
              ·
                refine ⟨8020707185682326762830361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347138123788217841886907 8020707185682326762830361)
                ·
                  refine ⟨6015530389261745072122771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020707185682326762830361 6015530389261745072122771)
                  ·
                    refine ⟨9023295583892617608184157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6015530389261745072122771 9023295583892617608184157)
                    ·
                      refine ⟨3383735843959731603069059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023295583892617608184157 3383735843959731603069059)
                      ·
                        rfl

theorem cell23_6589802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_6589802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589802 prefixEnd_6589802 := by exact prefixLift 6589802
  have htrace : WordTrace (prefixWord ++ tailWord_6589802) baseStart_6589802 baseEnd_6589802 := by
    simpa [prefixWord, tailWord_6589802, baseEnd_6589802] using wordTrace_append hprefix tailTrace_6589802
  have hstable : (prefixWord ++ tailWord_6589802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589802).length < 2 ^ (prefixWord ++ tailWord_6589802).sum := by decide
  have hdescent : baseEnd_6589802 < baseStart_6589802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589807 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 3]
def baseStart_6589807 : Nat := 118140960795 + 6589807 * 2 ^ 59
def prefixEnd_6589807 : Nat := 4983230072969 + 3 ^ 40 * 6589807 * 2
def baseEnd_6589807 : Nat := 3383738411363004083506535

theorem tailTrace_6589807 : CollatzResearch.WordTrace tailWord_6589807 prefixEnd_6589807 3383738411363004083506535 := by
  unfold tailWord_6589807
  simp only [CollatzResearch.WordTrace]
  refine ⟨240350006837262163279103675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160233337891508108852735783 240350006837262163279103675)
  ·
    refine ⟨360525010255893244918655513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240350006837262163279103675 360525010255893244918655513)
    ·
      refine ⟨270393757691919933688991635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360525010255893244918655513 270393757691919933688991635)
      ·
        refine ⟨405590636537879900533487453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270393757691919933688991635 405590636537879900533487453)
        ·
          refine ⟨152096488701704962700057795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405590636537879900533487453 152096488701704962700057795)
          ·
            refine ⟨228144733052557444050086693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152096488701704962700057795 228144733052557444050086693)
            ·
              refine ⟨42777137447354520759391255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228144733052557444050086693 42777137447354520759391255)
              ·
                refine ⟨64165706171031781139086883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42777137447354520759391255 64165706171031781139086883)
                ·
                  refine ⟨96248559256547671708630325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64165706171031781139086883 96248559256547671708630325)
                  ·
                    refine ⟨9023302430301344222684093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96248559256547671708630325 9023302430301344222684093)
                    ·
                      refine ⟨3383738411363004083506535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023302430301344222684093 3383738411363004083506535)
                      ·
                        rfl

theorem cell23_6589807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_6589807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589807 prefixEnd_6589807 := by exact prefixLift 6589807
  have htrace : WordTrace (prefixWord ++ tailWord_6589807) baseStart_6589807 baseEnd_6589807 := by
    simpa [prefixWord, tailWord_6589807, baseEnd_6589807] using wordTrace_append hprefix tailTrace_6589807
  have hstable : (prefixWord ++ tailWord_6589807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589807).length < 2 ^ (prefixWord ++ tailWord_6589807).sum := by decide
  have hdescent : baseEnd_6589807 < baseStart_6589807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589842 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6589842 : Nat := 118140960795 + 6589842 * 2 ^ 59
def prefixEnd_6589842 : Nat := 4983230072969 + 3 ^ 40 * 6589842 * 2
def baseEnd_6589842 : Nat := 3383756383185911446568875

theorem tailTrace_6589842 : CollatzResearch.WordTrace tailWord_6589842 prefixEnd_6589842 3383756383185911446568875 := by
  unfold tailWord_6589842
  simp only [CollatzResearch.WordTrace]
  refine ⟨60087820848033841064156945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160234188928090242837751853 60087820848033841064156945)
  ·
    refine ⟨45065865636025380798117709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60087820848033841064156945 45065865636025380798117709)
    ·
      refine ⟨16899699613509517799294141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45065865636025380798117709 16899699613509517799294141)
      ·
        refine ⟨6337387355066069174735303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16899699613509517799294141 6337387355066069174735303)
        ·
          refine ⟨9506081032599103762102955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6337387355066069174735303 9506081032599103762102955)
          ·
            refine ⟨14259121548898655643154433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506081032599103762102955 14259121548898655643154433)
            ·
              refine ⟨10694341161673991732365825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14259121548898655643154433 10694341161673991732365825)
              ·
                refine ⟨8020755871255493799274369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10694341161673991732365825 8020755871255493799274369)
                ·
                  refine ⟨6015566903441620349455777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020755871255493799274369 6015566903441620349455777)
                  ·
                    refine ⟨4511675177581215262091833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6015566903441620349455777 4511675177581215262091833)
                    ·
                      refine ⟨3383756383185911446568875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511675177581215262091833 3383756383185911446568875)
                      ·
                        rfl

theorem cell23_6589842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6589842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589842 prefixEnd_6589842 := by exact prefixLift 6589842
  have htrace : WordTrace (prefixWord ++ tailWord_6589842) baseStart_6589842 baseEnd_6589842 := by
    simpa [prefixWord, tailWord_6589842, baseEnd_6589842] using wordTrace_append hprefix tailTrace_6589842
  have hstable : (prefixWord ++ tailWord_6589842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589842).length < 2 ^ (prefixWord ++ tailWord_6589842).sum := by decide
  have hdescent : baseEnd_6589842 < baseStart_6589842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589847 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_6589847 : Nat := 118140960795 + 6589847 * 2 ^ 59
def prefixEnd_6589847 : Nat := 4983230072969 + 3 ^ 40 * 6589847 * 2
def baseEnd_6589847 : Nat := 3383758950589183927006351

theorem tailTrace_6589847 : CollatzResearch.WordTrace tailWord_6589847 prefixEnd_6589847 3383758950589183927006351 := by
  unfold tailWord_6589847
  simp only [CollatzResearch.WordTrace]
  refine ⟨240351465757117250110559795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160234310504744833407039863 240351465757117250110559795)
  ·
    refine ⟨360527198635675875165839693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240351465757117250110559795 360527198635675875165839693)
    ·
      refine ⟨135197699488378453187189885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360527198635675875165839693 135197699488378453187189885)
      ·
        refine ⟨50699137308141919945196207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135197699488378453187189885 50699137308141919945196207)
        ·
          refine ⟨76048705962212879917794311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50699137308141919945196207 76048705962212879917794311)
          ·
            refine ⟨114073058943319319876691467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76048705962212879917794311 114073058943319319876691467)
            ·
              refine ⟨171109588414978979815037201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114073058943319319876691467 171109588414978979815037201)
              ·
                refine ⟨128332191311234234861277901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171109588414978979815037201 128332191311234234861277901)
                ·
                  refine ⟨48124571741712838072979213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128332191311234234861277901 48124571741712838072979213)
                  ·
                    refine ⟨18046714403142314277367205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48124571741712838072979213 18046714403142314277367205)
                    ·
                      refine ⟨3383758950589183927006351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18046714403142314277367205 3383758950589183927006351)
                      ·
                        rfl

theorem cell23_6589847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_6589847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589847 prefixEnd_6589847 := by exact prefixLift 6589847
  have htrace : WordTrace (prefixWord ++ tailWord_6589847) baseStart_6589847 baseEnd_6589847 := by
    simpa [prefixWord, tailWord_6589847, baseEnd_6589847] using wordTrace_append hprefix tailTrace_6589847
  have hstable : (prefixWord ++ tailWord_6589847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589847).length < 2 ^ (prefixWord ++ tailWord_6589847).sum := by decide
  have hdescent : baseEnd_6589847 < baseStart_6589847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589867 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 3]
def baseStart_6589867 : Nat := 118140960795 + 6589867 * 2 ^ 59
def prefixEnd_6589867 : Nat := 4983230072969 + 3 ^ 40 * 6589867 * 2
def baseEnd_6589867 : Nat := 3383769220202273848756259

theorem tailTrace_6589867 : CollatzResearch.WordTrace tailWord_6589867 prefixEnd_6589867 3383769220202273848756259 := by
  unfold tailWord_6589867
  simp only [CollatzResearch.WordTrace]
  refine ⟨240352195217044793526287855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160234796811363195684191903 240352195217044793526287855)
  ·
    refine ⟨360528292825567190289431783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240352195217044793526287855 360528292825567190289431783)
    ·
      refine ⟨540792439238350785434147675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360528292825567190289431783 540792439238350785434147675)
      ·
        refine ⟨811188658857526178151221513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540792439238350785434147675 811188658857526178151221513)
        ·
          refine ⟨608391494143144633613416135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811188658857526178151221513 608391494143144633613416135)
          ·
            refine ⟨912587241214716950420124203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608391494143144633613416135 912587241214716950420124203)
            ·
              refine ⟨1368880861822075425630186305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912587241214716950420124203 1368880861822075425630186305)
              ·
                refine ⟨1026660646366556569222639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368880861822075425630186305 1026660646366556569222639729)
                ·
                  refine ⟨769995484774917426916979797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1026660646366556569222639729 769995484774917426916979797)
                  ·
                    refine ⟨9023384587206063596683357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 769995484774917426916979797 9023384587206063596683357)
                    ·
                      refine ⟨3383769220202273848756259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023384587206063596683357 3383769220202273848756259)
                      ·
                        rfl

theorem cell23_6589867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 3].length) (baseStart_6589867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589867 prefixEnd_6589867 := by exact prefixLift 6589867
  have htrace : WordTrace (prefixWord ++ tailWord_6589867) baseStart_6589867 baseEnd_6589867 := by
    simpa [prefixWord, tailWord_6589867, baseEnd_6589867] using wordTrace_append hprefix tailTrace_6589867
  have hstable : (prefixWord ++ tailWord_6589867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589867).length < 2 ^ (prefixWord ++ tailWord_6589867).sum := by decide
  have hdescent : baseEnd_6589867 < baseStart_6589867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589891 : List Nat := [1, 1, 1, 3, 1, 1, 5, 5, 1, 4]
def baseStart_6589891 : Nat := 118140960795 + 6589891 * 2 ^ 59
def prefixEnd_6589891 : Nat := 4983230072969 + 3 ^ 40 * 6589891 * 2
def baseEnd_6589891 : Nat := 1127927181245993918285383

theorem tailTrace_6589891 : CollatzResearch.WordTrace tailWord_6589891 prefixEnd_6589891 1127927181245993918285383 := by
  unfold tailWord_6589891
  simp only [CollatzResearch.WordTrace]
  refine ⟨240353070568957845625161527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160235380379305230416774351 240353070568957845625161527)
  ·
    refine ⟨360529605853436768437742291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240353070568957845625161527 360529605853436768437742291)
    ·
      refine ⟨540794408780155152656613437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360529605853436768437742291 540794408780155152656613437)
      ·
        refine ⟨202797903292558182246230039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540794408780155152656613437 202797903292558182246230039)
        ·
          refine ⟨304196854938837273369345059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202797903292558182246230039 304196854938837273369345059)
          ·
            refine ⟨456295282408255910054017589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304196854938837273369345059 456295282408255910054017589)
            ·
              refine ⟨42777682725773991567564149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456295282408255910054017589 42777682725773991567564149)
              ·
                refine ⟨4010407755541311709459139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42777682725773991567564149 4010407755541311709459139)
                ·
                  refine ⟨6015611633311967564188709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010407755541311709459139 6015611633311967564188709)
                  ·
                    refine ⟨1127927181245993918285383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015611633311967564188709 1127927181245993918285383)
                    ·
                      rfl

theorem cell23_6589891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 4].length) (baseStart_6589891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589891 prefixEnd_6589891 := by exact prefixLift 6589891
  have htrace : WordTrace (prefixWord ++ tailWord_6589891) baseStart_6589891 baseEnd_6589891 := by
    simpa [prefixWord, tailWord_6589891, baseEnd_6589891] using wordTrace_append hprefix tailTrace_6589891
  have hstable : (prefixWord ++ tailWord_6589891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589891).length < 2 ^ (prefixWord ++ tailWord_6589891).sum := by decide
  have hdescent : baseEnd_6589891 < baseStart_6589891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589908 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_6589908 : Nat := 118140960795 + 6589908 * 2 ^ 59
def prefixEnd_6589908 : Nat := 4983230072969 + 3 ^ 40 * 6589908 * 2
def baseEnd_6589908 : Nat := 1127930090969702729447857

theorem tailTrace_6589908 : CollatzResearch.WordTrace tailWord_6589908 prefixEnd_6589908 1127930090969702729447857 := by
  unfold tailWord_6589908
  simp only [CollatzResearch.WordTrace]
  refine ⟨120176845304948128764265189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160235793739930838352353585 120176845304948128764265189)
  ·
    refine ⟨22533158494677774143299723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120176845304948128764265189 22533158494677774143299723)
    ·
      refine ⟨33799737742016661214949585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22533158494677774143299723 33799737742016661214949585)
      ·
        refine ⟨25349803306512495911212189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33799737742016661214949585 25349803306512495911212189)
        ·
          refine ⟨9506176239942185966704571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25349803306512495911212189 9506176239942185966704571)
          ·
            refine ⟨14259264359913278950056857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506176239942185966704571 14259264359913278950056857)
            ·
              refine ⟨10694448269934959212542643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14259264359913278950056857 10694448269934959212542643)
              ·
                refine ⟨16041672404902438818813965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10694448269934959212542643 16041672404902438818813965)
                ·
                  refine ⟨6015627151838414557055237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16041672404902438818813965 6015627151838414557055237)
                  ·
                    refine ⟨1127930090969702729447857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015627151838414557055237 1127930090969702729447857)
                    ·
                      rfl

theorem cell23_6589908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_6589908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589908 prefixEnd_6589908 := by exact prefixLift 6589908
  have htrace : WordTrace (prefixWord ++ tailWord_6589908) baseStart_6589908 baseEnd_6589908 := by
    simpa [prefixWord, tailWord_6589908, baseEnd_6589908] using wordTrace_append hprefix tailTrace_6589908
  have hstable : (prefixWord ++ tailWord_6589908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589908).length < 2 ^ (prefixWord ++ tailWord_6589908).sum := by decide
  have hdescent : baseEnd_6589908 < baseStart_6589908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589921 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 6]
def baseStart_6589921 : Nat := 118140960795 + 6589921 * 2 ^ 59
def prefixEnd_6589921 : Nat := 4983230072969 + 3 ^ 40 * 6589921 * 2
def baseEnd_6589921 : Nat := 375977438684179626386779

theorem tailTrace_6589921 : CollatzResearch.WordTrace tailWord_6589921 prefixEnd_6589921 375977438684179626386779 := by
  unfold tailWord_6589921
  simp only [CollatzResearch.WordTrace]
  refine ⟨240354164758849160748753617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160236109839232773832502411 240354164758849160748753617)
  ·
    refine ⟨180265623569136870561565213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240354164758849160748753617 180265623569136870561565213)
    ·
      refine ⟨67599608838426326460586955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180265623569136870561565213 67599608838426326460586955)
      ·
        refine ⟨101399413257639489690880433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67599608838426326460586955 101399413257639489690880433)
        ·
          refine ⟨76049559943229617268160325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101399413257639489690880433 76049559943229617268160325)
          ·
            refine ⟨14259292489355553237780061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76049559943229617268160325 14259292489355553237780061)
            ·
              refine ⟨5347234683508332464167523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14259292489355553237780061 5347234683508332464167523)
              ·
                refine ⟨8020852025262498696251285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347234683508332464167523 8020852025262498696251285)
                ·
                  refine ⟨375977438684179626386779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8020852025262498696251285 375977438684179626386779)
                  ·
                    rfl

theorem cell23_6589921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 6].length) (baseStart_6589921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589921 prefixEnd_6589921 := by exact prefixLift 6589921
  have htrace : WordTrace (prefixWord ++ tailWord_6589921) baseStart_6589921 baseEnd_6589921 := by
    simpa [prefixWord, tailWord_6589921, baseEnd_6589921] using wordTrace_append hprefix tailTrace_6589921
  have hstable : (prefixWord ++ tailWord_6589921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589921).length < 2 ^ (prefixWord ++ tailWord_6589921).sum := by decide
  have hdescent : baseEnd_6589921 < baseStart_6589921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589972 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 6]
def baseStart_6589972 : Nat := 118140960795 + 6589972 * 2 ^ 59
def prefixEnd_6589972 : Nat := 4983230072969 + 3 ^ 40 * 6589972 * 2
def baseEnd_6589972 : Nat := 375980348407888437549253

theorem tailTrace_6589972 : CollatzResearch.WordTrace tailWord_6589972 prefixEnd_6589972 375980348407888437549253 := by
  unfold tailWord_6589972
  simp only [CollatzResearch.WordTrace]
  refine ⟨120178012440832198229430085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160237349921109597639240113 120178012440832198229430085)
  ·
    refine ⟨22533377332656037168018141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120178012440832198229430085 22533377332656037168018141)
    ·
      refine ⟨8450016499746013938006803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22533377332656037168018141 8450016499746013938006803)
      ·
        refine ⟨12675024749619020907010205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8450016499746013938006803 12675024749619020907010205)
        ·
          refine ⟨4753134281107132840128827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12675024749619020907010205 4753134281107132840128827)
          ·
            refine ⟨7129701421660699260193241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753134281107132840128827 7129701421660699260193241)
            ·
              refine ⟨5347276066245524445144931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7129701421660699260193241 5347276066245524445144931)
              ·
                refine ⟨8020914099368286667717397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347276066245524445144931 8020914099368286667717397)
                ·
                  refine ⟨375980348407888437549253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8020914099368286667717397 375980348407888437549253)
                  ·
                    rfl

theorem cell23_6589972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_6589972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589972 prefixEnd_6589972 := by exact prefixLift 6589972
  have htrace : WordTrace (prefixWord ++ tailWord_6589972) baseStart_6589972 baseEnd_6589972 := by
    simpa [prefixWord, tailWord_6589972, baseEnd_6589972] using wordTrace_append hprefix tailTrace_6589972
  have hstable : (prefixWord ++ tailWord_6589972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589972).length < 2 ^ (prefixWord ++ tailWord_6589972).sum := by decide
  have hdescent : baseEnd_6589972 < baseStart_6589972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6589994 : List Nat := [3, 1, 4, 1, 1, 1, 1, 11]
def baseStart_6589994 : Nat := 118140960795 + 6589994 * 2 ^ 59
def prefixEnd_6589994 : Nat := 4983230072969 + 3 ^ 40 * 6589994 * 2
def baseEnd_6589994 : Nat := 125327201194273883402525

theorem tailTrace_6589994 : CollatzResearch.WordTrace tailWord_6589994 prefixEnd_6589994 125327201194273883402525 := by
  unfold tailWord_6589994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60089206821896173554040259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160237884858389796144107357 60089206821896173554040259)
  ·
    refine ⟨90133810232844260331060389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60089206821896173554040259 90133810232844260331060389)
    ·
      refine ⟨16900089418658298812073823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90133810232844260331060389 16900089418658298812073823)
      ·
        refine ⟨25350134127987448218110735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16900089418658298812073823 25350134127987448218110735)
        ·
          refine ⟨38025201191981172327166103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25350134127987448218110735 38025201191981172327166103)
          ·
            refine ⟨57037801787971758490749155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38025201191981172327166103 57037801787971758490749155)
            ·
              refine ⟨85556702681957637736123733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57037801787971758490749155 85556702681957637736123733)
              ·
                refine ⟨125327201194273883402525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 85556702681957637736123733 125327201194273883402525)
                ·
                  rfl

theorem cell23_6589994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 11].length) (baseStart_6589994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6589994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6589994 prefixEnd_6589994 := by exact prefixLift 6589994
  have htrace : WordTrace (prefixWord ++ tailWord_6589994) baseStart_6589994 baseEnd_6589994 := by
    simpa [prefixWord, tailWord_6589994, baseEnd_6589994] using wordTrace_append hprefix tailTrace_6589994
  have hstable : (prefixWord ++ tailWord_6589994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6589994).length < 2 ^ (prefixWord ++ tailWord_6589994).sum := by decide
  have hdescent : baseEnd_6589994 < baseStart_6589994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6589994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590045 : List Nat := [1, 4, 4, 2, 1, 1, 3, 7]
def baseStart_6590045 : Nat := 118140960795 + 6590045 * 2 ^ 59
def prefixEnd_6590045 : Nat := 4983230072969 + 3 ^ 40 * 6590045 * 2
def baseEnd_6590045 : Nat := 125328171102176820456683

theorem tailTrace_6590045 : CollatzResearch.WordTrace tailWord_6590045 prefixEnd_6590045 125328171102176820456683 := by
  unfold tailWord_6590045
  simp only [CollatzResearch.WordTrace]
  refine ⟨240358687410399929926267589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160239124940266619950845059 240358687410399929926267589)
  ·
    refine ⟨45067253889449986861175173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240358687410399929926267589 45067253889449986861175173)
    ·
      refine ⟨8450110104271872536470345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45067253889449986861175173 8450110104271872536470345)
      ·
        refine ⟨6337582578203904402352759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8450110104271872536470345 6337582578203904402352759)
        ·
          refine ⟨9506373867305856603529139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6337582578203904402352759 9506373867305856603529139)
          ·
            refine ⟨14259560800958784905293709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506373867305856603529139 14259560800958784905293709)
            ·
              refine ⟨5347335300359544339485141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14259560800958784905293709 5347335300359544339485141)
              ·
                refine ⟨125328171102176820456683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5347335300359544339485141 125328171102176820456683)
                ·
                  rfl

theorem cell23_6590045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 7].length) (baseStart_6590045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590045 prefixEnd_6590045 := by exact prefixLift 6590045
  have htrace : WordTrace (prefixWord ++ tailWord_6590045) baseStart_6590045 baseEnd_6590045 := by
    simpa [prefixWord, tailWord_6590045, baseEnd_6590045] using wordTrace_append hprefix tailTrace_6590045
  have hstable : (prefixWord ++ tailWord_6590045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590045).length < 2 ^ (prefixWord ++ tailWord_6590045).sum := by decide
  have hdescent : baseEnd_6590045 < baseStart_6590045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590048 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 1, 3, 2]
def baseStart_6590048 : Nat := 118140960795 + 6590048 * 2 ^ 59
def prefixEnd_6590048 : Nat := 4983230072969 + 3 ^ 40 * 6590048 * 2
def baseEnd_6590048 : Nat := 3383862160200737640592927

theorem tailTrace_6590048 : CollatzResearch.WordTrace tailWord_6590048 prefixEnd_6590048 3383862160200737640592927 := by
  unfold tailWord_6590048
  simp only [CollatzResearch.WordTrace]
  refine ⟨120179398414694530719313399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160239197886259374292417865 120179398414694530719313399)
  ·
    refine ⟨180269097622041796078970099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120179398414694530719313399 180269097622041796078970099)
    ·
      refine ⟨270403646433062694118455149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180269097622041796078970099 270403646433062694118455149)
      ·
        refine ⟨101401367412398510294420681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270403646433062694118455149 101401367412398510294420681)
        ·
          refine ⟨76051025559298882720815511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101401367412398510294420681 76051025559298882720815511)
          ·
            refine ⟨114076538338948324081223267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76051025559298882720815511 114076538338948324081223267)
            ·
              refine ⟨171114807508422486121834901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114076538338948324081223267 171114807508422486121834901)
              ·
                refine ⟨8021006601957304036961011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171114807508422486121834901 8021006601957304036961011)
                ·
                  refine ⟨12031509902935956055441517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8021006601957304036961011 12031509902935956055441517)
                  ·
                    refine ⟨4511816213600983520790569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12031509902935956055441517 4511816213600983520790569)
                    ·
                      refine ⟨3383862160200737640592927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511816213600983520790569 3383862160200737640592927)
                      ·
                        rfl

theorem cell23_6590048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_6590048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590048 prefixEnd_6590048 := by exact prefixLift 6590048
  have htrace : WordTrace (prefixWord ++ tailWord_6590048) baseStart_6590048 baseEnd_6590048 := by
    simpa [prefixWord, tailWord_6590048, baseEnd_6590048] using wordTrace_append hprefix tailTrace_6590048
  have hstable : (prefixWord ++ tailWord_6590048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590048).length < 2 ^ (prefixWord ++ tailWord_6590048).sum := by decide
  have hdescent : baseEnd_6590048 < baseStart_6590048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590124 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_6590124 : Nat := 118140960795 + 6590124 * 2 ^ 59
def prefixEnd_6590124 : Nat := 4983230072969 + 3 ^ 40 * 6590124 * 2
def baseEnd_6590124 : Nat := 3383901184730479343242577

theorem tailTrace_6590124 : CollatzResearch.WordTrace tailWord_6590124 prefixEnd_6590124 3383901184730479343242577 := by
  unfold tailWord_6590124
  simp only [CollatzResearch.WordTrace]
  refine ⟨120180784388556863209196713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160241045851409150945595617 120180784388556863209196713)
  ·
    refine ⟨90135588291417647406897535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120180784388556863209196713 90135588291417647406897535)
    ·
      refine ⟨135203382437126471110346303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90135588291417647406897535 135203382437126471110346303)
      ·
        refine ⟨202805073655689706665519455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135203382437126471110346303 202805073655689706665519455)
        ·
          refine ⟨304207610483534559998279183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202805073655689706665519455 304207610483534559998279183)
          ·
            refine ⟨456311415725301839997418775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304207610483534559998279183 456311415725301839997418775)
            ·
              refine ⟨684467123587952759996128163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456311415725301839997418775 684467123587952759996128163)
              ·
                refine ⟨1026700685381929139994192245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684467123587952759996128163 1026700685381929139994192245)
                ·
                  refine ⟨96253189254555856874455523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1026700685381929139994192245 96253189254555856874455523)
                  ·
                    refine ⟨144379783881833785311683285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96253189254555856874455523 144379783881833785311683285)
                    ·
                      refine ⟨3383901184730479343242577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144379783881833785311683285 3383901184730479343242577)
                      ·
                        rfl

theorem cell23_6590124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_6590124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590124 prefixEnd_6590124 := by exact prefixLift 6590124
  have htrace : WordTrace (prefixWord ++ tailWord_6590124) baseStart_6590124 baseEnd_6590124 := by
    simpa [prefixWord, tailWord_6590124, baseEnd_6590124] using wordTrace_append hprefix tailTrace_6590124
  have hstable : (prefixWord ++ tailWord_6590124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590124).length < 2 ^ (prefixWord ++ tailWord_6590124).sum := by decide
  have hdescent : baseEnd_6590124 < baseStart_6590124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590131 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 2, 5]
def baseStart_6590131 : Nat := 118140960795 + 6590131 * 2 ^ 59
def prefixEnd_6590131 : Nat := 4983230072969 + 3 ^ 40 * 6590131 * 2
def baseEnd_6590131 : Nat := 1127968259698353605285015

theorem tailTrace_6590131 : CollatzResearch.WordTrace tailWord_6590131 prefixEnd_6590131 1127968259698353605285015 := by
  unfold tailWord_6590131
  simp only [CollatzResearch.WordTrace]
  refine ⟨240361824088088366613898247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160241216058725577742598831 240361824088088366613898247)
  ·
    refine ⟨360542736132132549920847371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240361824088088366613898247 360542736132132549920847371)
    ·
      refine ⟨540814104198198824881271057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360542736132132549920847371 540814104198198824881271057)
      ·
        refine ⟨405610578148649118660953293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540814104198198824881271057 405610578148649118660953293)
        ·
          refine ⟨152103966805743419497857485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405610578148649118660953293 152103966805743419497857485)
          ·
            refine ⟨57038987552153782311696557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152103966805743419497857485 57038987552153782311696557)
            ·
              refine ⟨21389620332057668366886209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57038987552153782311696557 21389620332057668366886209)
              ·
                refine ⟨16042215249043251275164657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21389620332057668366886209 16042215249043251275164657)
                ·
                  refine ⟨12031661436782438456373493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16042215249043251275164657 12031661436782438456373493)
                  ·
                    refine ⟨1127968259698353605285015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12031661436782438456373493 1127968259698353605285015)
                    ·
                      rfl

theorem cell23_6590131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 5].length) (baseStart_6590131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590131 prefixEnd_6590131 := by exact prefixLift 6590131
  have htrace : WordTrace (prefixWord ++ tailWord_6590131) baseStart_6590131 baseEnd_6590131 := by
    simpa [prefixWord, tailWord_6590131, baseEnd_6590131] using wordTrace_append hprefix tailTrace_6590131
  have hstable : (prefixWord ++ tailWord_6590131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590131).length < 2 ^ (prefixWord ++ tailWord_6590131).sum := by decide
  have hdescent : baseEnd_6590131 < baseStart_6590131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590135 : List Nat := [1, 1, 3, 1, 5, 2, 3, 2, 5]
def baseStart_6590135 : Nat := 118140960795 + 6590135 * 2 ^ 59
def prefixEnd_6590135 : Nat := 4983230072969 + 3 ^ 40 * 6590135 * 2
def baseEnd_6590135 : Nat := 375989648113075422245003

theorem tailTrace_6590135 : CollatzResearch.WordTrace tailWord_6590135 prefixEnd_6590135 375989648113075422245003 := by
  unfold tailWord_6590135
  simp only [CollatzResearch.WordTrace]
  refine ⟨240361969980073875297043859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160241313320049250198029239 240361969980073875297043859)
  ·
    refine ⟨360542954970110812945565789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240361969980073875297043859 360542954970110812945565789)
    ·
      refine ⟨135203608113791554854587171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360542954970110812945565789 135203608113791554854587171)
      ·
        refine ⟨202805412170687332281880757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135203608113791554854587171 202805412170687332281880757)
        ·
          refine ⟨19013007391001937401426321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202805412170687332281880757 19013007391001937401426321)
          ·
            refine ⟨14259755543251453051069741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19013007391001937401426321 14259755543251453051069741)
            ·
              refine ⟨5347408328719294894151153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14259755543251453051069741 5347408328719294894151153)
              ·
                refine ⟨4010556246539471170613365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5347408328719294894151153 4010556246539471170613365)
                ·
                  refine ⟨375989648113075422245003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4010556246539471170613365 375989648113075422245003)
                  ·
                    rfl

theorem cell23_6590135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 5].length) (baseStart_6590135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590135 prefixEnd_6590135 := by exact prefixLift 6590135
  have htrace : WordTrace (prefixWord ++ tailWord_6590135) baseStart_6590135 baseEnd_6590135 := by
    simpa [prefixWord, tailWord_6590135, baseEnd_6590135] using wordTrace_append hprefix tailTrace_6590135
  have hstable : (prefixWord ++ tailWord_6590135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590135).length < 2 ^ (prefixWord ++ tailWord_6590135).sum := by decide
  have hdescent : baseEnd_6590135 < baseStart_6590135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590141 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_6590141 : Nat := 118140960795 + 6590141 * 2 ^ 59
def prefixEnd_6590141 : Nat := 4983230072969 + 3 ^ 40 * 6590141 * 2
def baseEnd_6590141 : Nat := 3383909913901605776729999

theorem tailTrace_6590141 : CollatzResearch.WordTrace tailWord_6590141 prefixEnd_6590141 3383909913901605776729999 := by
  unfold tailWord_6590141
  simp only [CollatzResearch.WordTrace]
  refine ⟨240362188818052138321762277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160241459212034758881174851 240362188818052138321762277)
  ·
    refine ⟨45067910403384775935330427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240362188818052138321762277 45067910403384775935330427)
    ·
      refine ⟨67601865605077163902995641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45067910403384775935330427 67601865605077163902995641)
      ·
        refine ⟨50701399203807872927246731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67601865605077163902995641 50701399203807872927246731)
        ·
          refine ⟨76052098805711809390870097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50701399203807872927246731 76052098805711809390870097)
          ·
            refine ⟨57039074104283857043152573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76052098805711809390870097 57039074104283857043152573)
            ·
              refine ⟨21389652789106446391182215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57039074104283857043152573 21389652789106446391182215)
              ·
                refine ⟨32084479183659669586773323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21389652789106446391182215 32084479183659669586773323)
                ·
                  refine ⟨48126718775489504380159985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32084479183659669586773323 48126718775489504380159985)
                  ·
                    refine ⟨36095039081617128285119989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48126718775489504380159985 36095039081617128285119989)
                    ·
                      refine ⟨3383909913901605776729999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36095039081617128285119989 3383909913901605776729999)
                      ·
                        rfl

theorem cell23_6590141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_6590141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590141 prefixEnd_6590141 := by exact prefixLift 6590141
  have htrace : WordTrace (prefixWord ++ tailWord_6590141) baseStart_6590141 baseEnd_6590141 := by
    simpa [prefixWord, tailWord_6590141, baseEnd_6590141] using wordTrace_append hprefix tailTrace_6590141
  have hstable : (prefixWord ++ tailWord_6590141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590141).length < 2 ^ (prefixWord ++ tailWord_6590141).sum := by decide
  have hdescent : baseEnd_6590141 < baseStart_6590141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590151 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_6590151 : Nat := 118140960795 + 6590151 * 2 ^ 59
def prefixEnd_6590151 : Nat := 4983230072969 + 3 ^ 40 * 6590151 * 2
def baseEnd_6590151 : Nat := 3383915048708150737604953

theorem tailTrace_6590151 : CollatzResearch.WordTrace tailWord_6590151 prefixEnd_6590151 3383915048708150737604953 := by
  unfold tailWord_6590151
  simp only [CollatzResearch.WordTrace]
  refine ⟨240362553548015910029626307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160241702365343940019750871 240362553548015910029626307)
  ·
    refine ⟨360543830322023865044439461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240362553548015910029626307 360543830322023865044439461)
    ·
      refine ⟨67601968185379474695832399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360543830322023865044439461 67601968185379474695832399)
      ·
        refine ⟨101402952278069212043748599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67601968185379474695832399 101402952278069212043748599)
        ·
          refine ⟨152104428417103818065622899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101402952278069212043748599 152104428417103818065622899)
          ·
            refine ⟨228156642625655727098434349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152104428417103818065622899 228156642625655727098434349)
            ·
              refine ⟨85558740984620897661912881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228156642625655727098434349 85558740984620897661912881)
              ·
                refine ⟨64169055738465673246434661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85558740984620897661912881 64169055738465673246434661)
                ·
                  refine ⟨12031697950962313733706499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64169055738465673246434661 12031697950962313733706499)
                  ·
                    refine ⟨18047546926443470600559749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12031697950962313733706499 18047546926443470600559749)
                    ·
                      refine ⟨3383915048708150737604953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18047546926443470600559749 3383915048708150737604953)
                      ·
                        rfl

theorem cell23_6590151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_6590151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590151 prefixEnd_6590151 := by exact prefixLift 6590151
  have htrace : WordTrace (prefixWord ++ tailWord_6590151) baseStart_6590151 baseEnd_6590151 := by
    simpa [prefixWord, tailWord_6590151, baseEnd_6590151] using wordTrace_append hprefix tailTrace_6590151
  have hstable : (prefixWord ++ tailWord_6590151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590151).length < 2 ^ (prefixWord ++ tailWord_6590151).sum := by decide
  have hdescent : baseEnd_6590151 < baseStart_6590151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590168 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_6590168 : Nat := 118140960795 + 6590168 * 2 ^ 59
def prefixEnd_6590168 : Nat := 4983230072969 + 3 ^ 40 * 6590168 * 2
def baseEnd_6590168 : Nat := 3383923777879277171092375

theorem tailTrace_6590168 : CollatzResearch.WordTrace tailWord_6590168 prefixEnd_6590168 3383923777879277171092375 := by
  unfold tailWord_6590168
  simp only [CollatzResearch.WordTrace]
  refine ⟨120181586794477160966497579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160242115725969547955330105 120181586794477160966497579)
  ·
    refine ⟨180272380191715741449746369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120181586794477160966497579 180272380191715741449746369)
    ·
      refine ⟨135204285143786806087309777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180272380191715741449746369 135204285143786806087309777)
      ·
        refine ⟨101403213857840104565482333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135204285143786806087309777 101403213857840104565482333)
        ·
          refine ⟨38026205196690039212055875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101403213857840104565482333 38026205196690039212055875)
          ·
            refine ⟨57039307795035058818083813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38026205196690039212055875 57039307795035058818083813)
            ·
              refine ⟨10694870211569073528390715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57039307795035058818083813 10694870211569073528390715)
              ·
                refine ⟨16042305317353610292586073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10694870211569073528390715 16042305317353610292586073)
                ·
                  refine ⟨12031728988015207719439555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16042305317353610292586073 12031728988015207719439555)
                  ·
                    refine ⟨18047593482022811579159333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12031728988015207719439555 18047593482022811579159333)
                    ·
                      refine ⟨3383923777879277171092375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18047593482022811579159333 3383923777879277171092375)
                      ·
                        rfl

theorem cell23_6590168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_6590168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590168 prefixEnd_6590168 := by exact prefixLift 6590168
  have htrace : WordTrace (prefixWord ++ tailWord_6590168) baseStart_6590168 baseEnd_6590168 := by
    simpa [prefixWord, tailWord_6590168, baseEnd_6590168] using wordTrace_append hprefix tailTrace_6590168
  have hstable : (prefixWord ++ tailWord_6590168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590168).length < 2 ^ (prefixWord ++ tailWord_6590168).sum := by decide
  have hdescent : baseEnd_6590168 < baseStart_6590168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590181 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6590181 : Nat := 118140960795 + 6590181 * 2 ^ 59
def prefixEnd_6590181 : Nat := 4983230072969 + 3 ^ 40 * 6590181 * 2
def baseEnd_6590181 : Nat := 3383930453127785620229815

theorem tailTrace_6590181 : CollatzResearch.WordTrace tailWord_6590181 prefixEnd_6590181 3383930453127785620229815 := by
  unfold tailWord_6590181
  simp only [CollatzResearch.WordTrace]
  refine ⟨240363647737907225153218397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160242431825271483435478931 240363647737907225153218397)
  ·
    refine ⟨90136367901715209432456899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240363647737907225153218397 90136367901715209432456899)
    ·
      refine ⟨135204551852572814148685349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90136367901715209432456899 135204551852572814148685349)
      ·
        refine ⟨25350853472357402652878503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135204551852572814148685349 25350853472357402652878503)
        ·
          refine ⟨38026280208536103979317755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25350853472357402652878503 38026280208536103979317755)
          ·
            refine ⟨57039420312804155968976633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38026280208536103979317755 57039420312804155968976633)
            ·
              refine ⟨42779565234603116976732475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57039420312804155968976633 42779565234603116976732475)
              ·
                refine ⟨64169347851904675465098713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42779565234603116976732475 64169347851904675465098713)
                ·
                  refine ⟨48127010888928506598824035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64169347851904675465098713 48127010888928506598824035)
                  ·
                    refine ⟨72190516333392759898236053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48127010888928506598824035 72190516333392759898236053)
                    ·
                      refine ⟨3383930453127785620229815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72190516333392759898236053 3383930453127785620229815)
                      ·
                        rfl

theorem cell23_6590181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6590181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590181 prefixEnd_6590181 := by exact prefixLift 6590181
  have htrace : WordTrace (prefixWord ++ tailWord_6590181) baseStart_6590181 baseEnd_6590181 := by
    simpa [prefixWord, tailWord_6590181, baseEnd_6590181] using wordTrace_append hprefix tailTrace_6590181
  have hstable : (prefixWord ++ tailWord_6590181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590181).length < 2 ^ (prefixWord ++ tailWord_6590181).sum := by decide
  have hdescent : baseEnd_6590181 < baseStart_6590181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590188 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_6590188 : Nat := 118140960795 + 6590188 * 2 ^ 59
def prefixEnd_6590188 : Nat := 4983230072969 + 3 ^ 40 * 6590188 * 2
def baseEnd_6590188 : Nat := 3383934047492367092842283

theorem tailTrace_6590188 : CollatzResearch.WordTrace tailWord_6590188 prefixEnd_6590188 3383934047492367092842283 := by
  unfold tailWord_6590188
  simp only [CollatzResearch.WordTrace]
  refine ⟨120181951524440932674361609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160242602032587910232482145 120181951524440932674361609)
  ·
    refine ⟨90136463643330699505771207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120181951524440932674361609 90136463643330699505771207)
    ·
      refine ⟨135204695464996049258656811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90136463643330699505771207 135204695464996049258656811)
      ·
        refine ⟨202807043197494073887985217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135204695464996049258656811 202807043197494073887985217)
        ·
          refine ⟨152105282398120555415988913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202807043197494073887985217 152105282398120555415988913)
          ·
            refine ⟨114078961798590416561991685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152105282398120555415988913 114078961798590416561991685)
            ·
              refine ⟨21389805337235703105373441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114078961798590416561991685 21389805337235703105373441)
              ·
                refine ⟨16042354002926777329030081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21389805337235703105373441 16042354002926777329030081)
                ·
                  refine ⟨12031765502195082996772561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16042354002926777329030081 12031765502195082996772561)
                  ·
                    refine ⟨9023824126646312247579421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12031765502195082996772561 9023824126646312247579421)
                    ·
                      refine ⟨3383934047492367092842283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023824126646312247579421 3383934047492367092842283)
                      ·
                        rfl

theorem cell23_6590188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_6590188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590188 prefixEnd_6590188 := by exact prefixLift 6590188
  have htrace : WordTrace (prefixWord ++ tailWord_6590188) baseStart_6590188 baseEnd_6590188 := by
    simpa [prefixWord, tailWord_6590188, baseEnd_6590188] using wordTrace_append hprefix tailTrace_6590188
  have hstable : (prefixWord ++ tailWord_6590188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590188).length < 2 ^ (prefixWord ++ tailWord_6590188).sum := by decide
  have hdescent : baseEnd_6590188 < baseStart_6590188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590201 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 3]
def baseStart_6590201 : Nat := 118140960795 + 6590201 * 2 ^ 59
def prefixEnd_6590201 : Nat := 4983230072969 + 3 ^ 40 * 6590201 * 2
def baseEnd_6590201 : Nat := 3383940722740875541979723

theorem tailTrace_6590201 : CollatzResearch.WordTrace tailWord_6590201 prefixEnd_6590201 3383940722740875541979723 := by
  unfold tailWord_6590201
  simp only [CollatzResearch.WordTrace]
  refine ⟨240364377197834768568946457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160242918131889845712630971 240364377197834768568946457)
  ·
    refine ⟨180273282898376076426709843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240364377197834768568946457 180273282898376076426709843)
    ·
      refine ⟨270409924347564114640064765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180273282898376076426709843 270409924347564114640064765)
      ·
        refine ⟨101403721630336542990024287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270409924347564114640064765 101403721630336542990024287)
        ·
          refine ⟨152105582445504814485036431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101403721630336542990024287 152105582445504814485036431)
          ·
            refine ⟨228158373668257221727554647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152105582445504814485036431 228158373668257221727554647)
            ·
              refine ⟨342237560502385832591331971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228158373668257221727554647 342237560502385832591331971)
              ·
                refine ⟨513356340753578748886997957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342237560502385832591331971 513356340753578748886997957)
                ·
                  refine ⟨96254313891296015416312117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513356340753578748886997957 96254313891296015416312117)
                  ·
                    refine ⟨9023841927309001445279261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96254313891296015416312117 9023841927309001445279261)
                    ·
                      refine ⟨3383940722740875541979723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023841927309001445279261 3383940722740875541979723)
                      ·
                        rfl

theorem cell23_6590201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_6590201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590201 prefixEnd_6590201 := by exact prefixLift 6590201
  have htrace : WordTrace (prefixWord ++ tailWord_6590201) baseStart_6590201 baseEnd_6590201 := by
    simpa [prefixWord, tailWord_6590201, baseEnd_6590201] using wordTrace_append hprefix tailTrace_6590201
  have hstable : (prefixWord ++ tailWord_6590201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590201).length < 2 ^ (prefixWord ++ tailWord_6590201).sum := by decide
  have hdescent : baseEnd_6590201 < baseStart_6590201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590252 : List Nat := [2, 2, 1, 1, 1, 5, 2, 4, 1, 1, 3]
def baseStart_6590252 : Nat := 118140960795 + 6590252 * 2 ^ 59
def prefixEnd_6590252 : Nat := 4983230072969 + 3 ^ 40 * 6590252 * 2
def baseEnd_6590252 : Nat := 3383966910254254842441989

theorem tailTrace_6590252 : CollatzResearch.WordTrace tailWord_6590252 prefixEnd_6590252 3383966910254254842441989 := by
  unfold tailWord_6590252
  simp only [CollatzResearch.WordTrace]
  refine ⟨120183118660325002139526505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160244158213766669519368673 120183118660325002139526505)
  ·
    refine ⟨90137338995243751604644879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120183118660325002139526505 90137338995243751604644879)
    ·
      refine ⟨135206008492865627406967319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90137338995243751604644879 135206008492865627406967319)
      ·
        refine ⟨202809012739298441110450979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135206008492865627406967319 202809012739298441110450979)
        ·
          refine ⟨304213519108947661665676469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202809012739298441110450979 304213519108947661665676469)
          ·
            refine ⟨28520017416463843281157169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 304213519108947661665676469 28520017416463843281157169)
            ·
              refine ⟨21390013062347882460867877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28520017416463843281157169 21390013062347882460867877)
              ·
                refine ⟨4010627449190227961412727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21390013062347882460867877 4010627449190227961412727)
                ·
                  refine ⟨6015941173785341942119091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010627449190227961412727 6015941173785341942119091)
                  ·
                    refine ⟨9023911760678012913178637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6015941173785341942119091 9023911760678012913178637)
                    ·
                      refine ⟨3383966910254254842441989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9023911760678012913178637 3383966910254254842441989)
                      ·
                        rfl

theorem cell23_6590252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_6590252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590252 prefixEnd_6590252 := by exact prefixLift 6590252
  have htrace : WordTrace (prefixWord ++ tailWord_6590252) baseStart_6590252 baseEnd_6590252 := by
    simpa [prefixWord, tailWord_6590252, baseEnd_6590252] using wordTrace_append hprefix tailTrace_6590252
  have hstable : (prefixWord ++ tailWord_6590252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590252).length < 2 ^ (prefixWord ++ tailWord_6590252).sum := by decide
  have hdescent : baseEnd_6590252 < baseStart_6590252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590262 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6590262 : Nat := 118140960795 + 6590262 * 2 ^ 59
def prefixEnd_6590262 : Nat := 4983230072969 + 3 ^ 40 * 6590262 * 2
def baseEnd_6590262 : Nat := 3383972045060799803316943

theorem tailTrace_6590262 : CollatzResearch.WordTrace tailWord_6590262 prefixEnd_6590262 3383972045060799803316943 := by
  unfold tailWord_6590262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15022912628163360999182315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160244401367075850657944693 15022912628163360999182315)
  ·
    refine ⟨22534368942245041498773473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15022912628163360999182315 22534368942245041498773473)
    ·
      refine ⟨16900776706683781124080105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22534368942245041498773473 16900776706683781124080105)
      ·
        refine ⟨12675582530012835843060079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16900776706683781124080105 12675582530012835843060079)
        ·
          refine ⟨19013373795019253764590119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12675582530012835843060079 19013373795019253764590119)
          ·
            refine ⟨28520060692528880646885179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19013373795019253764590119 28520060692528880646885179)
            ·
              refine ⟨42780091038793320970327769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28520060692528880646885179 42780091038793320970327769)
              ·
                refine ⟨32085068279094990727745827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42780091038793320970327769 32085068279094990727745827)
                ·
                  refine ⟨48127602418642486091618741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32085068279094990727745827 48127602418642486091618741)
                  ·
                    refine ⟨4511962726747733071089257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48127602418642486091618741 4511962726747733071089257)
                    ·
                      refine ⟨3383972045060799803316943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4511962726747733071089257 3383972045060799803316943)
                      ·
                        rfl

theorem cell23_6590262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6590262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590262 prefixEnd_6590262 := by exact prefixLift 6590262
  have htrace : WordTrace (prefixWord ++ tailWord_6590262) baseStart_6590262 baseEnd_6590262 := by
    simpa [prefixWord, tailWord_6590262, baseEnd_6590262] using wordTrace_append hprefix tailTrace_6590262
  have hstable : (prefixWord ++ tailWord_6590262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590262).length < 2 ^ (prefixWord ++ tailWord_6590262).sum := by decide
  have hdescent : baseEnd_6590262 < baseStart_6590262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590268 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_6590268 : Nat := 118140960795 + 6590268 * 2 ^ 59
def prefixEnd_6590268 : Nat := 4983230072969 + 3 ^ 40 * 6590268 * 2
def baseEnd_6590268 : Nat := 1127991708648242259947305

theorem tailTrace_6590268 : CollatzResearch.WordTrace tailWord_6590268 prefixEnd_6590268 1127991708648242259947305 := by
  unfold tailWord_6590268
  simp only [CollatzResearch.WordTrace]
  refine ⟨120183410444296019505817729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160244547259061359341090305 120183410444296019505817729)
  ·
    refine ⟨90137557833222014629363297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120183410444296019505817729 90137557833222014629363297)
    ·
      refine ⟨67603168374916510972022473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90137557833222014629363297 67603168374916510972022473)
      ·
        refine ⟨50702376281187383229016855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67603168374916510972022473 50702376281187383229016855)
        ·
          refine ⟨76053564421781074843525283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50702376281187383229016855 76053564421781074843525283)
          ·
            refine ⟨114080346632671612265287925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76053564421781074843525283 114080346632671612265287925)
            ·
              refine ⟨10695032496812963649870743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114080346632671612265287925 10695032496812963649870743)
              ·
                refine ⟨16042548745219445474806115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10695032496812963649870743 16042548745219445474806115)
                ·
                  refine ⟨24063823117829168212209173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16042548745219445474806115 24063823117829168212209173)
                  ·
                    refine ⟨1127991708648242259947305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24063823117829168212209173 1127991708648242259947305)
                    ·
                      rfl

theorem cell23_6590268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_6590268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590268 prefixEnd_6590268 := by exact prefixLift 6590268
  have htrace : WordTrace (prefixWord ++ tailWord_6590268) baseStart_6590268 baseEnd_6590268 := by
    simpa [prefixWord, tailWord_6590268, baseEnd_6590268] using wordTrace_append hprefix tailTrace_6590268
  have hstable : (prefixWord ++ tailWord_6590268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590268).length < 2 ^ (prefixWord ++ tailWord_6590268).sum := by decide
  have hdescent : baseEnd_6590268 < baseStart_6590268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590275 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 4]
def baseStart_6590275 : Nat := 118140960795 + 6590275 * 2 ^ 59
def prefixEnd_6590275 : Nat := 4983230072969 + 3 ^ 40 * 6590275 * 2
def baseEnd_6590275 : Nat := 3383978720309308252454383

theorem tailTrace_6590275 : CollatzResearch.WordTrace tailWord_6590275 prefixEnd_6590275 3383978720309308252454383 := by
  unfold tailWord_6590275
  simp only [CollatzResearch.WordTrace]
  refine ⟨240367076199566679207140279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160244717466377786138093519 240367076199566679207140279)
  ·
    refine ⟨360550614299350018810710419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240367076199566679207140279 360550614299350018810710419)
    ·
      refine ⟨540825921449025028216065629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360550614299350018810710419 540825921449025028216065629)
      ·
        refine ⟨202809720543384385581024611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540825921449025028216065629 202809720543384385581024611)
        ·
          refine ⟨304214580815076578371536917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202809720543384385581024611 304214580815076578371536917)
          ·
            refine ⟨14260058475706714611165793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 304214580815076578371536917 14260058475706714611165793)
            ·
              refine ⟨10695043856780035958374345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14260058475706714611165793 10695043856780035958374345)
              ·
                refine ⟨8021282892585026968780759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10695043856780035958374345 8021282892585026968780759)
                ·
                  refine ⟨12031924338877540453171139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8021282892585026968780759 12031924338877540453171139)
                  ·
                    refine ⟨18047886508316310679756709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12031924338877540453171139 18047886508316310679756709)
                    ·
                      refine ⟨3383978720309308252454383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18047886508316310679756709 3383978720309308252454383)
                      ·
                        rfl

theorem cell23_6590275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_6590275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590275 prefixEnd_6590275 := by exact prefixLift 6590275
  have htrace : WordTrace (prefixWord ++ tailWord_6590275) baseStart_6590275 baseEnd_6590275 := by
    simpa [prefixWord, tailWord_6590275, baseEnd_6590275] using wordTrace_append hprefix tailTrace_6590275
  have hstable : (prefixWord ++ tailWord_6590275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590275).length < 2 ^ (prefixWord ++ tailWord_6590275).sum := by decide
  have hdescent : baseEnd_6590275 < baseStart_6590275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590281 : List Nat := [1, 2, 1, 1, 2, 4, 3, 9]
def baseStart_6590281 : Nat := 118140960795 + 6590281 * 2 ^ 59
def prefixEnd_6590281 : Nat := 4983230072969 + 3 ^ 40 * 6590281 * 2
def baseEnd_6590281 : Nat := 125332659303453156628865

theorem tailTrace_6590281 : CollatzResearch.WordTrace tailWord_6590281 prefixEnd_6590281 125332659303453156628865 := by
  unfold tailWord_6590281
  simp only [CollatzResearch.WordTrace]
  refine ⟨240367295037544942231858697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160244863358363294821239131 240367295037544942231858697)
  ·
    refine ⟨180275471278158706673894023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240367295037544942231858697 180275471278158706673894023)
    ·
      refine ⟨270413206917238060010841035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180275471278158706673894023 270413206917238060010841035)
      ·
        refine ⟨405619810375857090016261553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270413206917238060010841035 405619810375857090016261553)
        ·
          refine ⟨304214857781892817512196165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405619810375857090016261553 304214857781892817512196165)
          ·
            refine ⟨57040285834104903283536781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304214857781892817512196165 57040285834104903283536781)
            ·
              refine ⟨21390107187789338731326293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57040285834104903283536781 21390107187789338731326293)
              ·
                refine ⟨125332659303453156628865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21390107187789338731326293 125332659303453156628865)
                ·
                  rfl

theorem cell23_6590281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 9].length) (baseStart_6590281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590281 prefixEnd_6590281 := by exact prefixLift 6590281
  have htrace : WordTrace (prefixWord ++ tailWord_6590281) baseStart_6590281 baseEnd_6590281 := by
    simpa [prefixWord, tailWord_6590281, baseEnd_6590281] using wordTrace_append hprefix tailTrace_6590281
  have hstable : (prefixWord ++ tailWord_6590281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590281).length < 2 ^ (prefixWord ++ tailWord_6590281).sum := by decide
  have hdescent : baseEnd_6590281 < baseStart_6590281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590295 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_6590295 : Nat := 118140960795 + 6590295 * 2 ^ 59
def prefixEnd_6590295 : Nat := 4983230072969 + 3 ^ 40 * 6590295 * 2
def baseEnd_6590295 : Nat := 3383988989922398174204291

theorem tailTrace_6590295 : CollatzResearch.WordTrace tailWord_6590295 prefixEnd_6590295 3383988989922398174204291 := by
  unfold tailWord_6590295
  simp only [CollatzResearch.WordTrace]
  refine ⟨240367805659494222622868339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160245203772996148415245559 240367805659494222622868339)
  ·
    refine ⟨360551708489241333934302509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240367805659494222622868339 360551708489241333934302509)
    ·
      refine ⟨135206890683465500225363441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360551708489241333934302509 135206890683465500225363441)
      ·
        refine ⟨101405168012599125169022581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135206890683465500225363441 101405168012599125169022581)
        ·
          refine ⟨9506734501181167984595867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101405168012599125169022581 9506734501181167984595867)
          ·
            refine ⟨14260101751771751976893801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506734501181167984595867 14260101751771751976893801)
            ·
              refine ⟨10695076313828813982670351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14260101751771751976893801 10695076313828813982670351)
              ·
                refine ⟨16042614470743220974005527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10695076313828813982670351 16042614470743220974005527)
                ·
                  refine ⟨24063921706114831461008291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16042614470743220974005527 24063921706114831461008291)
                  ·
                    refine ⟨36095882559172247191512437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24063921706114831461008291 36095882559172247191512437)
                    ·
                      refine ⟨3383988989922398174204291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36095882559172247191512437 3383988989922398174204291)
                      ·
                        rfl

theorem cell23_6590295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_6590295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590295 prefixEnd_6590295 := by exact prefixLift 6590295
  have htrace : WordTrace (prefixWord ++ tailWord_6590295) baseStart_6590295 baseEnd_6590295 := by
    simpa [prefixWord, tailWord_6590295, baseEnd_6590295] using wordTrace_append hprefix tailTrace_6590295
  have hstable : (prefixWord ++ tailWord_6590295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590295).length < 2 ^ (prefixWord ++ tailWord_6590295).sum := by decide
  have hdescent : baseEnd_6590295 < baseStart_6590295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590325 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_6590325 : Nat := 118140960795 + 6590325 * 2 ^ 59
def prefixEnd_6590325 : Nat := 4983230072969 + 3 ^ 40 * 6590325 * 2
def baseEnd_6590325 : Nat := 3384004394342033056829153

theorem tailTrace_6590325 : CollatzResearch.WordTrace tailWord_6590325 prefixEnd_6590325 3384004394342033056829153 := by
  unfold tailWord_6590325
  simp only [CollatzResearch.WordTrace]
  refine ⟨240368899849385537746460429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160245933232923691830973619 240368899849385537746460429)
  ·
    refine ⟨90138337443519576654922661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240368899849385537746460429 90138337443519576654922661)
    ·
      refine ⟨16900938270659920622797999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90138337443519576654922661 16900938270659920622797999)
      ·
        refine ⟨25351407405989880934196999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16900938270659920622797999 25351407405989880934196999)
        ·
          refine ⟨38027111108984821401295499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25351407405989880934196999 38027111108984821401295499)
          ·
            refine ⟨57040666663477232101943249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38027111108984821401295499 57040666663477232101943249)
            ·
              refine ⟨42780499997607924076457437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57040666663477232101943249 42780499997607924076457437)
              ·
                refine ⟨16042687499102971528671539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42780499997607924076457437 16042687499102971528671539)
                ·
                  refine ⟨24064031248654457293007309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16042687499102971528671539 24064031248654457293007309)
                  ·
                    refine ⟨9024011718245421484877741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24064031248654457293007309 9024011718245421484877741)
                    ·
                      refine ⟨3384004394342033056829153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9024011718245421484877741 3384004394342033056829153)
                      ·
                        rfl

theorem cell23_6590325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_6590325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590325 prefixEnd_6590325 := by exact prefixLift 6590325
  have htrace : WordTrace (prefixWord ++ tailWord_6590325) baseStart_6590325 baseEnd_6590325 := by
    simpa [prefixWord, tailWord_6590325, baseEnd_6590325] using wordTrace_append hprefix tailTrace_6590325
  have hstable : (prefixWord ++ tailWord_6590325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590325).length < 2 ^ (prefixWord ++ tailWord_6590325).sum := by decide
  have hdescent : baseEnd_6590325 < baseStart_6590325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590326 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6590326 : Nat := 118140960795 + 6590326 * 2 ^ 59
def prefixEnd_6590326 : Nat := 4983230072969 + 3 ^ 40 * 6590326 * 2
def baseEnd_6590326 : Nat := 3384004907822687552916649

theorem tailTrace_6590326 : CollatzResearch.WordTrace tailWord_6590326 prefixEnd_6590326 3384004907822687552916649 := by
  unfold tailWord_6590326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15023058520148869682327927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160245957548254609944831221 15023058520148869682327927)
  ·
    refine ⟨22534587780223304523491891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15023058520148869682327927 22534587780223304523491891)
    ·
      refine ⟨33801881670334956785237837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22534587780223304523491891 33801881670334956785237837)
      ·
        refine ⟨12675705626375608794464189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33801881670334956785237837 12675705626375608794464189)
        ·
          refine ⟨4753389609890853297924071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12675705626375608794464189 4753389609890853297924071)
          ·
            refine ⟨7130084414836279946886107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753389609890853297924071 7130084414836279946886107)
            ·
              refine ⟨10695126622254419920329161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7130084414836279946886107 10695126622254419920329161)
              ·
                refine ⟨8021344966690814940246871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10695126622254419920329161 8021344966690814940246871)
                ·
                  refine ⟨12032017450036222410370307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8021344966690814940246871 12032017450036222410370307)
                  ·
                    refine ⟨18048026175054333615555461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12032017450036222410370307 18048026175054333615555461)
                    ·
                      refine ⟨3384004907822687552916649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18048026175054333615555461 3384004907822687552916649)
                      ·
                        rfl

theorem cell23_6590326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6590326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590326 prefixEnd_6590326 := by exact prefixLift 6590326
  have htrace : WordTrace (prefixWord ++ tailWord_6590326) baseStart_6590326 baseEnd_6590326 := by
    simpa [prefixWord, tailWord_6590326, baseEnd_6590326] using wordTrace_append hprefix tailTrace_6590326
  have hstable : (prefixWord ++ tailWord_6590326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590326).length < 2 ^ (prefixWord ++ tailWord_6590326).sum := by decide
  have hdescent : baseEnd_6590326 < baseStart_6590326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590331 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 8]
def baseStart_6590331 : Nat := 118140960795 + 6590331 * 2 ^ 59
def prefixEnd_6590331 : Nat := 4983230072969 + 3 ^ 40 * 6590331 * 2
def baseEnd_6590331 : Nat := 3384007475225960033354125

theorem tailTrace_6590331 : CollatzResearch.WordTrace tailWord_6590331 prefixEnd_6590331 3384007475225960033354125 := by
  unfold tailWord_6590331
  simp only [CollatzResearch.WordTrace]
  refine ⟨240369118687363800771178847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160246079124909200514119231 240369118687363800771178847)
  ·
    refine ⟨360553678031045701156768271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240369118687363800771178847 360553678031045701156768271)
    ·
      refine ⟨540830517046568551735152407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360553678031045701156768271 540830517046568551735152407)
      ·
        refine ⟨811245775569852827602728611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540830517046568551735152407 811245775569852827602728611)
        ·
          refine ⟨1216868663354779241404092917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811245775569852827602728611 1216868663354779241404092917)
          ·
            refine ⟨114081437189510553881633711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1216868663354779241404092917 114081437189510553881633711)
            ·
              refine ⟨171122155784265830822450567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114081437189510553881633711 171122155784265830822450567)
              ·
                refine ⟨256683233676398746233675851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171122155784265830822450567 256683233676398746233675851)
                ·
                  refine ⟨385024850514598119350513777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256683233676398746233675851 385024850514598119350513777)
                  ·
                    refine ⟨288768637885948589512885333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 385024850514598119350513777 288768637885948589512885333)
                    ·
                      refine ⟨3384007475225960033354125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 288768637885948589512885333 3384007475225960033354125)
                      ·
                        rfl

theorem cell23_6590331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_6590331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590331 prefixEnd_6590331 := by exact prefixLift 6590331
  have htrace : WordTrace (prefixWord ++ tailWord_6590331) baseStart_6590331 baseEnd_6590331 := by
    simpa [prefixWord, tailWord_6590331, baseEnd_6590331] using wordTrace_append hprefix tailTrace_6590331
  have hstable : (prefixWord ++ tailWord_6590331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590331).length < 2 ^ (prefixWord ++ tailWord_6590331).sum := by decide
  have hdescent : baseEnd_6590331 < baseStart_6590331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590360 : List Nat := [2, 1, 2, 6, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6590360 : Nat := 118140960795 + 6590360 * 2 ^ 59
def prefixEnd_6590360 : Nat := 4983230072969 + 3 ^ 40 * 6590360 * 2
def baseEnd_6590360 : Nat := 3384022366164940419891493

theorem tailTrace_6590360 : CollatzResearch.WordTrace tailWord_6590360 prefixEnd_6590360 3384022366164940419891493 := by
  unfold tailWord_6590360
  simp only [CollatzResearch.WordTrace]
  refine ⟨120185088202129369361992267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160246784269505825815989689 120185088202129369361992267)
  ·
    refine ⟨180277632303194054042988401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120185088202129369361992267 180277632303194054042988401)
    ·
      refine ⟨135208224227395540532241301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180277632303194054042988401 135208224227395540532241301)
      ·
        refine ⟨6337885510659165962448811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135208224227395540532241301 6337885510659165962448811)
        ·
          refine ⟨9506828265988748943673217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6337885510659165962448811 9506828265988748943673217)
          ·
            refine ⟨7130121199491561707754913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9506828265988748943673217 7130121199491561707754913)
            ·
              refine ⟨5347590899618671280816185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7130121199491561707754913 5347590899618671280816185)
              ·
                refine ⟨4010693174714003460612139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5347590899618671280816185 4010693174714003460612139)
                ·
                  refine ⟨6016039762071005190918209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010693174714003460612139 6016039762071005190918209)
                  ·
                    refine ⟨4512029821553253893188657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6016039762071005190918209 4512029821553253893188657)
                    ·
                      refine ⟨3384022366164940419891493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512029821553253893188657 3384022366164940419891493)
                      ·
                        rfl

theorem cell23_6590360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6590360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590360 prefixEnd_6590360 := by exact prefixLift 6590360
  have htrace : WordTrace (prefixWord ++ tailWord_6590360) baseStart_6590360 baseEnd_6590360 := by
    simpa [prefixWord, tailWord_6590360, baseEnd_6590360] using wordTrace_append hprefix tailTrace_6590360
  have hstable : (prefixWord ++ tailWord_6590360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590360).length < 2 ^ (prefixWord ++ tailWord_6590360).sum := by decide
  have hdescent : baseEnd_6590360 < baseStart_6590360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590375 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6590375 : Nat := 118140960795 + 6590375 * 2 ^ 59
def prefixEnd_6590375 : Nat := 4983230072969 + 3 ^ 40 * 6590375 * 2
def baseEnd_6590375 : Nat := 1128010022791585953734641

theorem tailTrace_6590375 : CollatzResearch.WordTrace tailWord_6590375 prefixEnd_6590375 1128010022791585953734641 := by
  unfold tailWord_6590375
  simp only [CollatzResearch.WordTrace]
  refine ⟨240370723499204396285780579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160247148999469597523853719 240370723499204396285780579)
  ·
    refine ⟨360556085248806594428670869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240370723499204396285780579 360556085248806594428670869)
    ·
      refine ⟨16901066496037809113843947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 360556085248806594428670869 16901066496037809113843947)
      ·
        refine ⟨25351599744056713670765921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16901066496037809113843947 25351599744056713670765921)
        ·
          refine ⟨19013699808042535253074441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25351599744056713670765921 19013699808042535253074441)
          ·
            refine ⟨14260274856031901439805831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19013699808042535253074441 14260274856031901439805831)
            ·
              refine ⟨21390412284047852159708747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14260274856031901439805831 21390412284047852159708747)
              ·
                refine ⟨32085618426071778239563121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21390412284047852159708747 32085618426071778239563121)
                ·
                  refine ⟨24064213819553833679672341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32085618426071778239563121 24064213819553833679672341)
                  ·
                    refine ⟨1128010022791585953734641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24064213819553833679672341 1128010022791585953734641)
                    ·
                      rfl

theorem cell23_6590375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6590375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590375 prefixEnd_6590375 := by exact prefixLift 6590375
  have htrace : WordTrace (prefixWord ++ tailWord_6590375) baseStart_6590375 baseEnd_6590375 := by
    simpa [prefixWord, tailWord_6590375, baseEnd_6590375] using wordTrace_append hprefix tailTrace_6590375
  have hstable : (prefixWord ++ tailWord_6590375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590375).length < 2 ^ (prefixWord ++ tailWord_6590375).sum := by decide
  have hdescent : baseEnd_6590375 < baseStart_6590375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590458 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_6590458 : Nat := 118140960795 + 6590458 * 2 ^ 59
def prefixEnd_6590458 : Nat := 4983230072969 + 3 ^ 40 * 6590458 * 2
def baseEnd_6590458 : Nat := 3384072687269081036466041

theorem tailTrace_6590458 : CollatzResearch.WordTrace tailWord_6590458 prefixEnd_6590458 3384072687269081036466041 := by
  unfold tailWord_6590458
  simp only [CollatzResearch.WordTrace]
  refine ⟨60093437689475925365263007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160249167171935800974034685 60093437689475925365263007)
  ·
    refine ⟨90140156534213888047894511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60093437689475925365263007 90140156534213888047894511)
    ·
      refine ⟨135210234801320832071841767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90140156534213888047894511 135210234801320832071841767)
      ·
        refine ⟨202815352201981248107762651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135210234801320832071841767 202815352201981248107762651)
        ·
          refine ⟨304223028302971872161643977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202815352201981248107762651 304223028302971872161643977)
          ·
            refine ⟨228167271227228904121232983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304223028302971872161643977 228167271227228904121232983)
            ·
              refine ⟨342250906840843356181849475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228167271227228904121232983 342250906840843356181849475)
              ·
                refine ⟨513376360261265034272774213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342250906840843356181849475 513376360261265034272774213)
                ·
                  refine ⟨96258067548987193926145165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513376360261265034272774213 96258067548987193926145165)
                  ·
                    refine ⟨36096775330870197722304437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96258067548987193926145165 36096775330870197722304437)
                    ·
                      refine ⟨3384072687269081036466041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36096775330870197722304437 3384072687269081036466041)
                      ·
                        rfl

theorem cell23_6590458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_6590458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590458 prefixEnd_6590458 := by exact prefixLift 6590458
  have htrace : WordTrace (prefixWord ++ tailWord_6590458) baseStart_6590458 baseEnd_6590458 := by
    simpa [prefixWord, tailWord_6590458, baseEnd_6590458] using wordTrace_append hprefix tailTrace_6590458
  have hstable : (prefixWord ++ tailWord_6590458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590458).length < 2 ^ (prefixWord ++ tailWord_6590458).sum := by decide
  have hdescent : baseEnd_6590458 < baseStart_6590458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590495 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 6]
def baseStart_6590495 : Nat := 118140960795 + 6590495 * 2 ^ 59
def prefixEnd_6590495 : Nat := 4983230072969 + 3 ^ 40 * 6590495 * 2
def baseEnd_6590495 : Nat := 376010187339255265744819

theorem tailTrace_6590495 : CollatzResearch.WordTrace tailWord_6590495 prefixEnd_6590495 376010187339255265744819 := by
  unfold tailWord_6590495
  simp only [CollatzResearch.WordTrace]
  refine ⟨240375100258769656780148939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160250066839179771186765959 240375100258769656780148939)
  ·
    refine ⟨360562650388154485170223409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240375100258769656780148939 360562650388154485170223409)
    ·
      refine ⟨270421987791115863877667557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360562650388154485170223409 270421987791115863877667557)
      ·
        refine ⟨50704122710834224477062667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270421987791115863877667557 50704122710834224477062667)
        ·
          refine ⟨76056184066251336715594001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50704122710834224477062667 76056184066251336715594001)
          ·
            refine ⟨57042138049688502536695501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76056184066251336715594001 57042138049688502536695501)
            ·
              refine ⟨21390801768633188451260813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57042138049688502536695501 21390801768633188451260813)
              ·
                refine ⟨8021550663237445669222805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21390801768633188451260813 8021550663237445669222805)
                ·
                  refine ⟨376010187339255265744819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8021550663237445669222805 376010187339255265744819)
                  ·
                    rfl

theorem cell23_6590495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 6].length) (baseStart_6590495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590495 prefixEnd_6590495 := by exact prefixLift 6590495
  have htrace : WordTrace (prefixWord ++ tailWord_6590495) baseStart_6590495 baseEnd_6590495 := by
    simpa [prefixWord, tailWord_6590495, baseEnd_6590495] using wordTrace_append hprefix tailTrace_6590495
  have hstable : (prefixWord ++ tailWord_6590495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590495).length < 2 ^ (prefixWord ++ tailWord_6590495).sum := by decide
  have hdescent : baseEnd_6590495 < baseStart_6590495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590539 : List Nat := [1, 1, 1, 1, 3, 1, 2, 8, 1, 1, 3]
def baseStart_6590539 : Nat := 118140960795 + 6590539 * 2 ^ 59
def prefixEnd_6590539 : Nat := 4983230072969 + 3 ^ 40 * 6590539 * 2
def baseEnd_6590539 : Nat := 3384114279202095219553169

theorem tailTrace_6590539 : CollatzResearch.WordTrace tailWord_6590539 prefixEnd_6590539 3384114279202095219553169 := by
  unfold tailWord_6590539
  simp only [CollatzResearch.WordTrace]
  refine ⟨240376705070610252294750671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160251136713740168196500447 240376705070610252294750671)
  ·
    refine ⟨360565057605915378442126007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240376705070610252294750671 360565057605915378442126007)
    ·
      refine ⟨540847586408873067663189011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360565057605915378442126007 540847586408873067663189011)
      ·
        refine ⟨811271379613309601494783517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540847586408873067663189011 811271379613309601494783517)
        ·
          refine ⟨304226767354991100560543819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 811271379613309601494783517 304226767354991100560543819)
          ·
            refine ⟨456340151032486650840815729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304226767354991100560543819 456340151032486650840815729)
            ·
              refine ⟨342255113274364988130611797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456340151032486650840815729 342255113274364988130611797)
              ·
                refine ⟨4010802108683964704655607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 342255113274364988130611797 4010802108683964704655607)
                ·
                  refine ⟨6016203163025947056983411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010802108683964704655607 6016203163025947056983411)
                  ·
                    refine ⟨9024304744538920585475117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6016203163025947056983411 9024304744538920585475117)
                    ·
                      refine ⟨3384114279202095219553169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9024304744538920585475117 3384114279202095219553169)
                      ·
                        rfl

theorem cell23_6590539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 1, 3].length) (baseStart_6590539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590539 prefixEnd_6590539 := by exact prefixLift 6590539
  have htrace : WordTrace (prefixWord ++ tailWord_6590539) baseStart_6590539 baseEnd_6590539 := by
    simpa [prefixWord, tailWord_6590539, baseEnd_6590539] using wordTrace_append hprefix tailTrace_6590539
  have hstable : (prefixWord ++ tailWord_6590539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590539).length < 2 ^ (prefixWord ++ tailWord_6590539).sum := by decide
  have hdescent : baseEnd_6590539 < baseStart_6590539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590585 : List Nat := [1, 2, 1, 3, 4, 2, 10]
def baseStart_6590585 : Nat := 118140960795 + 6590585 * 2 ^ 59
def prefixEnd_6590585 : Nat := 4983230072969 + 3 ^ 40 * 6590585 * 2
def baseEnd_6590585 : Nat := 41779480238422247402197

theorem tailTrace_6590585 : CollatzResearch.WordTrace tailWord_6590585 prefixEnd_6590585 41779480238422247402197 := by
  unfold tailWord_6590585
  simp only [CollatzResearch.WordTrace]
  refine ⟨240378382828443602150925209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160252255218962401433950139 240378382828443602150925209)
  ·
    refine ⟨180283787121332701613193907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240378382828443602150925209 180283787121332701613193907)
    ·
      refine ⟨270425680681999052419790861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180283787121332701613193907 270425680681999052419790861)
      ·
        refine ⟨101409630255749644657421573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270425680681999052419790861 101409630255749644657421573)
        ·
          refine ⟨19014305672953058373266545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101409630255749644657421573 19014305672953058373266545)
          ·
            refine ⟨14260729254714793779949909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19014305672953058373266545 14260729254714793779949909)
            ·
              refine ⟨41779480238422247402197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14260729254714793779949909 41779480238422247402197)
              ·
                rfl

theorem cell23_6590585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 10].length) (baseStart_6590585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590585 prefixEnd_6590585 := by exact prefixLift 6590585
  have htrace : WordTrace (prefixWord ++ tailWord_6590585) baseStart_6590585 baseEnd_6590585 := by
    simpa [prefixWord, tailWord_6590585, baseEnd_6590585] using wordTrace_append hprefix tailTrace_6590585
  have hstable : (prefixWord ++ tailWord_6590585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590585).length < 2 ^ (prefixWord ++ tailWord_6590585).sum := by decide
  have hdescent : baseEnd_6590585 < baseStart_6590585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590589 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_6590589 : Nat := 118140960795 + 6590589 * 2 ^ 59
def prefixEnd_6590589 : Nat := 4983230072969 + 3 ^ 40 * 6590589 * 2
def baseEnd_6590589 : Nat := 1128046651078273341309313

theorem tailTrace_6590589 : CollatzResearch.WordTrace tailWord_6590589 prefixEnd_6590589 1128046651078273341309313 := by
  unfold tailWord_6590589
  simp only [CollatzResearch.WordTrace]
  refine ⟨240378528720429110834070821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160252352480286073889380547 240378528720429110834070821)
  ·
    refine ⟨45070974135080458281388279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240378528720429110834070821 45070974135080458281388279)
    ·
      refine ⟨67606461202620687422082419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45070974135080458281388279 67606461202620687422082419)
      ·
        refine ⟨101409691803931031133123629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67606461202620687422082419 101409691803931031133123629)
        ·
          refine ⟨38028634426474136674921361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101409691803931031133123629 38028634426474136674921361)
          ·
            refine ⟨28521475819855602506191021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38028634426474136674921361 28521475819855602506191021)
            ·
              refine ⟨10695553432445850939821633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28521475819855602506191021 10695553432445850939821633)
              ·
                refine ⟨8021665074334388204866225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10695553432445850939821633 8021665074334388204866225)
                ·
                  refine ⟨6016248805750791153649669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8021665074334388204866225 6016248805750791153649669)
                  ·
                    refine ⟨1128046651078273341309313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6016248805750791153649669 1128046651078273341309313)
                    ·
                      rfl

theorem cell23_6590589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_6590589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590589 prefixEnd_6590589 := by exact prefixLift 6590589
  have htrace : WordTrace (prefixWord ++ tailWord_6590589) baseStart_6590589 baseEnd_6590589 := by
    simpa [prefixWord, tailWord_6590589, baseEnd_6590589] using wordTrace_append hprefix tailTrace_6590589
  have hstable : (prefixWord ++ tailWord_6590589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590589).length < 2 ^ (prefixWord ++ tailWord_6590589).sum := by decide
  have hdescent : baseEnd_6590589 < baseStart_6590589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590596 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_6590596 : Nat := 118140960795 + 6590596 * 2 ^ 59
def prefixEnd_6590596 : Nat := 4983230072969 + 3 ^ 40 * 6590596 * 2
def baseEnd_6590596 : Nat := 3384143547599401496540407

theorem tailTrace_6590596 : CollatzResearch.WordTrace tailWord_6590596 prefixEnd_6590596 3384143547599401496540407 := by
  unfold tailWord_6590596
  simp only [CollatzResearch.WordTrace]
  refine ⟨120189392015701875514787821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160252522687602500686383761 120189392015701875514787821)
  ·
    refine ⟨45071022005888203318045433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120189392015701875514787821 45071022005888203318045433)
    ·
      refine ⟨33803266504416152488534075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45071022005888203318045433 33803266504416152488534075)
      ·
        refine ⟨50704899756624228732801113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33803266504416152488534075 50704899756624228732801113)
        ·
          refine ⟨38028674817468171549600835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50704899756624228732801113 38028674817468171549600835)
          ·
            refine ⟨57043012226202257324401253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38028674817468171549600835 57043012226202257324401253)
            ·
              refine ⟨10695564792412923248325235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57043012226202257324401253 10695564792412923248325235)
              ·
                refine ⟨16043347188619384872487853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10695564792412923248325235 16043347188619384872487853)
                ·
                  refine ⟨6016255195732269327182945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16043347188619384872487853 6016255195732269327182945)
                  ·
                    refine ⟨4512191396799201995387209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6016255195732269327182945 4512191396799201995387209)
                    ·
                      refine ⟨3384143547599401496540407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512191396799201995387209 3384143547599401496540407)
                      ·
                        rfl

theorem cell23_6590596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_6590596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590596 prefixEnd_6590596 := by exact prefixLift 6590596
  have htrace : WordTrace (prefixWord ++ tailWord_6590596) baseStart_6590596 baseEnd_6590596 := by
    simpa [prefixWord, tailWord_6590596, baseEnd_6590596] using wordTrace_append hprefix tailTrace_6590596
  have hstable : (prefixWord ++ tailWord_6590596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590596).length < 2 ^ (prefixWord ++ tailWord_6590596).sum := by decide
  have hdescent : baseEnd_6590596 < baseStart_6590596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590606 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_6590606 : Nat := 118140960795 + 6590606 * 2 ^ 59
def prefixEnd_6590606 : Nat := 4983230072969 + 3 ^ 40 * 6590606 * 2
def baseEnd_6590606 : Nat := 1128049560801982152471787

theorem tailTrace_6590606 : CollatzResearch.WordTrace tailWord_6590606 prefixEnd_6590606 1128049560801982152471787 := by
  unfold tailWord_6590606
  simp only [CollatzResearch.WordTrace]
  refine ⟨30047393595170940342179959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160252765840911681824959781 30047393595170940342179959)
  ·
    refine ⟨45071090392756410513269939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30047393595170940342179959 45071090392756410513269939)
    ·
      refine ⟨67606635589134615769904909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45071090392756410513269939 67606635589134615769904909)
      ·
        refine ⟨25352488345925480913714341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67606635589134615769904909 25352488345925480913714341)
        ·
          refine ⟨4753591564861027671321439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25352488345925480913714341 4753591564861027671321439)
          ·
            refine ⟨7130387347291541506982159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753591564861027671321439 7130387347291541506982159)
            ·
              refine ⟨10695581020937312260473239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7130387347291541506982159 10695581020937312260473239)
              ·
                refine ⟨16043371531405968390709859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10695581020937312260473239 16043371531405968390709859)
                ·
                  refine ⟨24065057297108952586064789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16043371531405968390709859 24065057297108952586064789)
                  ·
                    refine ⟨1128049560801982152471787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24065057297108952586064789 1128049560801982152471787)
                    ·
                      rfl

theorem cell23_6590606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_6590606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590606 prefixEnd_6590606 := by exact prefixLift 6590606
  have htrace : WordTrace (prefixWord ++ tailWord_6590606) baseStart_6590606 baseEnd_6590606 := by
    simpa [prefixWord, tailWord_6590606, baseEnd_6590606] using wordTrace_append hprefix tailTrace_6590606
  have hstable : (prefixWord ++ tailWord_6590606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590606).length < 2 ^ (prefixWord ++ tailWord_6590606).sum := by decide
  have hdescent : baseEnd_6590606 < baseStart_6590606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590616 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_6590616 : Nat := 118140960795 + 6590616 * 2 ^ 59
def prefixEnd_6590616 : Nat := 4983230072969 + 3 ^ 40 * 6590616 * 2
def baseEnd_6590616 : Nat := 3384153817212491418290315

theorem tailTrace_6590616 : CollatzResearch.WordTrace tailWord_6590616 prefixEnd_6590616 3384153817212491418290315 := by
  unfold tailWord_6590616
  simp only [CollatzResearch.WordTrace]
  refine ⟨120189756745665647222651851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160253008994220862963535801 120189756745665647222651851)
  ·
    refine ⟨180284635118498470833977777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120189756745665647222651851 180284635118498470833977777)
    ·
      refine ⟨135213476338873853125483333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180284635118498470833977777 135213476338873853125483333)
      ·
        refine ⟨25352526813538847461028125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135213476338873853125483333 25352526813538847461028125)
        ·
          refine ⟨9507197555077067797885547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25352526813538847461028125 9507197555077067797885547)
          ·
            refine ⟨14260796332615601696828321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9507197555077067797885547 14260796332615601696828321)
            ·
              refine ⟨10695597249461701272621241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14260796332615601696828321 10695597249461701272621241)
              ·
                refine ⟨8021697937096275954465931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10695597249461701272621241 8021697937096275954465931)
                ·
                  refine ⟨12032546905644413931698897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8021697937096275954465931 12032546905644413931698897)
                  ·
                    refine ⟨9024410179233310448774173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12032546905644413931698897 9024410179233310448774173)
                    ·
                      refine ⟨3384153817212491418290315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9024410179233310448774173 3384153817212491418290315)
                      ·
                        rfl

theorem cell23_6590616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_6590616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590616 prefixEnd_6590616 := by exact prefixLift 6590616
  have htrace : WordTrace (prefixWord ++ tailWord_6590616) baseStart_6590616 baseEnd_6590616 := by
    simpa [prefixWord, tailWord_6590616, baseEnd_6590616] using wordTrace_append hprefix tailTrace_6590616
  have hstable : (prefixWord ++ tailWord_6590616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590616).length < 2 ^ (prefixWord ++ tailWord_6590616).sum := by decide
  have hdescent : baseEnd_6590616 < baseStart_6590616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590655 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_6590655 : Nat := 118140960795 + 6590655 * 2 ^ 59
def prefixEnd_6590655 : Nat := 4983230072969 + 3 ^ 40 * 6590655 * 2
def baseEnd_6590655 : Nat := 3384173842958016765702635

theorem tailTrace_6590655 : CollatzResearch.WordTrace tailWord_6590655 prefixEnd_6590655 3384173842958016765702635 := by
  unfold tailWord_6590655
  simp only [CollatzResearch.WordTrace]
  refine ⟨240380935938190004105973419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160253957292126669403982279 240380935938190004105973419)
  ·
    refine ⟨360571403907285006158960129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240380935938190004105973419 360571403907285006158960129)
    ·
      refine ⟨270428552930463754619220097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360571403907285006158960129 270428552930463754619220097)
      ·
        refine ⟨202821414697847815964415073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270428552930463754619220097 202821414697847815964415073)
        ·
          refine ⟨152116061023385861973311305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202821414697847815964415073 152116061023385861973311305)
          ·
            refine ⟨114087045767539396479983479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152116061023385861973311305 114087045767539396479983479)
            ·
              refine ⟨171130568651309094719975219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114087045767539396479983479 171130568651309094719975219)
              ·
                refine ⟨256695852976963642079962829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171130568651309094719975219 256695852976963642079962829)
                ·
                  refine ⟨96260944866361365779986061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256695852976963642079962829 96260944866361365779986061)
                  ·
                    refine ⟨36097854324885512167494773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96260944866361365779986061 36097854324885512167494773)
                    ·
                      refine ⟨3384173842958016765702635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36097854324885512167494773 3384173842958016765702635)
                      ·
                        rfl

theorem cell23_6590655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_6590655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590655 prefixEnd_6590655 := by exact prefixLift 6590655
  have htrace : WordTrace (prefixWord ++ tailWord_6590655) baseStart_6590655 baseEnd_6590655 := by
    simpa [prefixWord, tailWord_6590655, baseEnd_6590655] using wordTrace_append hprefix tailTrace_6590655
  have hstable : (prefixWord ++ tailWord_6590655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590655).length < 2 ^ (prefixWord ++ tailWord_6590655).sum := by decide
  have hdescent : baseEnd_6590655 < baseStart_6590655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590703 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 2, 2, 2]
def baseStart_6590703 : Nat := 118140960795 + 6590703 * 2 ^ 59
def prefixEnd_6590703 : Nat := 4983230072969 + 3 ^ 40 * 6590703 * 2
def baseEnd_6590703 : Nat := 3384198490029432577902415

theorem tailTrace_6590703 : CollatzResearch.WordTrace tailWord_6590703 prefixEnd_6590703 3384198490029432577902415 := by
  unfold tailWord_6590703
  simp only [CollatzResearch.WordTrace]
  refine ⟨240382686642016108303720763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160255124428010738869147175 240382686642016108303720763)
  ·
    refine ⟨360574029963024162455581145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240382686642016108303720763 360574029963024162455581145)
    ·
      refine ⟨270430522472268121841685859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360574029963024162455581145 270430522472268121841685859)
      ·
        refine ⟨405645783708402182762528789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270430522472268121841685859 405645783708402182762528789)
        ·
          refine ⟨19014646111331352316993537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 405645783708402182762528789 19014646111331352316993537)
          ·
            refine ⟨14260984583498514237745153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19014646111331352316993537 14260984583498514237745153)
            ·
              refine ⟨10695738437623885678308865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14260984583498514237745153 10695738437623885678308865)
              ·
                refine ⟨8021803828217914258731649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10695738437623885678308865 8021803828217914258731649)
                ·
                  refine ⟨6016352871163435694048737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8021803828217914258731649 6016352871163435694048737)
                  ·
                    refine ⟨4512264653372576770536553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6016352871163435694048737 4512264653372576770536553)
                    ·
                      refine ⟨3384198490029432577902415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512264653372576770536553 3384198490029432577902415)
                      ·
                        rfl

theorem cell23_6590703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 2, 2].length) (baseStart_6590703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590703 prefixEnd_6590703 := by exact prefixLift 6590703
  have htrace : WordTrace (prefixWord ++ tailWord_6590703) baseStart_6590703 baseEnd_6590703 := by
    simpa [prefixWord, tailWord_6590703, baseEnd_6590703] using wordTrace_append hprefix tailTrace_6590703
  have hstable : (prefixWord ++ tailWord_6590703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590703).length < 2 ^ (prefixWord ++ tailWord_6590703).sum := by decide
  have hdescent : baseEnd_6590703 < baseStart_6590703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590829 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_6590829 : Nat := 118140960795 + 6590829 * 2 ^ 59
def prefixEnd_6590829 : Nat := 4983230072969 + 3 ^ 40 * 6590829 * 2
def baseEnd_6590829 : Nat := 1128087729530633028308945

theorem tailTrace_6590829 : CollatzResearch.WordTrace tailWord_6590829 prefixEnd_6590829 1128087729530633028308945 := by
  unfold tailWord_6590829
  simp only [CollatzResearch.WordTrace]
  refine ⟨240387282239559631822807541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160258188159706421215205027 240387282239559631822807541)
  ·
    refine ⟨22536307709958715483388207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240387282239559631822807541 22536307709958715483388207)
    ·
      refine ⟨33804461564938073225082311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22536307709958715483388207 33804461564938073225082311)
      ·
        refine ⟨50706692347407109837623467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33804461564938073225082311 50706692347407109837623467)
        ·
          refine ⟨76060038521110664756435201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50706692347407109837623467 76060038521110664756435201)
          ·
            refine ⟨57045028890832998567326401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76060038521110664756435201 57045028890832998567326401)
            ·
              refine ⟨42783771668124748925494801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57045028890832998567326401 42783771668124748925494801)
              ·
                refine ⟨32087828751093561694121101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42783771668124748925494801 32087828751093561694121101)
                ·
                  refine ⟨12032935781660085635295413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32087828751093561694121101 12032935781660085635295413)
                  ·
                    refine ⟨1128087729530633028308945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12032935781660085635295413 1128087729530633028308945)
                    ·
                      rfl

theorem cell23_6590829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_6590829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590829 prefixEnd_6590829 := by exact prefixLift 6590829
  have htrace : WordTrace (prefixWord ++ tailWord_6590829) baseStart_6590829 baseEnd_6590829 := by
    simpa [prefixWord, tailWord_6590829, baseEnd_6590829] using wordTrace_append hprefix tailTrace_6590829
  have hstable : (prefixWord ++ tailWord_6590829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590829).length < 2 ^ (prefixWord ++ tailWord_6590829).sum := by decide
  have hdescent : baseEnd_6590829 < baseStart_6590829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590859 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 1, 6]
def baseStart_6590859 : Nat := 118140960795 + 6590859 * 2 ^ 59
def prefixEnd_6590859 : Nat := 4983230072969 + 3 ^ 40 * 6590859 * 2
def baseEnd_6590859 : Nat := 1128092864337177989183899

theorem tailTrace_6590859 : CollatzResearch.WordTrace tailWord_6590859 prefixEnd_6590859 1128092864337177989183899 := by
  unfold tailWord_6590859
  simp only [CollatzResearch.WordTrace]
  refine ⟨240388376429450946946399631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160258917619633964630933087 240388376429450946946399631)
  ·
    refine ⟨360582564644176420419599447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240388376429450946946399631 360582564644176420419599447)
    ·
      refine ⟨540873846966264630629399171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360582564644176420419599447 540873846966264630629399171)
      ·
        refine ⟨811310770449396945944098757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540873846966264630629399171 811310770449396945944098757)
        ·
          refine ⟨152120769459261927364518517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 811310770449396945944098757 152120769459261927364518517)
          ·
            refine ⟨14261322136805805690423611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152120769459261927364518517 14261322136805805690423611)
            ·
              refine ⟨21391983205208708535635417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14261322136805805690423611 21391983205208708535635417)
              ·
                refine ⟨16043987403906531401726563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21391983205208708535635417 16043987403906531401726563)
                ·
                  refine ⟨24065981105859797102589845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16043987403906531401726563 24065981105859797102589845)
                  ·
                    refine ⟨1128092864337177989183899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24065981105859797102589845 1128092864337177989183899)
                    ·
                      rfl

theorem cell23_6590859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 6].length) (baseStart_6590859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590859 prefixEnd_6590859 := by exact prefixLift 6590859
  have htrace : WordTrace (prefixWord ++ tailWord_6590859) baseStart_6590859 baseEnd_6590859 := by
    simpa [prefixWord, tailWord_6590859, baseEnd_6590859] using wordTrace_append hprefix tailTrace_6590859
  have hstable : (prefixWord ++ tailWord_6590859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590859).length < 2 ^ (prefixWord ++ tailWord_6590859).sum := by decide
  have hdescent : baseEnd_6590859 < baseStart_6590859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590879 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_6590879 : Nat := 118140960795 + 6590879 * 2 ^ 59
def prefixEnd_6590879 : Nat := 4983230072969 + 3 ^ 40 * 6590879 * 2
def baseEnd_6590879 : Nat := 3384288862624623889301605

theorem tailTrace_6590879 : CollatzResearch.WordTrace tailWord_6590879 prefixEnd_6590879 3384288862624623889301605 := by
  unfold tailWord_6590879
  simp only [CollatzResearch.WordTrace]
  refine ⟨240389105889378490362127691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160259403926252326908085127 240389105889378490362127691)
  ·
    refine ⟨360583658834067735543191537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240389105889378490362127691 360583658834067735543191537)
    ·
      refine ⟨270437744125550801657393653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360583658834067735543191537 270437744125550801657393653)
      ·
        refine ⟨25353538511770387655380655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270437744125550801657393653 25353538511770387655380655)
        ·
          refine ⟨38030307767655581483070983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25353538511770387655380655 38030307767655581483070983)
          ·
            refine ⟨57045461651483372224606475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38030307767655581483070983 57045461651483372224606475)
            ·
              refine ⟨85568192477225058336909713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57045461651483372224606475 85568192477225058336909713)
              ·
                refine ⟨64176144357918793752682285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85568192477225058336909713 64176144357918793752682285)
                ·
                  refine ⟨24066054134219547657255857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64176144357918793752682285 24066054134219547657255857)
                  ·
                    refine ⟨18049540600664660742941893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24066054134219547657255857 18049540600664660742941893)
                    ·
                      refine ⟨3384288862624623889301605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18049540600664660742941893 3384288862624623889301605)
                      ·
                        rfl

theorem cell23_6590879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_6590879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590879 prefixEnd_6590879 := by exact prefixLift 6590879
  have htrace : WordTrace (prefixWord ++ tailWord_6590879) baseStart_6590879 baseEnd_6590879 := by
    simpa [prefixWord, tailWord_6590879, baseEnd_6590879] using wordTrace_append hprefix tailTrace_6590879
  have hstable : (prefixWord ++ tailWord_6590879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590879).length < 2 ^ (prefixWord ++ tailWord_6590879).sum := by decide
  have hdescent : baseEnd_6590879 < baseStart_6590879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590893 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6590893 : Nat := 118140960795 + 6590893 * 2 ^ 59
def prefixEnd_6590893 : Nat := 4983230072969 + 3 ^ 40 * 6590893 * 2
def baseEnd_6590893 : Nat := 1128098683784595611508847

theorem tailTrace_6590893 : CollatzResearch.WordTrace tailWord_6590893 prefixEnd_6590893 1128098683784595611508847 := by
  unfold tailWord_6590893
  simp only [CollatzResearch.WordTrace]
  refine ⟨240389616511327770753137333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160259744340885180502091555 240389616511327770753137333)
  ·
    refine ⟨22536526547936978508106625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240389616511327770753137333 22536526547936978508106625)
    ·
      refine ⟨16902394910952733881079969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22536526547936978508106625 16902394910952733881079969)
      ·
        refine ⟨12676796183214550410809977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16902394910952733881079969 12676796183214550410809977)
        ·
          refine ⟨9507597137410912808107483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12676796183214550410809977 9507597137410912808107483)
          ·
            refine ⟨14261395706116369212161225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9507597137410912808107483 14261395706116369212161225)
            ·
              refine ⟨10696046779587276909120919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14261395706116369212161225 10696046779587276909120919)
              ·
                refine ⟨16044070169380915363681379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10696046779587276909120919 16044070169380915363681379)
                ·
                  refine ⟨24066105254071373045522069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16044070169380915363681379 24066105254071373045522069)
                  ·
                    refine ⟨1128098683784595611508847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24066105254071373045522069 1128098683784595611508847)
                    ·
                      rfl

theorem cell23_6590893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6590893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590893 prefixEnd_6590893 := by exact prefixLift 6590893
  have htrace : WordTrace (prefixWord ++ tailWord_6590893) baseStart_6590893 baseEnd_6590893 := by
    simpa [prefixWord, tailWord_6590893, baseEnd_6590893] using wordTrace_append hprefix tailTrace_6590893
  have hstable : (prefixWord ++ tailWord_6590893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590893).length < 2 ^ (prefixWord ++ tailWord_6590893).sum := by decide
  have hdescent : baseEnd_6590893 < baseStart_6590893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590920 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_6590920 : Nat := 118140960795 + 6590920 * 2 ^ 59
def prefixEnd_6590920 : Nat := 4983230072969 + 3 ^ 40 * 6590920 * 2
def baseEnd_6590920 : Nat := 3384309915331458228888917

theorem tailTrace_6590920 : CollatzResearch.WordTrace tailWord_6590920 prefixEnd_6590920 3384309915331458228888917 := by
  unfold tailWord_6590920
  simp only [CollatzResearch.WordTrace]
  refine ⟨120195300641114977182185107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160260400854819969576246809 120195300641114977182185107)
  ·
    refine ⟨180292950961672465773277661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120195300641114977182185107 180292950961672465773277661)
    ·
      refine ⟨67609856610627174664979123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180292950961672465773277661 67609856610627174664979123)
      ·
        refine ⟨101414784915940761997468685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67609856610627174664979123 101414784915940761997468685)
        ·
          refine ⟨38030544343477785749050757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101414784915940761997468685 38030544343477785749050757)
          ·
            refine ⟨7130727064402084827947017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38030544343477785749050757 7130727064402084827947017)
            ·
              refine ⟨5348045298301563620960263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7130727064402084827947017 5348045298301563620960263)
              ·
                refine ⟨8022067947452345431440395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348045298301563620960263 8022067947452345431440395)
                ·
                  refine ⟨12033101921178518147160593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022067947452345431440395 12033101921178518147160593)
                  ·
                    refine ⟨9024826440883888610370445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12033101921178518147160593 9024826440883888610370445)
                    ·
                      refine ⟨3384309915331458228888917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9024826440883888610370445 3384309915331458228888917)
                      ·
                        rfl

theorem cell23_6590920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_6590920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590920 prefixEnd_6590920 := by exact prefixLift 6590920
  have htrace : WordTrace (prefixWord ++ tailWord_6590920) baseStart_6590920 baseEnd_6590920 := by
    simpa [prefixWord, tailWord_6590920, baseEnd_6590920] using wordTrace_append hprefix tailTrace_6590920
  have hstable : (prefixWord ++ tailWord_6590920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590920).length < 2 ^ (prefixWord ++ tailWord_6590920).sum := by decide
  have hdescent : baseEnd_6590920 < baseStart_6590920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590933 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_6590933 : Nat := 118140960795 + 6590933 * 2 ^ 59
def prefixEnd_6590933 : Nat := 4983230072969 + 3 ^ 40 * 6590933 * 2
def baseEnd_6590933 : Nat := 3384316590579966678026357

theorem tailTrace_6590933 : CollatzResearch.WordTrace tailWord_6590933 prefixEnd_6590933 3384316590579966678026357 := by
  unfold tailWord_6590933
  simp only [CollatzResearch.WordTrace]
  refine ⟨240391075431182857584593453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160260716954121905056395635 240391075431182857584593453)
  ·
    refine ⟨90146653286693571594222545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240391075431182857584593453 90146653286693571594222545)
    ·
      refine ⟨67609989965020178695666909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90146653286693571594222545 67609989965020178695666909)
      ·
        refine ⟨25353746236882567010875091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67609989965020178695666909 25353746236882567010875091)
        ·
          refine ⟨38030619355323850516312637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25353746236882567010875091 38030619355323850516312637)
          ·
            refine ⟨14261482258246443943617239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38030619355323850516312637 14261482258246443943617239)
            ·
              refine ⟨21392223387369665915425859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14261482258246443943617239 21392223387369665915425859)
              ·
                refine ⟨32088335081054498873138789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21392223387369665915425859 32088335081054498873138789)
                ·
                  refine ⟨6016562827697718538713523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32088335081054498873138789 6016562827697718538713523)
                  ·
                    refine ⟨9024844241546577808070285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6016562827697718538713523 9024844241546577808070285)
                    ·
                      refine ⟨3384316590579966678026357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9024844241546577808070285 3384316590579966678026357)
                      ·
                        rfl

theorem cell23_6590933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_6590933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590933 prefixEnd_6590933 := by exact prefixLift 6590933
  have htrace : WordTrace (prefixWord ++ tailWord_6590933) baseStart_6590933 baseEnd_6590933 := by
    simpa [prefixWord, tailWord_6590933, baseEnd_6590933] using wordTrace_append hprefix tailTrace_6590933
  have hstable : (prefixWord ++ tailWord_6590933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590933).length < 2 ^ (prefixWord ++ tailWord_6590933).sum := by decide
  have hdescent : baseEnd_6590933 < baseStart_6590933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590959 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_6590959 : Nat := 118140960795 + 6590959 * 2 ^ 59
def prefixEnd_6590959 : Nat := 4983230072969 + 3 ^ 40 * 6590959 * 2
def baseEnd_6590959 : Nat := 3384329941076983576301237

theorem tailTrace_6590959 : CollatzResearch.WordTrace tailWord_6590959 prefixEnd_6590959 3384329941076983576301237 := by
  unfold tailWord_6590959
  simp only [CollatzResearch.WordTrace]
  refine ⟨240392023729088664025039931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160261349152725776016693287 240392023729088664025039931)
  ·
    refine ⟨360588035593632996037559897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240392023729088664025039931 360588035593632996037559897)
    ·
      refine ⟨270441026695224747028169923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360588035593632996037559897 270441026695224747028169923)
      ·
        refine ⟨405661540042837120542254885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270441026695224747028169923 405661540042837120542254885)
        ·
          refine ⟨76061538758031960101672791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405661540042837120542254885 76061538758031960101672791)
          ·
            refine ⟨114092308137047940152509187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76061538758031960101672791 114092308137047940152509187)
            ·
              refine ⟨171138462205571910228763781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114092308137047940152509187 171138462205571910228763781)
              ·
                refine ⟨32088461663544733167893209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171138462205571910228763781 32088461663544733167893209)
                ·
                  refine ⟨24066346247658549875919907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32088461663544733167893209 24066346247658549875919907)
                  ·
                    refine ⟨36099519371487824813879861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24066346247658549875919907 36099519371487824813879861)
                    ·
                      refine ⟨3384329941076983576301237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36099519371487824813879861 3384329941076983576301237)
                      ·
                        rfl

theorem cell23_6590959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_6590959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590959 prefixEnd_6590959 := by exact prefixLift 6590959
  have htrace : WordTrace (prefixWord ++ tailWord_6590959) baseStart_6590959 baseEnd_6590959 := by
    simpa [prefixWord, tailWord_6590959, baseEnd_6590959] using wordTrace_append hprefix tailTrace_6590959
  have hstable : (prefixWord ++ tailWord_6590959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590959).length < 2 ^ (prefixWord ++ tailWord_6590959).sum := by decide
  have hdescent : baseEnd_6590959 < baseStart_6590959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590969 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_6590969 : Nat := 118140960795 + 6590969 * 2 ^ 59
def prefixEnd_6590969 : Nat := 4983230072969 + 3 ^ 40 * 6590969 * 2
def baseEnd_6590969 : Nat := 3384335075883528537176191

theorem tailTrace_6590969 : CollatzResearch.WordTrace tailWord_6590969 prefixEnd_6590969 3384335075883528537176191 := by
  unfold tailWord_6590969
  simp only [CollatzResearch.WordTrace]
  refine ⟨240392388459052435732903961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160261592306034957155269307 240392388459052435732903961)
  ·
    refine ⟨180294291344289326799677971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240392388459052435732903961 180294291344289326799677971)
    ·
      refine ⟨270441437016433990199516957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180294291344289326799677971 270441437016433990199516957)
      ·
        refine ⟨101415538881162746324818859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270441437016433990199516957 101415538881162746324818859)
        ·
          refine ⟨152123308321744119487228289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101415538881162746324818859 152123308321744119487228289)
          ·
            refine ⟨114092481241308089615421217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152123308321744119487228289 114092481241308089615421217)
            ·
              refine ⟨85569360930981067211565913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114092481241308089615421217 85569360930981067211565913)
              ·
                refine ⟨64177020698235800408674435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85569360930981067211565913 64177020698235800408674435)
                ·
                  refine ⟨96265531047353700613011653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64177020698235800408674435 96265531047353700613011653)
                  ·
                    refine ⟨18049787071378818864939685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96265531047353700613011653 18049787071378818864939685)
                    ·
                      refine ⟨3384335075883528537176191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18049787071378818864939685 3384335075883528537176191)
                      ·
                        rfl

theorem cell23_6590969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_6590969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590969 prefixEnd_6590969 := by exact prefixLift 6590969
  have htrace : WordTrace (prefixWord ++ tailWord_6590969) baseStart_6590969 baseEnd_6590969 := by
    simpa [prefixWord, tailWord_6590969, baseEnd_6590969] using wordTrace_append hprefix tailTrace_6590969
  have hstable : (prefixWord ++ tailWord_6590969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590969).length < 2 ^ (prefixWord ++ tailWord_6590969).sum := by decide
  have hdescent : baseEnd_6590969 < baseStart_6590969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590973 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_6590973 : Nat := 118140960795 + 6590973 * 2 ^ 59
def prefixEnd_6590973 : Nat := 4983230072969 + 3 ^ 40 * 6590973 * 2
def baseEnd_6590973 : Nat := 3384337129806146521526173

theorem tailTrace_6590973 : CollatzResearch.WordTrace tailWord_6590973 prefixEnd_6590973 3384337129806146521526173 := by
  unfold tailWord_6590973
  simp only [CollatzResearch.WordTrace]
  refine ⟨240392534351037944416049573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160261689567358629610699715 240392534351037944416049573)
  ·
    refine ⟨45073600190819614578009295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240392534351037944416049573 45073600190819614578009295)
    ·
      refine ⟨67610400286229421867013943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45073600190819614578009295 67610400286229421867013943)
      ·
        refine ⟨101415600429344132800520915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67610400286229421867013943 101415600429344132800520915)
        ·
          refine ⟨152123400644016199200781373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101415600429344132800520915 152123400644016199200781373)
          ·
            refine ⟨57046275241506074700293015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152123400644016199200781373 57046275241506074700293015)
            ·
              refine ⟨85569412862259112050439523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57046275241506074700293015 85569412862259112050439523)
              ·
                refine ⟨128354119293388668075659285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85569412862259112050439523 128354119293388668075659285)
                ·
                  refine ⟨6016599341877593816046529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128354119293388668075659285 6016599341877593816046529)
                  ·
                    refine ⟨4512449506408195362034897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6016599341877593816046529 4512449506408195362034897)
                    ·
                      refine ⟨3384337129806146521526173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512449506408195362034897 3384337129806146521526173)
                      ·
                        rfl

theorem cell23_6590973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_6590973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590973 prefixEnd_6590973 := by exact prefixLift 6590973
  have htrace : WordTrace (prefixWord ++ tailWord_6590973) baseStart_6590973 baseEnd_6590973 := by
    simpa [prefixWord, tailWord_6590973, baseEnd_6590973] using wordTrace_append hprefix tailTrace_6590973
  have hstable : (prefixWord ++ tailWord_6590973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590973).length < 2 ^ (prefixWord ++ tailWord_6590973).sum := by decide
  have hdescent : baseEnd_6590973 < baseStart_6590973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6590990 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_6590990 : Nat := 118140960795 + 6590990 * 2 ^ 59
def prefixEnd_6590990 : Nat := 4983230072969 + 3 ^ 40 * 6590990 * 2
def baseEnd_6590990 : Nat := 3384345858977272955013595

theorem tailTrace_6590990 : CollatzResearch.WordTrace tailWord_6590990 prefixEnd_6590990 3384345858977272955013595 := by
  unfold tailWord_6590990
  simp only [CollatzResearch.WordTrace]
  refine ⟨30049144298997044539927303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160262102927984237546278949 30049144298997044539927303)
  ·
    refine ⟨45073716448495566809890955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30049144298997044539927303 45073716448495566809890955)
    ·
      refine ⟨67610574672743350214836433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45073716448495566809890955 67610574672743350214836433)
      ·
        refine ⟨50707931004557512661127325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67610574672743350214836433 50707931004557512661127325)
        ·
          refine ⟨19015474126709067247922747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50707931004557512661127325 19015474126709067247922747)
          ·
            refine ⟨28523211190063600871884121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19015474126709067247922747 28523211190063600871884121)
            ·
              refine ⟨21392408392547700653913091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28523211190063600871884121 21392408392547700653913091)
              ·
                refine ⟨32088612588821550980869637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21392408392547700653913091 32088612588821550980869637)
                ·
                  refine ⟨6016614860404040808913057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32088612588821550980869637 6016614860404040808913057)
                  ·
                    refine ⟨4512461145303030606684793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6016614860404040808913057 4512461145303030606684793)
                    ·
                      refine ⟨3384345858977272955013595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512461145303030606684793 3384345858977272955013595)
                      ·
                        rfl

theorem cell23_6590990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_6590990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6590990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6590990 prefixEnd_6590990 := by exact prefixLift 6590990
  have htrace : WordTrace (prefixWord ++ tailWord_6590990) baseStart_6590990 baseEnd_6590990 := by
    simpa [prefixWord, tailWord_6590990, baseEnd_6590990] using wordTrace_append hprefix tailTrace_6590990
  have hstable : (prefixWord ++ tailWord_6590990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6590990).length < 2 ^ (prefixWord ++ tailWord_6590990).sum := by decide
  have hdescent : baseEnd_6590990 < baseStart_6590990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6590990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591026 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_6591026 : Nat := 118140960795 + 6591026 * 2 ^ 59
def prefixEnd_6591026 : Nat := 4983230072969 + 3 ^ 40 * 6591026 * 2
def baseEnd_6591026 : Nat := 1128121448093611604721143

theorem tailTrace_6591026 : CollatzResearch.WordTrace tailWord_6591026 prefixEnd_6591026 1128121448093611604721143 := by
  unfold tailWord_6591026
  simp only [CollatzResearch.WordTrace]
  refine ⟨60098616854961483616932233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160262978279897289645152621 60098616854961483616932233)
  ·
    refine ⟨45073962641221112712699175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60098616854961483616932233 45073962641221112712699175)
    ·
      refine ⟨67610943961831669069048763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45073962641221112712699175 67610943961831669069048763)
      ·
        refine ⟨101416415942747503603573145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67610943961831669069048763 101416415942747503603573145)
        ·
          refine ⟨76062311957060627702679859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101416415942747503603573145 76062311957060627702679859)
          ·
            refine ⟨114093467935590941554019789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76062311957060627702679859 114093467935590941554019789)
            ·
              refine ⟨42785050475846603082757421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114093467935590941554019789 42785050475846603082757421)
              ·
                refine ⟨16044393928442476156034033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42785050475846603082757421 16044393928442476156034033)
                ·
                  refine ⟨12033295446331857117025525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16044393928442476156034033 12033295446331857117025525)
                  ·
                    refine ⟨1128121448093611604721143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12033295446331857117025525 1128121448093611604721143)
                    ·
                      rfl

theorem cell23_6591026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_6591026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591026 prefixEnd_6591026 := by exact prefixLift 6591026
  have htrace : WordTrace (prefixWord ++ tailWord_6591026) baseStart_6591026 baseEnd_6591026 := by
    simpa [prefixWord, tailWord_6591026, baseEnd_6591026] using wordTrace_append hprefix tailTrace_6591026
  have hstable : (prefixWord ++ tailWord_6591026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591026).length < 2 ^ (prefixWord ++ tailWord_6591026).sum := by decide
  have hdescent : baseEnd_6591026 < baseStart_6591026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591036 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_6591036 : Nat := 118140960795 + 6591036 * 2 ^ 59
def prefixEnd_6591036 : Nat := 4983230072969 + 3 ^ 40 * 6591036 * 2
def baseEnd_6591036 : Nat := 3384369479087379775038383

theorem tailTrace_6591036 : CollatzResearch.WordTrace tailWord_6591036 prefixEnd_6591036 3384369479087379775038383 := by
  unfold tailWord_6591036
  simp only [CollatzResearch.WordTrace]
  refine ⟨120197416074904853087796481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160263221433206470783728641 120197416074904853087796481)
  ·
    refine ⟨90148062056178639815847361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120197416074904853087796481 90148062056178639815847361)
    ·
      refine ⟨67611046542133979861885521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90148062056178639815847361 67611046542133979861885521)
      ·
        refine ⟨50708284906600484896414141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67611046542133979861885521 50708284906600484896414141)
        ·
          refine ⟨19015606839975181836155303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50708284906600484896414141 19015606839975181836155303)
          ·
            refine ⟨28523410259962772754232955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19015606839975181836155303 28523410259962772754232955)
            ·
              refine ⟨42785115389944159131349433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28523410259962772754232955 42785115389944159131349433)
              ·
                refine ⟨32088836542458119348512075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42785115389944159131349433 32088836542458119348512075)
                ·
                  refine ⟨48133254813687179022768113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32088836542458119348512075 48133254813687179022768113)
                  ·
                    refine ⟨36099941110265384267076085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48133254813687179022768113 36099941110265384267076085)
                    ·
                      refine ⟨3384369479087379775038383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36099941110265384267076085 3384369479087379775038383)
                      ·
                        rfl

theorem cell23_6591036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_6591036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591036 prefixEnd_6591036 := by exact prefixLift 6591036
  have htrace : WordTrace (prefixWord ++ tailWord_6591036) baseStart_6591036 baseEnd_6591036 := by
    simpa [prefixWord, tailWord_6591036, baseEnd_6591036] using wordTrace_append hprefix tailTrace_6591036
  have hstable : (prefixWord ++ tailWord_6591036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591036).length < 2 ^ (prefixWord ++ tailWord_6591036).sum := by decide
  have hdescent : baseEnd_6591036 < baseStart_6591036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591053 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_6591053 : Nat := 118140960795 + 6591053 * 2 ^ 59
def prefixEnd_6591053 : Nat := 4983230072969 + 3 ^ 40 * 6591053 * 2
def baseEnd_6591053 : Nat := 3384378208258506208525805

theorem tailTrace_6591053 : CollatzResearch.WordTrace tailWord_6591053 prefixEnd_6591053 3384378208258506208525805 := by
  unfold tailWord_6591053
  simp only [CollatzResearch.WordTrace]
  refine ⟨240395452190748118078961813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160263634793832078719307875 240395452190748118078961813)
  ·
    refine ⟨11268536821441318034951335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240395452190748118078961813 11268536821441318034951335)
    ·
      refine ⟨16902805232161977052427003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11268536821441318034951335 16902805232161977052427003)
      ·
        refine ⟨25354207848242965578640505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16902805232161977052427003 25354207848242965578640505)
        ·
          refine ⟨19015655886182224183980379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25354207848242965578640505 19015655886182224183980379)
          ·
            refine ⟨28523483829273336275970569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19015655886182224183980379 28523483829273336275970569)
            ·
              refine ⟨21392612871955002206977927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28523483829273336275970569 21392612871955002206977927)
              ·
                refine ⟨32088919307932503310466891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21392612871955002206977927 32088919307932503310466891)
                ·
                  refine ⟨48133378961898754965700337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32088919307932503310466891 48133378961898754965700337)
                  ·
                    refine ⟨36100034221424066224275253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48133378961898754965700337 36100034221424066224275253)
                    ·
                      refine ⟨3384378208258506208525805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36100034221424066224275253 3384378208258506208525805)
                      ·
                        rfl

theorem cell23_6591053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_6591053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591053 prefixEnd_6591053 := by exact prefixLift 6591053
  have htrace : WordTrace (prefixWord ++ tailWord_6591053) baseStart_6591053 baseEnd_6591053 := by
    simpa [prefixWord, tailWord_6591053, baseEnd_6591053] using wordTrace_append hprefix tailTrace_6591053
  have hstable : (prefixWord ++ tailWord_6591053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591053).length < 2 ^ (prefixWord ++ tailWord_6591053).sum := by decide
  have hdescent : baseEnd_6591053 < baseStart_6591053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591063 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 2, 4, 2]
def baseStart_6591063 : Nat := 118140960795 + 6591063 * 2 ^ 59
def prefixEnd_6591063 : Nat := 4983230072969 + 3 ^ 40 * 6591063 * 2
def baseEnd_6591063 : Nat := 3384383343065051169400759

theorem tailTrace_6591063 : CollatzResearch.WordTrace tailWord_6591063 prefixEnd_6591063 3384383343065051169400759 := by
  unfold tailWord_6591063
  simp only [CollatzResearch.WordTrace]
  refine ⟨240395816920711889786825843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160263877947141259857883895 240395816920711889786825843)
  ·
    refine ⟨360593725381067834680238765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240395816920711889786825843 360593725381067834680238765)
    ·
      refine ⟨135222647017900438005089537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360593725381067834680238765 135222647017900438005089537)
      ·
        refine ⟨101416985263425328503817153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135222647017900438005089537 101416985263425328503817153)
        ·
          refine ⟨76062738947568996377862865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101416985263425328503817153 76062738947568996377862865)
          ·
            refine ⟨57047054210676747283397149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76062738947568996377862865 57047054210676747283397149)
            ·
              refine ⟨21392645329003780231273931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57047054210676747283397149 21392645329003780231273931)
              ·
                refine ⟨32088967993505670346910897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21392645329003780231273931 32088967993505670346910897)
                ·
                  refine ⟨24066725995129252760183173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32088967993505670346910897 24066725995129252760183173)
                  ·
                    refine ⟨4512511124086734892534345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24066725995129252760183173 4512511124086734892534345)
                    ·
                      refine ⟨3384383343065051169400759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512511124086734892534345 3384383343065051169400759)
                      ·
                        rfl

theorem cell23_6591063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_6591063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591063 prefixEnd_6591063 := by exact prefixLift 6591063
  have htrace : WordTrace (prefixWord ++ tailWord_6591063) baseStart_6591063 baseEnd_6591063 := by
    simpa [prefixWord, tailWord_6591063, baseEnd_6591063] using wordTrace_append hprefix tailTrace_6591063
  have hstable : (prefixWord ++ tailWord_6591063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591063).length < 2 ^ (prefixWord ++ tailWord_6591063).sum := by decide
  have hdescent : baseEnd_6591063 < baseStart_6591063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591073 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 3, 4]
def baseStart_6591073 : Nat := 118140960795 + 6591073 * 2 ^ 59
def prefixEnd_6591073 : Nat := 4983230072969 + 3 ^ 40 * 6591073 * 2
def baseEnd_6591073 : Nat := 1128129492623865376758571

theorem tailTrace_6591073 : CollatzResearch.WordTrace tailWord_6591073 prefixEnd_6591073 1128129492623865376758571 := by
  unfold tailWord_6591073
  simp only [CollatzResearch.WordTrace]
  refine ⟨240396181650675661494689873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160264121100450440996459915 240396181650675661494689873)
  ·
    refine ⟨180297136238006746121017405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240396181650675661494689873 180297136238006746121017405)
    ·
      refine ⟨67611426089252529795381527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180297136238006746121017405 67611426089252529795381527)
      ·
        refine ⟨101417139133878794693072291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67611426089252529795381527 101417139133878794693072291)
        ·
          refine ⟨152125708700818192039608437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101417139133878794693072291 152125708700818192039608437)
          ·
            refine ⟨14261785190701705503713291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152125708700818192039608437 14261785190701705503713291)
            ·
              refine ⟨21392677786052558255569937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14261785190701705503713291 21392677786052558255569937)
              ·
                refine ⟨16044508339539418691677453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21392677786052558255569937 16044508339539418691677453)
                ·
                  refine ⟨6016690627327282009379045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16044508339539418691677453 6016690627327282009379045)
                  ·
                    refine ⟨1128129492623865376758571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6016690627327282009379045 1128129492623865376758571)
                    ·
                      rfl

theorem cell23_6591073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_6591073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591073 prefixEnd_6591073 := by exact prefixLift 6591073
  have htrace : WordTrace (prefixWord ++ tailWord_6591073) baseStart_6591073 baseEnd_6591073 := by
    simpa [prefixWord, tailWord_6591073, baseEnd_6591073] using wordTrace_append hprefix tailTrace_6591073
  have hstable : (prefixWord ++ tailWord_6591073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591073).length < 2 ^ (prefixWord ++ tailWord_6591073).sum := by decide
  have hdescent : baseEnd_6591073 < baseStart_6591073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591116 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_6591116 : Nat := 118140960795 + 6591116 * 2 ^ 59
def prefixEnd_6591116 : Nat := 4983230072969 + 3 ^ 40 * 6591116 * 2
def baseEnd_6591116 : Nat := 1128136852513246487346005

theorem tailTrace_6591116 : CollatzResearch.WordTrace tailWord_6591116 prefixEnd_6591116 1128136852513246487346005 := by
  unfold tailWord_6591116
  simp only [CollatzResearch.WordTrace]
  refine ⟨120198874994759939919252601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160265166659679919892336801 120198874994759939919252601)
  ·
    refine ⟨90149156246069954939439451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120198874994759939919252601 90149156246069954939439451)
    ·
      refine ⟨135223734369104932409159177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90149156246069954939439451 135223734369104932409159177)
      ·
        refine ⟨101417800776828699306869383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135223734369104932409159177 101417800776828699306869383)
        ·
          refine ⟨152126701165243048960304075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101417800776828699306869383 152126701165243048960304075)
          ·
            refine ⟨228190051747864573440456113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152126701165243048960304075 228190051747864573440456113)
            ·
              refine ⟨171142538810898430080342085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228190051747864573440456113 171142538810898430080342085)
              ·
                refine ⟨32089226027043455640064141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171142538810898430080342085 32089226027043455640064141)
                ·
                  refine ⟨12033459760141295865024053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32089226027043455640064141 12033459760141295865024053)
                  ·
                    refine ⟨1128136852513246487346005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12033459760141295865024053 1128136852513246487346005)
                    ·
                      rfl

theorem cell23_6591116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_6591116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591116 prefixEnd_6591116 := by exact prefixLift 6591116
  have htrace : WordTrace (prefixWord ++ tailWord_6591116) baseStart_6591116 baseEnd_6591116 := by
    simpa [prefixWord, tailWord_6591116, baseEnd_6591116] using wordTrace_append hprefix tailTrace_6591116
  have hstable : (prefixWord ++ tailWord_6591116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591116).length < 2 ^ (prefixWord ++ tailWord_6591116).sum := by decide
  have hdescent : baseEnd_6591116 < baseStart_6591116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591123 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 4, 3, 2]
def baseStart_6591123 : Nat := 118140960795 + 6591123 * 2 ^ 59
def prefixEnd_6591123 : Nat := 4983230072969 + 3 ^ 40 * 6591123 * 2
def baseEnd_6591123 : Nat := 3384414151904320934650483

theorem tailTrace_6591123 : CollatzResearch.WordTrace tailWord_6591123 prefixEnd_6591123 3384414151904320934650483 := by
  unfold tailWord_6591123
  simp only [CollatzResearch.WordTrace]
  refine ⟨240398005300494520034010023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160265336866996346689340015 240398005300494520034010023)
  ·
    refine ⟨360597007950741780051015035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240398005300494520034010023 360597007950741780051015035)
    ·
      refine ⟨540895511926112670076522553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360597007950741780051015035 540895511926112670076522553)
      ·
        refine ⟨405671633944584502557391915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540895511926112670076522553 405671633944584502557391915)
        ·
          refine ⟨608507450916876753836087873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405671633944584502557391915 608507450916876753836087873)
          ·
            refine ⟨456380588187657565377065905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608507450916876753836087873 456380588187657565377065905)
            ·
              refine ⟨342285441140743174032799429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456380588187657565377065905 342285441140743174032799429)
              ·
                refine ⟨64178520213889345131149893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342285441140743174032799429 64178520213889345131149893)
                ·
                  refine ⟨12033472540104252212090605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64178520213889345131149893 12033472540104252212090605)
                  ·
                    refine ⟨4512552202539094579533977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12033472540104252212090605 4512552202539094579533977)
                    ·
                      refine ⟨3384414151904320934650483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512552202539094579533977 3384414151904320934650483)
                      ·
                        rfl

theorem cell23_6591123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 3, 2].length) (baseStart_6591123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591123 prefixEnd_6591123 := by exact prefixLift 6591123
  have htrace : WordTrace (prefixWord ++ tailWord_6591123) baseStart_6591123 baseEnd_6591123 := by
    simpa [prefixWord, tailWord_6591123, baseEnd_6591123] using wordTrace_append hprefix tailTrace_6591123
  have hstable : (prefixWord ++ tailWord_6591123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591123).length < 2 ^ (prefixWord ++ tailWord_6591123).sum := by decide
  have hdescent : baseEnd_6591123 < baseStart_6591123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591133 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_6591133 : Nat := 118140960795 + 6591133 * 2 ^ 59
def prefixEnd_6591133 : Nat := 4983230072969 + 3 ^ 40 * 6591133 * 2
def baseEnd_6591133 : Nat := 1128139762236955298508479

theorem tailTrace_6591133 : CollatzResearch.WordTrace tailWord_6591133 prefixEnd_6591133 1128139762236955298508479 := by
  unfold tailWord_6591133
  simp only [CollatzResearch.WordTrace]
  refine ⟨240398370030458291741874053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160265580020305527827916035 240398370030458291741874053)
  ·
    refine ⟨45074694380710929701601385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240398370030458291741874053 45074694380710929701601385)
    ·
      refine ⟨33806020785533197276201039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45074694380710929701601385 33806020785533197276201039)
      ·
        refine ⟨50709031178299795914301559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33806020785533197276201039 50709031178299795914301559)
        ·
          refine ⟨76063546767449693871452339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50709031178299795914301559 76063546767449693871452339)
          ·
            refine ⟨114095320151174540807178509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76063546767449693871452339 114095320151174540807178509)
            ·
              refine ⟨42785745056690452802691941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114095320151174540807178509 42785745056690452802691941)
              ·
                refine ⟨8022327198129459900504739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42785745056690452802691941 8022327198129459900504739)
                ·
                  refine ⟨12033490797194189850757109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022327198129459900504739 12033490797194189850757109)
                  ·
                    refine ⟨1128139762236955298508479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12033490797194189850757109 1128139762236955298508479)
                    ·
                      rfl

theorem cell23_6591133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_6591133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591133 prefixEnd_6591133 := by exact prefixLift 6591133
  have htrace : WordTrace (prefixWord ++ tailWord_6591133) baseStart_6591133 baseEnd_6591133 := by
    simpa [prefixWord, tailWord_6591133, baseEnd_6591133] using wordTrace_append hprefix tailTrace_6591133
  have hstable : (prefixWord ++ tailWord_6591133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591133).length < 2 ^ (prefixWord ++ tailWord_6591133).sum := by decide
  have hdescent : baseEnd_6591133 < baseStart_6591133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591140 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_6591140 : Nat := 118140960795 + 6591140 * 2 ^ 59
def prefixEnd_6591140 : Nat := 4983230072969 + 3 ^ 40 * 6591140 * 2
def baseEnd_6591140 : Nat := 3384422881075447368137905

theorem tailTrace_6591140 : CollatzResearch.WordTrace tailWord_6591140 prefixEnd_6591140 3384422881075447368137905 := by
  unfold tailWord_6591140
  simp only [CollatzResearch.WordTrace]
  refine ⟨120199312670716465968689437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160265750227621954624919249 120199312670716465968689437)
  ·
    refine ⟨45074742251518674738258539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120199312670716465968689437 45074742251518674738258539)
    ·
      refine ⟨67612113377278012107387809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45074742251518674738258539 67612113377278012107387809)
      ·
        refine ⟨50709085032958509080540857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67612113377278012107387809 50709085032958509080540857)
        ·
          refine ⟨38031813774718881810405643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50709085032958509080540857 38031813774718881810405643)
          ·
            refine ⟨57047720662078322715608465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38031813774718881810405643 57047720662078322715608465)
            ·
              refine ⟨42785790496558742036706349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57047720662078322715608465 42785790496558742036706349)
              ·
                refine ⟨16044671436209528263764881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42785790496558742036706349 16044671436209528263764881)
                ·
                  refine ⟨12033503577157146197823661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16044671436209528263764881 12033503577157146197823661)
                  ·
                    refine ⟨4512563841433929824183873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12033503577157146197823661 4512563841433929824183873)
                    ·
                      refine ⟨3384422881075447368137905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512563841433929824183873 3384422881075447368137905)
                      ·
                        rfl

theorem cell23_6591140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_6591140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591140 prefixEnd_6591140 := by exact prefixLift 6591140
  have htrace : WordTrace (prefixWord ++ tailWord_6591140) baseStart_6591140 baseEnd_6591140 := by
    simpa [prefixWord, tailWord_6591140, baseEnd_6591140] using wordTrace_append hprefix tailTrace_6591140
  have hstable : (prefixWord ++ tailWord_6591140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591140).length < 2 ^ (prefixWord ++ tailWord_6591140).sum := by decide
  have hdescent : baseEnd_6591140 < baseStart_6591140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591157 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_6591157 : Nat := 118140960795 + 6591157 * 2 ^ 59
def prefixEnd_6591157 : Nat := 4983230072969 + 3 ^ 40 * 6591157 * 2
def baseEnd_6591157 : Nat := 3384431610246573801625327

theorem tailTrace_6591157 : CollatzResearch.WordTrace tailWord_6591157 prefixEnd_6591157 3384431610246573801625327 := by
  unfold tailWord_6591157
  simp only [CollatzResearch.WordTrace]
  refine ⟨240399245382371343840747725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160266163588247562560498483 240399245382371343840747725)
  ·
    refine ⟨90149717018389253940280397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240399245382371343840747725 90149717018389253940280397)
    ·
      refine ⟨33806143881895970227605149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90149717018389253940280397 33806143881895970227605149)
      ·
        refine ⟨12677303955710988835351931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33806143881895970227605149 12677303955710988835351931)
        ·
          refine ⟨19015955933566483253027897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12677303955710988835351931 19015955933566483253027897)
          ·
            refine ⟨14261966950174862439770923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19015955933566483253027897 14261966950174862439770923)
            ·
              refine ⟨21392950425262293659656385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14261966950174862439770923 21392950425262293659656385)
              ·
                refine ⟨16044712818946720244742289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21392950425262293659656385 16044712818946720244742289)
                ·
                  refine ⟨12033534614210040183556717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16044712818946720244742289 12033534614210040183556717)
                  ·
                    refine ⟨4512575480328765068833769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12033534614210040183556717 4512575480328765068833769)
                    ·
                      refine ⟨3384431610246573801625327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512575480328765068833769 3384431610246573801625327)
                      ·
                        rfl

theorem cell23_6591157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_6591157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591157 prefixEnd_6591157 := by exact prefixLift 6591157
  have htrace : WordTrace (prefixWord ++ tailWord_6591157) baseStart_6591157 baseEnd_6591157 := by
    simpa [prefixWord, tailWord_6591157, baseEnd_6591157] using wordTrace_append hprefix tailTrace_6591157
  have hstable : (prefixWord ++ tailWord_6591157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591157).length < 2 ^ (prefixWord ++ tailWord_6591157).sum := by decide
  have hdescent : baseEnd_6591157 < baseStart_6591157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591164 : List Nat := [2, 2, 2, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_6591164 : Nat := 118140960795 + 6591164 * 2 ^ 59
def prefixEnd_6591164 : Nat := 4983230072969 + 3 ^ 40 * 6591164 * 2
def baseEnd_6591164 : Nat := 3384435204611155274237795

theorem tailTrace_6591164 : CollatzResearch.WordTrace tailWord_6591164 prefixEnd_6591164 3384435204611155274237795 := by
  unfold tailWord_6591164
  simp only [CollatzResearch.WordTrace]
  refine ⟨120199750346672992018126273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160266333795563989357501697 120199750346672992018126273)
  ·
    refine ⟨90149812760004744013594705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120199750346672992018126273 90149812760004744013594705)
    ·
      refine ⟨67612359570003558010196029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90149812760004744013594705 67612359570003558010196029)
      ·
        refine ⟨25354634838751334253823511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67612359570003558010196029 25354634838751334253823511)
        ·
          refine ⟨38031952258127001380735267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25354634838751334253823511 38031952258127001380735267)
          ·
            refine ⟨57047928387190502071102901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38031952258127001380735267 57047928387190502071102901)
            ·
              refine ⟨5348243286299109569165897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57047928387190502071102901 5348243286299109569165897)
              ·
                refine ⟨4011182464724332176874423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5348243286299109569165897 4011182464724332176874423)
                ·
                  refine ⟨6016773697086498265311635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011182464724332176874423 6016773697086498265311635)
                  ·
                    refine ⟨9025160545629747397967453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6016773697086498265311635 9025160545629747397967453)
                    ·
                      refine ⟨3384435204611155274237795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9025160545629747397967453 3384435204611155274237795)
                      ·
                        rfl

theorem cell23_6591164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_6591164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591164 prefixEnd_6591164 := by exact prefixLift 6591164
  have htrace : WordTrace (prefixWord ++ tailWord_6591164) baseStart_6591164 baseEnd_6591164 := by
    simpa [prefixWord, tailWord_6591164, baseEnd_6591164] using wordTrace_append hprefix tailTrace_6591164
  have hstable : (prefixWord ++ tailWord_6591164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591164).length < 2 ^ (prefixWord ++ tailWord_6591164).sum := by decide
  have hdescent : baseEnd_6591164 < baseStart_6591164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591176 : List Nat := [2, 1, 3, 1, 2, 3, 1, 10]
def baseStart_6591176 : Nat := 118140960795 + 6591176 * 2 ^ 59
def prefixEnd_6591176 : Nat := 4983230072969 + 3 ^ 40 * 6591176 * 2
def baseEnd_6591176 : Nat := 125349680236259601010657

theorem tailTrace_6591176 : CollatzResearch.WordTrace tailWord_6591176 prefixEnd_6591176 125349680236259601010657 := by
  unfold tailWord_6591176
  simp only [CollatzResearch.WordTrace]
  refine ⟨120199969184651255042844691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160266625579535006723792921 120199969184651255042844691)
  ·
    refine ⟨180299953776976882564267037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120199969184651255042844691 180299953776976882564267037)
    ·
      refine ⟨67612482666366330961600139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180299953776976882564267037 67612482666366330961600139)
      ·
        refine ⟨101418723999549496442400209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67612482666366330961600139 101418723999549496442400209)
        ·
          refine ⟨76064042999662122331800157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101418723999549496442400209 76064042999662122331800157)
          ·
            refine ⟨28524016124873295874425059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76064042999662122331800157 28524016124873295874425059)
            ·
              refine ⟨42786024187309943811637589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28524016124873295874425059 42786024187309943811637589)
              ·
                refine ⟨125349680236259601010657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42786024187309943811637589 125349680236259601010657)
                ·
                  rfl

theorem cell23_6591176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 10].length) (baseStart_6591176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591176 prefixEnd_6591176 := by exact prefixLift 6591176
  have htrace : WordTrace (prefixWord ++ tailWord_6591176) baseStart_6591176 baseEnd_6591176 := by
    simpa [prefixWord, tailWord_6591176, baseEnd_6591176] using wordTrace_append hprefix tailTrace_6591176
  have hstable : (prefixWord ++ tailWord_6591176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591176).length < 2 ^ (prefixWord ++ tailWord_6591176).sum := by decide
  have hdescent : baseEnd_6591176 < baseStart_6591176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591264 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 1, 3, 2]
def baseStart_6591264 : Nat := 118140960795 + 6591264 * 2 ^ 59
def prefixEnd_6591264 : Nat := 4983230072969 + 3 ^ 40 * 6591264 * 2
def baseEnd_6591264 : Nat := 3384486552676604882987335

theorem tailTrace_6591264 : CollatzResearch.WordTrace tailWord_6591264 prefixEnd_6591264 3384486552676604882987335 := by
  unfold tailWord_6591264
  simp only [CollatzResearch.WordTrace]
  refine ⟨120201573996491850557446423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160268765328655800743261897 120201573996491850557446423)
  ·
    refine ⟨180302360994737775836169635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120201573996491850557446423 180302360994737775836169635)
    ·
      refine ⟨270453541492106663754254453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180302360994737775836169635 270453541492106663754254453)
      ·
        refine ⟨25355019514884999726961355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270453541492106663754254453 25355019514884999726961355)
        ·
          refine ⟨38032529272327499590442033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25355019514884999726961355 38032529272327499590442033)
          ·
            refine ⟨28524396954245624692831525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38032529272327499590442033 28524396954245624692831525)
            ·
              refine ⟨5348324428921054629905911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28524396954245624692831525 5348324428921054629905911)
              ·
                refine ⟨8022486643381581944858867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348324428921054629905911 8022486643381581944858867)
                ·
                  refine ⟨12033729965072372917288301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022486643381581944858867 12033729965072372917288301)
                  ·
                    refine ⟨4512648736902139843983113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12033729965072372917288301 4512648736902139843983113)
                    ·
                      refine ⟨3384486552676604882987335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512648736902139843983113 3384486552676604882987335)
                      ·
                        rfl

theorem cell23_6591264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_6591264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591264 prefixEnd_6591264 := by exact prefixLift 6591264
  have htrace : WordTrace (prefixWord ++ tailWord_6591264) baseStart_6591264 baseEnd_6591264 := by
    simpa [prefixWord, tailWord_6591264, baseEnd_6591264] using wordTrace_append hprefix tailTrace_6591264
  have hstable : (prefixWord ++ tailWord_6591264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591264).length < 2 ^ (prefixWord ++ tailWord_6591264).sum := by decide
  have hdescent : baseEnd_6591264 < baseStart_6591264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591283 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 7]
def baseStart_6591283 : Nat := 118140960795 + 6591283 * 2 ^ 59
def prefixEnd_6591283 : Nat := 4983230072969 + 3 ^ 40 * 6591283 * 2
def baseEnd_6591283 : Nat := 376055145423226700961083

theorem tailTrace_6591283 : CollatzResearch.WordTrace tailWord_6591283 prefixEnd_6591283 376055145423226700961083 := by
  unfold tailWord_6591283
  simp only [CollatzResearch.WordTrace]
  refine ⟨240403840979914867359834503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160269227319943244906556335 240403840979914867359834503)
  ·
    refine ⟨360605761469872301039751755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240403840979914867359834503 360605761469872301039751755)
    ·
      refine ⟨540908642204808451559627633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360605761469872301039751755 540908642204808451559627633)
      ·
        refine ⟨405681481653606338669720725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540908642204808451559627633 405681481653606338669720725)
        ·
          refine ⟨19016319452512797125143159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 405681481653606338669720725 19016319452512797125143159)
          ·
            refine ⟨28524479178769195687714739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19016319452512797125143159 28524479178769195687714739)
            ·
              refine ⟨42786718768153793531572109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28524479178769195687714739 42786718768153793531572109)
              ·
                refine ⟨16045019538057672574339541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42786718768153793531572109 16045019538057672574339541)
                ·
                  refine ⟨376055145423226700961083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16045019538057672574339541 376055145423226700961083)
                  ·
                    rfl

theorem cell23_6591283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 7].length) (baseStart_6591283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591283 prefixEnd_6591283 := by exact prefixLift 6591283
  have htrace : WordTrace (prefixWord ++ tailWord_6591283) baseStart_6591283 baseEnd_6591283 := by
    simpa [prefixWord, tailWord_6591283, baseEnd_6591283] using wordTrace_append hprefix tailTrace_6591283
  have hstable : (prefixWord ++ tailWord_6591283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591283).length < 2 ^ (prefixWord ++ tailWord_6591283).sum := by decide
  have hdescent : baseEnd_6591283 < baseStart_6591283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591367 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_6591367 : Nat := 118140960795 + 6591367 * 2 ^ 59
def prefixEnd_6591367 : Nat := 4983230072969 + 3 ^ 40 * 6591367 * 2
def baseEnd_6591367 : Nat := 3384539441184017979999361

theorem tailTrace_6591367 : CollatzResearch.WordTrace tailWord_6591367 prefixEnd_6591367 3384539441184017979999361 := by
  unfold tailWord_6591367
  simp only [CollatzResearch.WordTrace]
  refine ⟨240406904711610549705892355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160271269807740366470594903 240406904711610549705892355)
  ·
    refine ⟨360610357067415824558838533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240406904711610549705892355 360610357067415824558838533)
    ·
      refine ⟨67614441950140467104782225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360610357067415824558838533 67614441950140467104782225)
      ·
        refine ⟨50710831462605350328586669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67614441950140467104782225 50710831462605350328586669)
        ·
          refine ⟨19016561798477006373220001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50710831462605350328586669 19016561798477006373220001)
          ·
            refine ⟨14262421348857754779915001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19016561798477006373220001 14262421348857754779915001)
            ·
              refine ⟨10696816011643316084936251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14262421348857754779915001 10696816011643316084936251)
              ·
                refine ⟨16045224017464974127404377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10696816011643316084936251 16045224017464974127404377)
                ·
                  refine ⟨12033918013098730595553283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16045224017464974127404377 12033918013098730595553283)
                  ·
                    refine ⟨18050877019648095893329925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12033918013098730595553283 18050877019648095893329925)
                    ·
                      refine ⟨3384539441184017979999361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18050877019648095893329925 3384539441184017979999361)
                      ·
                        rfl

theorem cell23_6591367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_6591367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591367 prefixEnd_6591367 := by exact prefixLift 6591367
  have htrace : WordTrace (prefixWord ++ tailWord_6591367) baseStart_6591367 baseEnd_6591367 := by
    simpa [prefixWord, tailWord_6591367, baseEnd_6591367] using wordTrace_append hprefix tailTrace_6591367
  have hstable : (prefixWord ++ tailWord_6591367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591367).length < 2 ^ (prefixWord ++ tailWord_6591367).sum := by decide
  have hdescent : baseEnd_6591367 < baseStart_6591367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591377 : List Nat := [1, 2, 2, 1, 1, 1, 3, 7, 1, 4]
def baseStart_6591377 : Nat := 118140960795 + 6591377 * 2 ^ 59
def prefixEnd_6591377 : Nat := 4983230072969 + 3 ^ 40 * 6591377 * 2
def baseEnd_6591377 : Nat := 1128181525330187646958105

theorem tailTrace_6591377 : CollatzResearch.WordTrace tailWord_6591377 prefixEnd_6591377 1128181525330187646958105 := by
  unfold tailWord_6591377
  simp only [CollatzResearch.WordTrace]
  refine ⟨240407269441574321413756385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160271512961049547609170923 240407269441574321413756385)
  ·
    refine ⟨180305452081180741060317289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240407269441574321413756385 180305452081180741060317289)
    ·
      refine ⟨135229089060885555795237967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180305452081180741060317289 135229089060885555795237967)
      ·
        refine ⟨202843633591328333692856951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135229089060885555795237967 202843633591328333692856951)
        ·
          refine ⟨304265450386992500539285427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202843633591328333692856951 304265450386992500539285427)
          ·
            refine ⟨456398175580488750808928141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304265450386992500539285427 456398175580488750808928141)
            ·
              refine ⟨171149315842683281553348053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456398175580488750808928141 171149315842683281553348053)
              ·
                refine ⟨4011312090062889411406595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 171149315842683281553348053 4011312090062889411406595)
                ·
                  refine ⟨6016968135094334117109893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011312090062889411406595 6016968135094334117109893)
                  ·
                    refine ⟨1128181525330187646958105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6016968135094334117109893 1128181525330187646958105)
                    ·
                      rfl

theorem cell23_6591377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_6591377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591377 prefixEnd_6591377 := by exact prefixLift 6591377
  have htrace : WordTrace (prefixWord ++ tailWord_6591377) baseStart_6591377 baseEnd_6591377 := by
    simpa [prefixWord, tailWord_6591377, baseEnd_6591377] using wordTrace_append hprefix tailTrace_6591377
  have hstable : (prefixWord ++ tailWord_6591377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591377).length < 2 ^ (prefixWord ++ tailWord_6591377).sum := by decide
  have hdescent : baseEnd_6591377 < baseStart_6591377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591380 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6591380 : Nat := 118140960795 + 6591380 * 2 ^ 59
def prefixEnd_6591380 : Nat := 4983230072969 + 3 ^ 40 * 6591380 * 2
def baseEnd_6591380 : Nat := 3384546116432526429136801

theorem tailTrace_6591380 : CollatzResearch.WordTrace tailWord_6591380 prefixEnd_6591380 3384546116432526429136801 := by
  unfold tailWord_6591380
  simp only [CollatzResearch.WordTrace]
  refine ⟨120203689430281726463057797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160271585907042301950743729 120203689430281726463057797)
  ·
    refine ⟨22538191768177823711823337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120203689430281726463057797 22538191768177823711823337)
    ·
      refine ⟨16903643826133367783867503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22538191768177823711823337 16903643826133367783867503)
      ·
        refine ⟨25355465739200051675801255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16903643826133367783867503 25355465739200051675801255)
        ·
          refine ⟨38033198608800077513701883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25355465739200051675801255 38033198608800077513701883)
          ·
            refine ⟨57049797913200116270552825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38033198608800077513701883 57049797913200116270552825)
            ·
              refine ⟨42787348434900087202914619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57049797913200116270552825 42787348434900087202914619)
              ·
                refine ⟨64181022652350130804371929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42787348434900087202914619 64181022652350130804371929)
                ·
                  refine ⟨48135766989262598103278947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64181022652350130804371929 48135766989262598103278947)
                  ·
                    refine ⟨72203650483893897154918421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48135766989262598103278947 72203650483893897154918421)
                    ·
                      refine ⟨3384546116432526429136801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72203650483893897154918421 3384546116432526429136801)
                      ·
                        rfl

theorem cell23_6591380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6591380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591380 prefixEnd_6591380 := by exact prefixLift 6591380
  have htrace : WordTrace (prefixWord ++ tailWord_6591380) baseStart_6591380 baseEnd_6591380 := by
    simpa [prefixWord, tailWord_6591380, baseEnd_6591380] using wordTrace_append hprefix tailTrace_6591380
  have hstable : (prefixWord ++ tailWord_6591380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591380).length < 2 ^ (prefixWord ++ tailWord_6591380).sum := by decide
  have hdescent : baseEnd_6591380 < baseStart_6591380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591417 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 3]
def baseStart_6591417 : Nat := 118140960795 + 6591417 * 2 ^ 59
def prefixEnd_6591417 : Nat := 4983230072969 + 3 ^ 40 * 6591417 * 2
def baseEnd_6591417 : Nat := 3384565115216742784374131

theorem tailTrace_6591417 : CollatzResearch.WordTrace tailWord_6591417 prefixEnd_6591417 3384565115216742784374131 := by
  unfold tailWord_6591417
  simp only [CollatzResearch.WordTrace]
  refine ⟨240408728361429408245212505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160272485574286272163475003 240408728361429408245212505)
  ·
    refine ⟨180306546271072056183909379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240408728361429408245212505 180306546271072056183909379)
    ·
      refine ⟨270459819406608084275864069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180306546271072056183909379 270459819406608084275864069)
      ·
        refine ⟨50711216138739015801724513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270459819406608084275864069 50711216138739015801724513)
        ·
          refine ⟨38033412104054261851293385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50711216138739015801724513 38033412104054261851293385)
          ·
            refine ⟨28525059078040696388470039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38033412104054261851293385 28525059078040696388470039)
            ·
              refine ⟨42787588617061044582705059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28525059078040696388470039 42787588617061044582705059)
              ·
                refine ⟨64181382925591566874057589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42787588617061044582705059 64181382925591566874057589)
                ·
                  refine ⟨6017004649274209394442899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64181382925591566874057589 6017004649274209394442899)
                  ·
                    refine ⟨9025506973911314091664349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017004649274209394442899 9025506973911314091664349)
                    ·
                      refine ⟨3384565115216742784374131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9025506973911314091664349 3384565115216742784374131)
                      ·
                        rfl

theorem cell23_6591417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_6591417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591417 prefixEnd_6591417 := by exact prefixLift 6591417
  have htrace : WordTrace (prefixWord ++ tailWord_6591417) baseStart_6591417 baseEnd_6591417 := by
    simpa [prefixWord, tailWord_6591417, baseEnd_6591417] using wordTrace_append hprefix tailTrace_6591417
  have hstable : (prefixWord ++ tailWord_6591417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591417).length < 2 ^ (prefixWord ++ tailWord_6591417).sum := by decide
  have hdescent : baseEnd_6591417 < baseStart_6591417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591421 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_6591421 : Nat := 118140960795 + 6591421 * 2 ^ 59
def prefixEnd_6591421 : Nat := 4983230072969 + 3 ^ 40 * 6591421 * 2
def baseEnd_6591421 : Nat := 3384567169139360768724113

theorem tailTrace_6591421 : CollatzResearch.WordTrace tailWord_6591421 prefixEnd_6591421 3384567169139360768724113 := by
  unfold tailWord_6591421
  simp only [CollatzResearch.WordTrace]
  refine ⟨240408874253414916928358117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160272582835609944618905411 240408874253414916928358117)
  ·
    refine ⟨45076663922515296924067147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240408874253414916928358117 45076663922515296924067147)
    ·
      refine ⟨67614995883772945386100721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45076663922515296924067147 67614995883772945386100721)
      ·
        refine ⟨50711246912829709039575541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67614995883772945386100721 50711246912829709039575541)
        ·
          refine ⟨4754179398077785222460207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50711246912829709039575541 4754179398077785222460207)
          ·
            refine ⟨7131269097116677833690311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754179398077785222460207 7131269097116677833690311)
            ·
              refine ⟨10696903645675016750535467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7131269097116677833690311 10696903645675016750535467)
              ·
                refine ⟨16045355468512525125803201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10696903645675016750535467 16045355468512525125803201)
                ·
                  refine ⟨12034016601384393844352401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16045355468512525125803201 12034016601384393844352401)
                  ·
                    refine ⟨9025512451038295383264301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12034016601384393844352401 9025512451038295383264301)
                    ·
                      refine ⟨3384567169139360768724113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9025512451038295383264301 3384567169139360768724113)
                      ·
                        rfl

theorem cell23_6591421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_6591421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591421 prefixEnd_6591421 := by exact prefixLift 6591421
  have htrace : WordTrace (prefixWord ++ tailWord_6591421) baseStart_6591421 baseEnd_6591421 := by
    simpa [prefixWord, tailWord_6591421, baseEnd_6591421] using wordTrace_append hprefix tailTrace_6591421
  have hstable : (prefixWord ++ tailWord_6591421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591421).length < 2 ^ (prefixWord ++ tailWord_6591421).sum := by decide
  have hdescent : baseEnd_6591421 < baseStart_6591421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591428 : List Nat := [2, 3, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6591428 : Nat := 118140960795 + 6591428 * 2 ^ 59
def prefixEnd_6591428 : Nat := 4983230072969 + 3 ^ 40 * 6591428 * 2
def baseEnd_6591428 : Nat := 1128190254501314080445527

theorem tailTrace_6591428 : CollatzResearch.WordTrace tailWord_6591428 prefixEnd_6591428 1128190254501314080445527 := by
  unfold tailWord_6591428
  simp only [CollatzResearch.WordTrace]
  refine ⟨120204564782194778561931469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160272753042926371415908625 120204564782194778561931469)
  ·
    refine ⟨45076711793323041960724301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120204564782194778561931469 45076711793323041960724301)
    ·
      refine ⟨16903766922496140735271613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45076711793323041960724301 16903766922496140735271613)
      ·
        refine ⟨6338912595936052775726855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16903766922496140735271613 6338912595936052775726855)
        ·
          refine ⟨9508368893904079163590283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6338912595936052775726855 9508368893904079163590283)
          ·
            refine ⟨14262553340856118745385425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9508368893904079163590283 14262553340856118745385425)
            ·
              refine ⟨10696915005642089059039069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14262553340856118745385425 10696915005642089059039069)
              ·
                refine ⟨4011343127115783397139651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10696915005642089059039069 4011343127115783397139651)
                ·
                  refine ⟨6017014690673675095709477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011343127115783397139651 6017014690673675095709477)
                  ·
                    refine ⟨1128190254501314080445527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6017014690673675095709477 1128190254501314080445527)
                    ·
                      rfl

theorem cell23_6591428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6591428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591428 prefixEnd_6591428 := by exact prefixLift 6591428
  have htrace : WordTrace (prefixWord ++ tailWord_6591428) baseStart_6591428 baseEnd_6591428 := by
    simpa [prefixWord, tailWord_6591428, baseEnd_6591428] using wordTrace_append hprefix tailTrace_6591428
  have hstable : (prefixWord ++ tailWord_6591428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591428).length < 2 ^ (prefixWord ++ tailWord_6591428).sum := by decide
  have hdescent : baseEnd_6591428 < baseStart_6591428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591460 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_6591460 : Nat := 118140960795 + 6591460 * 2 ^ 59
def prefixEnd_6591460 : Nat := 4983230072969 + 3 ^ 40 * 6591460 * 2
def baseEnd_6591460 : Nat := 3384587194884886116136433

theorem tailTrace_6591460 : CollatzResearch.WordTrace tailWord_6591460 prefixEnd_6591460 3384587194884886116136433 := by
  unfold tailWord_6591460
  simp only [CollatzResearch.WordTrace]
  refine ⟨120205148350136813294513917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160273531133515751059351889 120205148350136813294513917)
  ·
    refine ⟨45076930631301304985442719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120205148350136813294513917 45076930631301304985442719)
    ·
      refine ⟨67615395946951957478164079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45076930631301304985442719 67615395946951957478164079)
      ·
        refine ⟨101423093920427936217246119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67615395946951957478164079 101423093920427936217246119)
        ·
          refine ⟨152134640880641904325869179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101423093920427936217246119 152134640880641904325869179)
          ·
            refine ⟨228201961320962856488803769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152134640880641904325869179 228201961320962856488803769)
            ·
              refine ⟨171151470990722142366602827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228201961320962856488803769 171151470990722142366602827)
              ·
                refine ⟨256727206486083213549904241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171151470990722142366602827 256727206486083213549904241)
                ·
                  refine ⟨192545404864562410162428181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256727206486083213549904241 192545404864562410162428181)
                  ·
                    refine ⟨9025565853026362976363821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 192545404864562410162428181 9025565853026362976363821)
                    ·
                      refine ⟨3384587194884886116136433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9025565853026362976363821 3384587194884886116136433)
                      ·
                        rfl

theorem cell23_6591460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_6591460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591460 prefixEnd_6591460 := by exact prefixLift 6591460
  have htrace : WordTrace (prefixWord ++ tailWord_6591460) baseStart_6591460 baseEnd_6591460 := by
    simpa [prefixWord, tailWord_6591460, baseEnd_6591460] using wordTrace_append hprefix tailTrace_6591460
  have hstable : (prefixWord ++ tailWord_6591460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591460).length < 2 ^ (prefixWord ++ tailWord_6591460).sum := by decide
  have hdescent : baseEnd_6591460 < baseStart_6591460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591558 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_6591558 : Nat := 118140960795 + 6591558 * 2 ^ 59
def prefixEnd_6591558 : Nat := 4983230072969 + 3 ^ 40 * 6591558 * 2
def baseEnd_6591558 : Nat := 3384637515989026732710983

theorem tailTrace_6591558 : CollatzResearch.WordTrace tailWord_6591558 prefixEnd_6591558 3384637515989026732710983 := by
  unfold tailWord_6591558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7512933470434955916440479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160275914035945726217396885 7512933470434955916440479)
  ·
    refine ⟨11269400205652433874660719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7512933470434955916440479 11269400205652433874660719)
    ·
      refine ⟨16904100308478650811991079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11269400205652433874660719 16904100308478650811991079)
      ·
        refine ⟨25356150462717976217986619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16904100308478650811991079 25356150462717976217986619)
        ·
          refine ⟨38034225694076964326979929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25356150462717976217986619 38034225694076964326979929)
          ·
            refine ⟨28525669270557723245234947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38034225694076964326979929 28525669270557723245234947)
            ·
              refine ⟨42788503905836584867852421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28525669270557723245234947 42788503905836584867852421)
              ·
                refine ⟨8022844482344359662722329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42788503905836584867852421 8022844482344359662722329)
                ·
                  refine ⟨6017133361758269747041747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8022844482344359662722329 6017133361758269747041747)
                  ·
                    refine ⟨9025700042637404620562621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017133361758269747041747 9025700042637404620562621)
                    ·
                      refine ⟨3384637515989026732710983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9025700042637404620562621 3384637515989026732710983)
                      ·
                        rfl

theorem cell23_6591558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_6591558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591558 prefixEnd_6591558 := by exact prefixLift 6591558
  have htrace : WordTrace (prefixWord ++ tailWord_6591558) baseStart_6591558 baseEnd_6591558 := by
    simpa [prefixWord, tailWord_6591558, baseEnd_6591558] using wordTrace_append hprefix tailTrace_6591558
  have hstable : (prefixWord ++ tailWord_6591558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591558).length < 2 ^ (prefixWord ++ tailWord_6591558).sum := by decide
  have hdescent : baseEnd_6591558 < baseStart_6591558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591637 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_6591637 : Nat := 118140960795 + 6591637 * 2 ^ 59
def prefixEnd_6591637 : Nat := 4983230072969 + 3 ^ 40 * 6591637 * 2
def baseEnd_6591637 : Nat := 3384678080960731923623119

theorem tailTrace_6591637 : CollatzResearch.WordTrace tailWord_6591637 prefixEnd_6591637 3384678080960731923623119 := by
  unfold tailWord_6591637
  simp only [CollatzResearch.WordTrace]
  refine ⟨240416752420632385818221165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160277834947088257212147443 240416752420632385818221165)
  ·
    refine ⟨90156282157737144681832937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240416752420632385818221165 90156282157737144681832937)
    ·
      refine ⟨67617211618302858511374703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90156282157737144681832937 67617211618302858511374703)
      ·
        refine ⟨101425817427454287767062055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67617211618302858511374703 101425817427454287767062055)
        ·
          refine ⟨152138726141181431650593083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101425817427454287767062055 152138726141181431650593083)
          ·
            refine ⟨228208089211772147475889625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152138726141181431650593083 228208089211772147475889625)
            ·
              refine ⟨171156066908829110606917219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228208089211772147475889625 171156066908829110606917219)
              ·
                refine ⟨256734100363243665910375829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171156066908829110606917219 256734100363243665910375829)
                ·
                  refine ⟨12034410954527046839548867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256734100363243665910375829 12034410954527046839548867)
                  ·
                    refine ⟨18051616431790570259323301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12034410954527046839548867 18051616431790570259323301)
                    ·
                      refine ⟨3384678080960731923623119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18051616431790570259323301 3384678080960731923623119)
                      ·
                        rfl

theorem cell23_6591637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_6591637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591637 prefixEnd_6591637 := by exact prefixLift 6591637
  have htrace : WordTrace (prefixWord ++ tailWord_6591637) baseStart_6591637 baseEnd_6591637 := by
    simpa [prefixWord, tailWord_6591637, baseEnd_6591637] using wordTrace_append hprefix tailTrace_6591637
  have hstable : (prefixWord ++ tailWord_6591637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591637).length < 2 ^ (prefixWord ++ tailWord_6591637).sum := by decide
  have hdescent : baseEnd_6591637 < baseStart_6591637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591677 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 8]
def baseStart_6591677 : Nat := 118140960795 + 6591677 * 2 ^ 59
def prefixEnd_6591677 : Nat := 4983230072969 + 3 ^ 40 * 6591677 * 2
def baseEnd_6591677 : Nat := 376077624465212418569215

theorem tailTrace_6591677 : CollatzResearch.WordTrace tailWord_6591677 prefixEnd_6591677 376077624465212418569215 := by
  unfold tailWord_6591677
  simp only [CollatzResearch.WordTrace]
  refine ⟨240418211340487472649677285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160278807560324981766451523 240418211340487472649677285)
  ·
    refine ⟨45078414626341401121814491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240418211340487472649677285 45078414626341401121814491)
    ·
      refine ⟨67617621939512101682721737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45078414626341401121814491 67617621939512101682721737)
      ·
        refine ⟨50713216454634076262041303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67617621939512101682721737 50713216454634076262041303)
        ·
          refine ⟨76069824681951114393061955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50713216454634076262041303 76069824681951114393061955)
          ·
            refine ⟨114104737022926671589592933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76069824681951114393061955 114104737022926671589592933)
            ·
              refine ⟨21394638191798750923048675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114104737022926671589592933 21394638191798750923048675)
              ·
                refine ⟨32091957287698126384573013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21394638191798750923048675 32091957287698126384573013)
                ·
                  refine ⟨376077624465212418569215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32091957287698126384573013 376077624465212418569215)
                  ·
                    rfl

theorem cell23_6591677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_6591677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591677 prefixEnd_6591677 := by exact prefixLift 6591677
  have htrace : WordTrace (prefixWord ++ tailWord_6591677) baseStart_6591677 baseEnd_6591677 := by
    simpa [prefixWord, tailWord_6591677, baseEnd_6591677] using wordTrace_append hprefix tailTrace_6591677
  have hstable : (prefixWord ++ tailWord_6591677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591677).length < 2 ^ (prefixWord ++ tailWord_6591677).sum := by decide
  have hdescent : baseEnd_6591677 < baseStart_6591677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591731 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 2, 3, 2]
def baseStart_6591731 : Nat := 118140960795 + 6591731 * 2 ^ 59
def prefixEnd_6591731 : Nat := 4983230072969 + 3 ^ 40 * 6591731 * 2
def baseEnd_6591731 : Nat := 3384726348142254555847687

theorem tailTrace_6591731 : CollatzResearch.WordTrace tailWord_6591731 prefixEnd_6591731 3384726348142254555847687 := by
  unfold tailWord_6591731
  simp only [CollatzResearch.WordTrace]
  refine ⟨240420180882291839872143047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160280120588194559914762031 240420180882291839872143047)
  ·
    refine ⟨360630271323437759808214571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240420180882291839872143047 360630271323437759808214571)
    ·
      refine ⟨540945406985156639712321857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360630271323437759808214571 540945406985156639712321857)
      ·
        refine ⟨405709055238867479784241393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540945406985156639712321857 405709055238867479784241393)
        ·
          refine ⟨304281791429150609838181045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405709055238867479784241393 304281791429150609838181045)
          ·
            refine ⟨28526417946482869672329473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 304281791429150609838181045 28526417946482869672329473)
            ·
              refine ⟨21394813459862152254247105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28526417946482869672329473 21394813459862152254247105)
              ·
                refine ⟨16046110094896614190685329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21394813459862152254247105 16046110094896614190685329)
                ·
                  refine ⟨12034582571172460643013997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16046110094896614190685329 12034582571172460643013997)
                  ·
                    refine ⟨4512968464189672741130249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12034582571172460643013997 4512968464189672741130249)
                    ·
                      refine ⟨3384726348142254555847687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512968464189672741130249 3384726348142254555847687)
                      ·
                        rfl

theorem cell23_6591731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 3, 2].length) (baseStart_6591731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591731 prefixEnd_6591731 := by exact prefixLift 6591731
  have htrace : WordTrace (prefixWord ++ tailWord_6591731) baseStart_6591731 baseEnd_6591731 := by
    simpa [prefixWord, tailWord_6591731, baseEnd_6591731] using wordTrace_append hprefix tailTrace_6591731
  have hstable : (prefixWord ++ tailWord_6591731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591731).length < 2 ^ (prefixWord ++ tailWord_6591731).sum := by decide
  have hdescent : baseEnd_6591731 < baseStart_6591731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591737 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 3, 6]
def baseStart_6591737 : Nat := 118140960795 + 6591737 * 2 ^ 59
def prefixEnd_6591737 : Nat := 4983230072969 + 3 ^ 40 * 6591737 * 2
def baseEnd_6591737 : Nat := 1128243143008727177457553

theorem tailTrace_6591737 : CollatzResearch.WordTrace tailWord_6591737 prefixEnd_6591737 1128243143008727177457553 := by
  unfold tailWord_6591737
  simp only [CollatzResearch.WordTrace]
  refine ⟨240420399720270102896861465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160280266480180068597907643 240420399720270102896861465)
  ·
    refine ⟨180315299790202577172646099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240420399720270102896861465 180315299790202577172646099)
    ·
      refine ⟨270472949685303865758969149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180315299790202577172646099 270472949685303865758969149)
      ·
        refine ⟨101427356131988949659613431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270472949685303865758969149 101427356131988949659613431)
        ·
          refine ⟨152141034197983424489420147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101427356131988949659613431 152141034197983424489420147)
          ·
            refine ⟨228211551296975136734130221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152141034197983424489420147 228211551296975136734130221)
            ·
              refine ⟨85579331736365676275298833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228211551296975136734130221 85579331736365676275298833)
              ·
                refine ⟨64184498802274257206474125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85579331736365676275298833 64184498802274257206474125)
                ·
                  refine ⟨24069187050852846452427797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64184498802274257206474125 24069187050852846452427797)
                  ·
                    refine ⟨1128243143008727177457553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24069187050852846452427797 1128243143008727177457553)
                    ·
                      rfl

theorem cell23_6591737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_6591737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591737 prefixEnd_6591737 := by exact prefixLift 6591737
  have htrace : WordTrace (prefixWord ++ tailWord_6591737) baseStart_6591737 baseEnd_6591737 := by
    simpa [prefixWord, tailWord_6591737, baseEnd_6591737] using wordTrace_append hprefix tailTrace_6591737
  have hstable : (prefixWord ++ tailWord_6591737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591737).length < 2 ^ (prefixWord ++ tailWord_6591737).sum := by decide
  have hdescent : baseEnd_6591737 < baseStart_6591737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591738 : List Nat := [3, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3]
def baseStart_6591738 : Nat := 118140960795 + 6591738 * 2 ^ 59
def prefixEnd_6591738 : Nat := 4983230072969 + 3 ^ 40 * 6591738 * 2
def baseEnd_6591738 : Nat := 3384729942506836028460155

theorem tailTrace_6591738 : CollatzResearch.WordTrace tailWord_6591738 prefixEnd_6591738 3384729942506836028460155 := by
  unfold tailWord_6591738
  simp only [CollatzResearch.WordTrace]
  refine ⟨60105109048316620016911967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160280290795510986711765245 60105109048316620016911967)
  ·
    refine ⟨90157663572474930025367951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60105109048316620016911967 90157663572474930025367951)
    ·
      refine ⟨135236495358712395038051927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90157663572474930025367951 135236495358712395038051927)
      ·
        refine ⟨202854743038068592557077891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135236495358712395038051927 202854743038068592557077891)
        ·
          refine ⟨304282114557102888835616837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202854743038068592557077891 304282114557102888835616837)
          ·
            refine ⟨57052896479456791656678157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304282114557102888835616837 57052896479456791656678157)
            ·
              refine ⟨21394836179796296871254309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57052896479456791656678157 21394836179796296871254309)
              ·
                refine ⟨4011531783711805663360183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21394836179796296871254309 4011531783711805663360183)
                ·
                  refine ⟨6017297675567708495040275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011531783711805663360183 6017297675567708495040275)
                  ·
                    refine ⟨9025946513351562742560413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017297675567708495040275 9025946513351562742560413)
                    ·
                      refine ⟨3384729942506836028460155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9025946513351562742560413 3384729942506836028460155)
                      ·
                        rfl

theorem cell23_6591738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_6591738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591738 prefixEnd_6591738 := by exact prefixLift 6591738
  have htrace : WordTrace (prefixWord ++ tailWord_6591738) baseStart_6591738 baseEnd_6591738 := by
    simpa [prefixWord, tailWord_6591738, baseEnd_6591738] using wordTrace_append hprefix tailTrace_6591738
  have hstable : (prefixWord ++ tailWord_6591738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591738).length < 2 ^ (prefixWord ++ tailWord_6591738).sum := by decide
  have hdescent : baseEnd_6591738 < baseStart_6591738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591744 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 2, 6, 2]
def baseStart_6591744 : Nat := 118140960795 + 6591744 * 2 ^ 59
def prefixEnd_6591744 : Nat := 4983230072969 + 3 ^ 40 * 6591744 * 2
def baseEnd_6591744 : Nat := 3384733023390763004985127

theorem tailTrace_6591744 : CollatzResearch.WordTrace tailWord_6591744 prefixEnd_6591744 3384733023390763004985127 := by
  unfold tailWord_6591744
  simp only [CollatzResearch.WordTrace]
  refine ⟨120210327515622371546183143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160280436687496495394910857 120210327515622371546183143)
  ·
    refine ⟨180315491273433557319274715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120210327515622371546183143 180315491273433557319274715)
    ·
      refine ⟨270473236910150335978912073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180315491273433557319274715 270473236910150335978912073)
      ·
        refine ⟨202854927682612751984184055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270473236910150335978912073 202854927682612751984184055)
        ·
          refine ⟨304282391523919127976276083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202854927682612751984184055 304282391523919127976276083)
          ·
            refine ⟨456423587285878691964414125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304282391523919127976276083 456423587285878691964414125)
            ·
              refine ⟨171158845232204509486655297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456423587285878691964414125 171158845232204509486655297)
              ·
                refine ⟨128369133924153382114991473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171158845232204509486655297 128369133924153382114991473)
                ·
                  refine ⟨96276850443115036586243605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128369133924153382114991473 96276850443115036586243605)
                  ·
                    refine ⟨4512977364521017339980169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96276850443115036586243605 4512977364521017339980169)
                    ·
                      refine ⟨3384733023390763004985127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4512977364521017339980169 3384733023390763004985127)
                      ·
                        rfl

theorem cell23_6591744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_6591744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591744 prefixEnd_6591744 := by exact prefixLift 6591744
  have htrace : WordTrace (prefixWord ++ tailWord_6591744) baseStart_6591744 baseEnd_6591744 := by
    simpa [prefixWord, tailWord_6591744, baseEnd_6591744] using wordTrace_append hprefix tailTrace_6591744
  have hstable : (prefixWord ++ tailWord_6591744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591744).length < 2 ^ (prefixWord ++ tailWord_6591744).sum := by decide
  have hdescent : baseEnd_6591744 < baseStart_6591744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591754 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_6591754 : Nat := 118140960795 + 6591754 * 2 ^ 59
def prefixEnd_6591754 : Nat := 4983230072969 + 3 ^ 40 * 6591754 * 2
def baseEnd_6591754 : Nat := 1128246052732435988620027

theorem tailTrace_6591754 : CollatzResearch.WordTrace tailWord_6591754 prefixEnd_6591754 1128246052732435988620027 := by
  unfold tailWord_6591754
  simp only [CollatzResearch.WordTrace]
  refine ⟨60105254940302128700057579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160280679840805676533486877 60105254940302128700057579)
  ·
    refine ⟨90157882410453193050086369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60105254940302128700057579 90157882410453193050086369)
    ·
      refine ⟨67618411807839894787564777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90157882410453193050086369 67618411807839894787564777)
      ·
        refine ⟨50713808855879921090673583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67618411807839894787564777 50713808855879921090673583)
        ·
          refine ⟨76070713283819881636010375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50713808855879921090673583 76070713283819881636010375)
          ·
            refine ⟨114106069925729822454015563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76070713283819881636010375 114106069925729822454015563)
            ·
              refine ⟨171159104888594733681023345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114106069925729822454015563 171159104888594733681023345)
              ·
                refine ⟨128369328666446050260767509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171159104888594733681023345 128369328666446050260767509)
                ·
                  refine ⟨6017312281239658605973477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128369328666446050260767509 6017312281239658605973477)
                  ·
                    refine ⟨1128246052732435988620027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6017312281239658605973477 1128246052732435988620027)
                    ·
                      rfl

theorem cell23_6591754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_6591754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591754 prefixEnd_6591754 := by exact prefixLift 6591754
  have htrace : WordTrace (prefixWord ++ tailWord_6591754) baseStart_6591754 baseEnd_6591754 := by
    simpa [prefixWord, tailWord_6591754, baseEnd_6591754] using wordTrace_append hprefix tailTrace_6591754
  have hstable : (prefixWord ++ tailWord_6591754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591754).length < 2 ^ (prefixWord ++ tailWord_6591754).sum := by decide
  have hdescent : baseEnd_6591754 < baseStart_6591754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591775 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 1, 5]
def baseStart_6591775 : Nat := 118140960795 + 6591775 * 2 ^ 59
def prefixEnd_6591775 : Nat := 4983230072969 + 3 ^ 40 * 6591775 * 2
def baseEnd_6591775 : Nat := 1128249647097017461232495

theorem tailTrace_6591775 : CollatzResearch.WordTrace tailWord_6591775 prefixEnd_6591775 1128249647097017461232495 := by
  unfold tailWord_6591775
  simp only [CollatzResearch.WordTrace]
  refine ⟨240421785694132435386744779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160281190462754956924496519 240421785694132435386744779)
  ·
    refine ⟨360632678541198653080117169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240421785694132435386744779 360632678541198653080117169)
    ·
      refine ⟨270474508905898989810087877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360632678541198653080117169 270474508905898989810087877)
      ·
        refine ⟨50713970419856060589391477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270474508905898989810087877 50713970419856060589391477)
        ·
          refine ⟨4754434726861505680255451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50713970419856060589391477 4754434726861505680255451)
          ·
            refine ⟨7131652090292258520383177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754434726861505680255451 7131652090292258520383177)
            ·
              refine ⟨5348739067719193890287383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7131652090292258520383177 5348739067719193890287383)
              ·
                refine ⟨8023108601578790835431075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348739067719193890287383 8023108601578790835431075)
                ·
                  refine ⟨12034662902368186253146613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8023108601578790835431075 12034662902368186253146613)
                  ·
                    refine ⟨1128249647097017461232495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12034662902368186253146613 1128249647097017461232495)
                    ·
                      rfl

theorem cell23_6591775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 5].length) (baseStart_6591775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591775 prefixEnd_6591775 := by exact prefixLift 6591775
  have htrace : WordTrace (prefixWord ++ tailWord_6591775) baseStart_6591775 baseEnd_6591775 := by
    simpa [prefixWord, tailWord_6591775, baseEnd_6591775] using wordTrace_append hprefix tailTrace_6591775
  have hstable : (prefixWord ++ tailWord_6591775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591775).length < 2 ^ (prefixWord ++ tailWord_6591775).sum := by decide
  have hdescent : baseEnd_6591775 < baseStart_6591775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591778 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_6591778 : Nat := 118140960795 + 6591778 * 2 ^ 59
def prefixEnd_6591778 : Nat := 4983230072969 + 3 ^ 40 * 6591778 * 2
def baseEnd_6591778 : Nat := 3384750481733015871959971

theorem tailTrace_6591778 : CollatzResearch.WordTrace tailWord_6591778 prefixEnd_6591778 3384750481733015871959971 := by
  unfold tailWord_6591778
  simp only [CollatzResearch.WordTrace]
  refine ⟨60105473778280391724775997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160281263408747711266069325 60105473778280391724775997)
  ·
    refine ⟨22539552666855146896790999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60105473778280391724775997 22539552666855146896790999)
    ·
      refine ⟨33809329000282720345186499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22539552666855146896790999 33809329000282720345186499)
      ·
        refine ⟨50713993500424080517779749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33809329000282720345186499 50713993500424080517779749)
        ·
          refine ⟨9508873781329515097083703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50713993500424080517779749 9508873781329515097083703)
          ·
            refine ⟨14263310671994272645625555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9508873781329515097083703 14263310671994272645625555)
            ·
              refine ⟨21394966007991408968438333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14263310671994272645625555 21394966007991408968438333)
              ·
                refine ⟨8023112252996778363164375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21394966007991408968438333 8023112252996778363164375)
                ·
                  refine ⟨12034668379495167544746563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8023112252996778363164375 12034668379495167544746563)
                  ·
                    refine ⟨18052002569242751317119845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12034668379495167544746563 18052002569242751317119845)
                    ·
                      refine ⟨3384750481733015871959971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18052002569242751317119845 3384750481733015871959971)
                      ·
                        rfl

theorem cell23_6591778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_6591778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591778 prefixEnd_6591778 := by exact prefixLift 6591778
  have htrace : WordTrace (prefixWord ++ tailWord_6591778) baseStart_6591778 baseEnd_6591778 := by
    simpa [prefixWord, tailWord_6591778, baseEnd_6591778] using wordTrace_append hprefix tailTrace_6591778
  have hstable : (prefixWord ++ tailWord_6591778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591778).length < 2 ^ (prefixWord ++ tailWord_6591778).sum := by decide
  have hdescent : baseEnd_6591778 < baseStart_6591778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591784 : List Nat := [2, 1, 5, 1, 2, 2, 10]
def baseStart_6591784 : Nat := 118140960795 + 6591784 * 2 ^ 59
def prefixEnd_6591784 : Nat := 4983230072969 + 3 ^ 40 * 6591784 * 2
def baseEnd_6591784 : Nat := 41787081019962257388703

theorem tailTrace_6591784 : CollatzResearch.WordTrace tailWord_6591784 prefixEnd_6591784 41787081019962257388703 := by
  unfold tailWord_6591784
  simp only [CollatzResearch.WordTrace]
  refine ⟨120211056975549914961911203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160281409300733219949214937 120211056975549914961911203)
  ·
    refine ⟨180316585463324872442866805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120211056975549914961911203 180316585463324872442866805)
    ·
      refine ⟨16904679887186706791518763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180316585463324872442866805 16904679887186706791518763)
      ·
        refine ⟨25357019830780060187278145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16904679887186706791518763 25357019830780060187278145)
        ·
          refine ⟨19017764873085045140458609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25357019830780060187278145 19017764873085045140458609)
          ·
            refine ⟨14263323654813783855343957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19017764873085045140458609 14263323654813783855343957)
            ·
              refine ⟨41787081019962257388703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14263323654813783855343957 41787081019962257388703)
              ·
                rfl

theorem cell23_6591784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 10].length) (baseStart_6591784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591784 prefixEnd_6591784 := by exact prefixLift 6591784
  have htrace : WordTrace (prefixWord ++ tailWord_6591784) baseStart_6591784 baseEnd_6591784 := by
    simpa [prefixWord, tailWord_6591784, baseEnd_6591784] using wordTrace_append hprefix tailTrace_6591784
  have hstable : (prefixWord ++ tailWord_6591784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591784).length < 2 ^ (prefixWord ++ tailWord_6591784).sum := by decide
  have hdescent : baseEnd_6591784 < baseStart_6591784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6591795 : List Nat := [1, 1, 1, 2, 5, 2, 2, 4, 1, 2, 2]
def baseStart_6591795 : Nat := 118140960795 + 6591795 * 2 ^ 59
def prefixEnd_6591795 : Nat := 4983230072969 + 3 ^ 40 * 6591795 * 2
def baseEnd_6591795 : Nat := 3384759210904142305447393

theorem tailTrace_6591795 : CollatzResearch.WordTrace tailWord_6591795 prefixEnd_6591795 3384759210904142305447393 := by
  unfold tailWord_6591795
  simp only [CollatzResearch.WordTrace]
  refine ⟨240422515154059978802472839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160281676769373319201648559 240422515154059978802472839)
  ·
    refine ⟨360633772731089968203709259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240422515154059978802472839 360633772731089968203709259)
    ·
      refine ⟨540950659096634952305563889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360633772731089968203709259 540950659096634952305563889)
      ·
        refine ⟨405712994322476214229172917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540950659096634952305563889 405712994322476214229172917)
        ·
          refine ⟨38035593217732145083984961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 405712994322476214229172917 38035593217732145083984961)
          ·
            refine ⟨28526694913299108812988721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38035593217732145083984961 28526694913299108812988721)
            ·
              refine ⟨21395021184974331609741541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28526694913299108812988721 21395021184974331609741541)
              ·
                refine ⟨4011566472182687176826539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21395021184974331609741541 4011566472182687176826539)
                ·
                  refine ⟨6017349708274030765239809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011566472182687176826539 6017349708274030765239809)
                  ·
                    refine ⟨4513012281205523073929857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6017349708274030765239809 4513012281205523073929857)
                    ·
                      refine ⟨3384759210904142305447393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513012281205523073929857 3384759210904142305447393)
                      ·
                        rfl

theorem cell23_6591795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 2, 2].length) (baseStart_6591795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591795 prefixEnd_6591795 := by exact prefixLift 6591795
  have htrace : WordTrace (prefixWord ++ tailWord_6591795) baseStart_6591795 baseEnd_6591795 := by
    simpa [prefixWord, tailWord_6591795, baseEnd_6591795] using wordTrace_append hprefix tailTrace_6591795
  have hstable : (prefixWord ++ tailWord_6591795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591795).length < 2 ^ (prefixWord ++ tailWord_6591795).sum := by decide
  have hdescent : baseEnd_6591795 < baseStart_6591795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
