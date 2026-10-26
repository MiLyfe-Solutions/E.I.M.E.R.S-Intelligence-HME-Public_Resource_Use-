import V185TrunkScan22Chunk246

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2204092 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_2204092 : Nat := 118140960795 + 2204092 * 2 ^ 59
def prefixEnd_2204092 : Nat := 4983230072969 + 3 ^ 40 * 2204092 * 2
def baseEnd_2204092 : Nat := 754505735153130475742381

theorem tailTrace_2204092 : CollatzResearch.WordTrace tailWord_2204092 prefixEnd_2204092 754505735153130475742381 := by
  unfold tailWord_2204092
  simp only [CollatzResearch.WordTrace]
  refine ⟨40194919765479293894835265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53593226353972391859780353 40194919765479293894835265)
  ·
    refine ⟨30146189824109470421126449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40194919765479293894835265 30146189824109470421126449)
    ·
      refine ⟨22609642368082102815844837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30146189824109470421126449 22609642368082102815844837)
      ·
        refine ⟨4239307944015394277970907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22609642368082102815844837 4239307944015394277970907)
        ·
          refine ⟨6358961916023091416956361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239307944015394277970907 6358961916023091416956361)
          ·
            refine ⟨4769221437017318562717271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6358961916023091416956361 4769221437017318562717271)
            ·
              refine ⟨7153832155525977844075907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4769221437017318562717271 7153832155525977844075907)
              ·
                refine ⟨10730748233288966766113861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7153832155525977844075907 10730748233288966766113861)
                ·
                  refine ⟨2012015293741681268646349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10730748233288966766113861 2012015293741681268646349)
                  ·
                    refine ⟨754505735153130475742381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2012015293741681268646349 754505735153130475742381)
                    ·
                      rfl

theorem cell22_2204092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_2204092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204092 prefixEnd_2204092 := by exact prefixLift 2204092
  have htrace : WordTrace (prefixWord ++ tailWord_2204092) baseStart_2204092 baseEnd_2204092 := by
    simpa [prefixWord, tailWord_2204092, baseEnd_2204092] using wordTrace_append hprefix tailTrace_2204092
  have hstable : (prefixWord ++ tailWord_2204092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204092).length < 2 ^ (prefixWord ++ tailWord_2204092).sum := by decide
  have hdescent : baseEnd_2204092 < baseStart_2204092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204137 : List Nat := [1, 2, 1, 1, 1, 2, 1, 9, 1, 3]
def baseStart_2204137 : Nat := 118140960795 + 2204137 * 2 ^ 59
def prefixEnd_2204137 : Nat := 4983230072969 + 3 ^ 40 * 2204137 * 2
def baseEnd_2204137 : Nat := 754521139572765358367243

theorem tailTrace_2204137 : CollatzResearch.WordTrace tailWord_2204137 prefixEnd_2204137 754521139572765358367243 := by
  unfold tailWord_2204137
  simp only [CollatzResearch.WordTrace]
  refine ⟨80391480815795560475058665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53594320543863706983372443 80391480815795560475058665)
  ·
    refine ⟨60293610611846670356293999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80391480815795560475058665 60293610611846670356293999)
    ·
      refine ⟨90440415917770005534440999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60293610611846670356293999 90440415917770005534440999)
      ·
        refine ⟨135660623876655008301661499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90440415917770005534440999 135660623876655008301661499)
        ·
          refine ⟨203490935814982512452492249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135660623876655008301661499 203490935814982512452492249)
          ·
            refine ⟨152618201861236884339369187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203490935814982512452492249 152618201861236884339369187)
            ·
              refine ⟨228927302791855326509053781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152618201861236884339369187 228927302791855326509053781)
              ·
                refine ⟨1341370914796027303763987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 228927302791855326509053781 1341370914796027303763987)
                ·
                  refine ⟨2012056372194040955645981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341370914796027303763987 2012056372194040955645981)
                  ·
                    refine ⟨754521139572765358367243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2012056372194040955645981 754521139572765358367243)
                    ·
                      rfl

theorem cell22_2204137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 3].length) (baseStart_2204137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204137 prefixEnd_2204137 := by exact prefixLift 2204137
  have htrace : WordTrace (prefixWord ++ tailWord_2204137) baseStart_2204137 baseEnd_2204137 := by
    simpa [prefixWord, tailWord_2204137, baseEnd_2204137] using wordTrace_append hprefix tailTrace_2204137
  have hstable : (prefixWord ++ tailWord_2204137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204137).length < 2 ^ (prefixWord ++ tailWord_2204137).sum := by decide
  have hdescent : baseEnd_2204137 < baseStart_2204137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204150 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_2204150 : Nat := 118140960795 + 2204150 * 2 ^ 59
def prefixEnd_2204150 : Nat := 4983230072969 + 3 ^ 40 * 2204150 * 2
def baseEnd_2204150 : Nat := 251508529912812552597401

theorem tailTrace_2204150 : CollatzResearch.WordTrace tailWord_2204150 prefixEnd_2204150 251508529912812552597401 := by
  unfold tailWord_2204150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5024497185296778980955119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53594636643165642463521269 5024497185296778980955119)
  ·
    refine ⟨7536745777945168471432679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5024497185296778980955119 7536745777945168471432679)
    ·
      refine ⟨11305118666917752707149019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7536745777945168471432679 11305118666917752707149019)
      ·
        refine ⟨16957678000376629060723529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11305118666917752707149019 16957678000376629060723529)
        ·
          refine ⟨12718258500282471795542647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16957678000376629060723529 12718258500282471795542647)
          ·
            refine ⟨19077387750423707693313971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12718258500282471795542647 19077387750423707693313971)
            ·
              refine ⟨28616081625635561539970957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19077387750423707693313971 28616081625635561539970957)
              ·
                refine ⟨10731030609613335577489109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28616081625635561539970957 10731030609613335577489109)
                ·
                  refine ⟨251508529912812552597401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10731030609613335577489109 251508529912812552597401)
                  ·
                    rfl

theorem cell22_2204150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_2204150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204150 prefixEnd_2204150 := by exact prefixLift 2204150
  have htrace : WordTrace (prefixWord ++ tailWord_2204150) baseStart_2204150 baseEnd_2204150 := by
    simpa [prefixWord, tailWord_2204150, baseEnd_2204150] using wordTrace_append hprefix tailTrace_2204150
  have hstable : (prefixWord ++ tailWord_2204150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204150).length < 2 ^ (prefixWord ++ tailWord_2204150).sum := by decide
  have hdescent : baseEnd_2204150 < baseStart_2204150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204167 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 5]
def baseStart_2204167 : Nat := 118140960795 + 2204167 * 2 ^ 59
def prefixEnd_2204167 : Nat := 4983230072969 + 3 ^ 40 * 2204167 * 2
def baseEnd_2204167 : Nat := 251510469728618426705717

theorem tailTrace_2204167 : CollatzResearch.WordTrace tailWord_2204167 prefixEnd_2204167 251510469728618426705717 := by
  unfold tailWord_2204167
  simp only [CollatzResearch.WordTrace]
  refine ⟨80392575005686875598650755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53595050003791250399100503 80392575005686875598650755)
  ·
    refine ⟨120588862508530313397976133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80392575005686875598650755 120588862508530313397976133)
    ·
      refine ⟨22610411720349433762120525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120588862508530313397976133 22610411720349433762120525)
      ·
        refine ⟨8478904395131037660795197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22610411720349433762120525 8478904395131037660795197)
        ·
          refine ⟨3179589148174139122798199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8478904395131037660795197 3179589148174139122798199)
          ·
            refine ⟨4769383722261208684197299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179589148174139122798199 4769383722261208684197299)
            ·
              refine ⟨7154075583391813026295949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4769383722261208684197299 7154075583391813026295949)
              ·
                refine ⟨2682778343771929884860981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7154075583391813026295949 2682778343771929884860981)
                ·
                  refine ⟨251510469728618426705717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2682778343771929884860981 251510469728618426705717)
                  ·
                    rfl

theorem cell22_2204167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 5].length) (baseStart_2204167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204167 prefixEnd_2204167 := by exact prefixLift 2204167
  have htrace : WordTrace (prefixWord ++ tailWord_2204167) baseStart_2204167 baseEnd_2204167 := by
    simpa [prefixWord, tailWord_2204167, baseEnd_2204167] using wordTrace_append hprefix tailTrace_2204167
  have hstable : (prefixWord ++ tailWord_2204167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204167).length < 2 ^ (prefixWord ++ tailWord_2204167).sum := by decide
  have hdescent : baseEnd_2204167 < baseStart_2204167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204205 : List Nat := [1, 5, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2204205 : Nat := 118140960795 + 2204205 * 2 ^ 59
def prefixEnd_2204205 : Nat := 4983230072969 + 3 ^ 40 * 2204205 * 2
def baseEnd_2204205 : Nat := 754544417362435847667035

theorem tailTrace_2204205 : CollatzResearch.WordTrace tailWord_2204205 prefixEnd_2204205 754544417362435847667035 := by
  unfold tailWord_2204205
  simp only [CollatzResearch.WordTrace]
  refine ⟨80393960979549208088534069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53595973986366138725689379 80393960979549208088534069)
  ·
    refine ⟨7536933841832738258300069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80393960979549208088534069 7536933841832738258300069)
    ·
      refine ⟨1413175095343638423431263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7536933841832738258300069 1413175095343638423431263)
      ·
        refine ⟨2119762643015457635146895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413175095343638423431263 2119762643015457635146895)
        ·
          refine ⟨3179643964523186452720343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119762643015457635146895 3179643964523186452720343)
          ·
            refine ⟨4769465946784779679080515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179643964523186452720343 4769465946784779679080515)
            ·
              refine ⟨7154198920177169518620773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4769465946784779679080515 7154198920177169518620773)
              ·
                refine ⟨1341412297533219284741395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7154198920177169518620773 1341412297533219284741395)
                ·
                  refine ⟨2012118446299828927112093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341412297533219284741395 2012118446299828927112093)
                  ·
                    refine ⟨754544417362435847667035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2012118446299828927112093 754544417362435847667035)
                    ·
                      rfl

theorem cell22_2204205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2204205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204205 prefixEnd_2204205 := by exact prefixLift 2204205
  have htrace : WordTrace (prefixWord ++ tailWord_2204205) baseStart_2204205 baseEnd_2204205 := by
    simpa [prefixWord, tailWord_2204205, baseEnd_2204205] using wordTrace_append hprefix tailTrace_2204205
  have hstable : (prefixWord ++ tailWord_2204205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204205).length < 2 ^ (prefixWord ++ tailWord_2204205).sum := by decide
  have hdescent : baseEnd_2204205 < baseStart_2204205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204261 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_2204261 : Nat := 118140960795 + 2204261 * 2 ^ 59
def prefixEnd_2204261 : Nat := 4983230072969 + 3 ^ 40 * 2204261 * 2
def baseEnd_2204261 : Nat := 754563587306870368266863

theorem tailTrace_2204261 : CollatzResearch.WordTrace tailWord_2204261 prefixEnd_2204261 754563587306870368266863 := by
  unfold tailWord_2204261
  simp only [CollatzResearch.WordTrace]
  refine ⟨80396003467346329652572637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53597335644897553101715091 80396003467346329652572637)
  ·
    refine ⟨30148501300254873619714739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80396003467346329652572637 30148501300254873619714739)
    ·
      refine ⟨45222751950382310429572109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30148501300254873619714739 45222751950382310429572109)
      ·
        refine ⟨16958531981393366411089541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45222751950382310429572109 16958531981393366411089541)
        ·
          refine ⟨3179724746511256202079289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16958531981393366411089541 3179724746511256202079289)
          ·
            refine ⟨2384793559883442151559467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3179724746511256202079289 2384793559883442151559467)
            ·
              refine ⟨3577190339825163227339201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384793559883442151559467 3577190339825163227339201)
              ·
                refine ⟨2682892754868872420504401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3577190339825163227339201 2682892754868872420504401)
                ·
                  refine ⟨2012169566151654315378301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682892754868872420504401 2012169566151654315378301)
                  ·
                    refine ⟨754563587306870368266863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2012169566151654315378301 754563587306870368266863)
                    ·
                      rfl

theorem cell22_2204261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_2204261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204261 prefixEnd_2204261 := by exact prefixLift 2204261
  have htrace : WordTrace (prefixWord ++ tailWord_2204261) baseStart_2204261 baseEnd_2204261 := by
    simpa [prefixWord, tailWord_2204261, baseEnd_2204261] using wordTrace_append hprefix tailTrace_2204261
  have hstable : (prefixWord ++ tailWord_2204261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204261).length < 2 ^ (prefixWord ++ tailWord_2204261).sum := by decide
  have hdescent : baseEnd_2204261 < baseStart_2204261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204278 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_2204278 : Nat := 118140960795 + 2204278 * 2 ^ 59
def prefixEnd_2204278 : Nat := 4983230072969 + 3 ^ 40 * 2204278 * 2
def baseEnd_2204278 : Nat := 754569406754287990591811

theorem tailTrace_2204278 : CollatzResearch.WordTrace tailWord_2204278 prefixEnd_2204278 754569406754287990591811 := by
  unfold tailWord_2204278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5024788969267796347246343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53597749005523161037294325 5024788969267796347246343)
  ·
    refine ⟨7537183453901694520869515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5024788969267796347246343 7537183453901694520869515)
    ·
      refine ⟨11305775180852541781304273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7537183453901694520869515 11305775180852541781304273)
      ·
        refine ⟨8479331385639406335978205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11305775180852541781304273 8479331385639406335978205)
        ·
          refine ⟨3179749269614777375991827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8479331385639406335978205 3179749269614777375991827)
          ·
            refine ⟨4769623904422166063987741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179749269614777375991827 4769623904422166063987741)
            ·
              refine ⟨1788608964158312273995403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4769623904422166063987741 1788608964158312273995403)
              ·
                refine ⟨2682913446237468410993105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788608964158312273995403 2682913446237468410993105)
                ·
                  refine ⟨2012185084678101308244829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682913446237468410993105 2012185084678101308244829)
                  ·
                    refine ⟨754569406754287990591811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2012185084678101308244829 754569406754287990591811)
                    ·
                      rfl

theorem cell22_2204278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_2204278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204278 prefixEnd_2204278 := by exact prefixLift 2204278
  have htrace : WordTrace (prefixWord ++ tailWord_2204278) baseStart_2204278 baseEnd_2204278 := by
    simpa [prefixWord, tailWord_2204278, baseEnd_2204278] using wordTrace_append hprefix tailTrace_2204278
  have hstable : (prefixWord ++ tailWord_2204278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204278).length < 2 ^ (prefixWord ++ tailWord_2204278).sum := by decide
  have hdescent : baseEnd_2204278 < baseStart_2204278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204300 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_2204300 : Nat := 118140960795 + 2204300 * 2 ^ 59
def prefixEnd_2204300 : Nat := 4983230072969 + 3 ^ 40 * 2204300 * 2
def baseEnd_2204300 : Nat := 754576937803887266541743

theorem tailTrace_2204300 : CollatzResearch.WordTrace tailWord_2204300 prefixEnd_2204300 754576937803887266541743 := by
  unfold tailWord_2204300
  simp only [CollatzResearch.WordTrace]
  refine ⟨40198712957102519656621177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53598283942803359542161569 40198712957102519656621177)
  ·
    refine ⟨30149034717826889742465883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40198712957102519656621177 30149034717826889742465883)
    ·
      refine ⟨45223552076740334613698825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30149034717826889742465883 45223552076740334613698825)
      ·
        refine ⟨33917664057555250960274119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45223552076740334613698825 33917664057555250960274119)
        ·
          refine ⟨50876496086332876440411179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33917664057555250960274119 50876496086332876440411179)
          ·
            refine ⟨76314744129499314660616769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50876496086332876440411179 76314744129499314660616769)
            ·
              refine ⟨57236058097124485995462577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76314744129499314660616769 57236058097124485995462577)
              ·
                refine ⟨42927043572843364496596933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57236058097124485995462577 42927043572843364496596933)
                ·
                  refine ⟨8048820669908130843111925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42927043572843364496596933 8048820669908130843111925)
                  ·
                    refine ⟨754576937803887266541743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8048820669908130843111925 754576937803887266541743)
                    ·
                      rfl

theorem cell22_2204300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_2204300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204300 prefixEnd_2204300 := by exact prefixLift 2204300
  have htrace : WordTrace (prefixWord ++ tailWord_2204300) baseStart_2204300 baseEnd_2204300 := by
    simpa [prefixWord, tailWord_2204300, baseEnd_2204300] using wordTrace_append hprefix tailTrace_2204300
  have hstable : (prefixWord ++ tailWord_2204300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204300).length < 2 ^ (prefixWord ++ tailWord_2204300).sum := by decide
  have hdescent : baseEnd_2204300 < baseStart_2204300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204349 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_2204349 : Nat := 118140960795 + 2204349 * 2 ^ 59
def prefixEnd_2204349 : Nat := 4983230072969 + 3 ^ 40 * 2204349 * 2
def baseEnd_2204349 : Nat := 754593711505267472066593

theorem tailTrace_2204349 : CollatzResearch.WordTrace tailWord_2204349 prefixEnd_2204349 754593711505267472066593 := by
  unfold tailWord_2204349
  simp only [CollatzResearch.WordTrace]
  refine ⟨80399213091027520681776101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53599475394018347121184067 80399213091027520681776101)
  ·
    refine ⟨15074852454567660127833019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80399213091027520681776101 15074852454567660127833019)
    ·
      refine ⟨22612278681851490191749529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15074852454567660127833019 22612278681851490191749529)
      ·
        refine ⟨16959209011388617643812147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22612278681851490191749529 16959209011388617643812147)
        ·
          refine ⟨25438813517082926465718221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16959209011388617643812147 25438813517082926465718221)
          ·
            refine ⟨9539555068906097424644333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25438813517082926465718221 9539555068906097424644333)
            ·
              refine ⟨3577333150839786534241625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9539555068906097424644333 3577333150839786534241625)
              ·
                refine ⟨2682999863129839900681219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3577333150839786534241625 2682999863129839900681219)
                ·
                  refine ⟨4024499794694759851021829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682999863129839900681219 4024499794694759851021829)
                  ·
                    refine ⟨754593711505267472066593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4024499794694759851021829 754593711505267472066593)
                    ·
                      rfl

theorem cell22_2204349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_2204349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204349 prefixEnd_2204349 := by exact prefixLift 2204349
  have htrace : WordTrace (prefixWord ++ tailWord_2204349) baseStart_2204349 baseEnd_2204349 := by
    simpa [prefixWord, tailWord_2204349, baseEnd_2204349] using wordTrace_append hprefix tailTrace_2204349
  have hstable : (prefixWord ++ tailWord_2204349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204349).length < 2 ^ (prefixWord ++ tailWord_2204349).sum := by decide
  have hdescent : baseEnd_2204349 < baseStart_2204349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204362 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_2204362 : Nat := 118140960795 + 2204362 * 2 ^ 59
def prefixEnd_2204362 : Nat := 4983230072969 + 3 ^ 40 * 2204362 * 2
def baseEnd_2204362 : Nat := 754598161670939771491553

theorem tailTrace_2204362 : CollatzResearch.WordTrace tailWord_2204362 prefixEnd_2204362 754598161670939771491553 := by
  unfold tailWord_2204362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20099921809995105975499835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53599791493320282601332893 20099921809995105975499835)
  ·
    refine ⟨30149882714992658963249753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20099921809995105975499835 30149882714992658963249753)
    ·
      refine ⟨22612412036244494222437315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30149882714992658963249753 22612412036244494222437315)
      ·
        refine ⟨33918618054366741333655973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22612412036244494222437315 33918618054366741333655973)
        ·
          refine ⟨6359740885193764000060495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33918618054366741333655973 6359740885193764000060495)
          ·
            refine ⟨9539611327790646000090743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6359740885193764000060495 9539611327790646000090743)
            ·
              refine ⟨14309416991685969000136115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9539611327790646000090743 14309416991685969000136115)
              ·
                refine ⟨21464125487528953500204173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14309416991685969000136115 21464125487528953500204173)
                ·
                  refine ⟨8049047057823357562576565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21464125487528953500204173 8049047057823357562576565)
                  ·
                    refine ⟨754598161670939771491553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8049047057823357562576565 754598161670939771491553)
                    ·
                      rfl

theorem cell22_2204362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_2204362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204362 prefixEnd_2204362 := by exact prefixLift 2204362
  have htrace : WordTrace (prefixWord ++ tailWord_2204362) baseStart_2204362 baseEnd_2204362 := by
    simpa [prefixWord, tailWord_2204362, baseEnd_2204362] using wordTrace_append hprefix tailTrace_2204362
  have hstable : (prefixWord ++ tailWord_2204362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204362).length < 2 ^ (prefixWord ++ tailWord_2204362).sum := by decide
  have hdescent : baseEnd_2204362 < baseStart_2204362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204366 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_2204366 : Nat := 118140960795 + 2204366 * 2 ^ 59
def prefixEnd_2204366 : Nat := 4983230072969 + 3 ^ 40 * 2204366 * 2
def baseEnd_2204366 : Nat := 754599530952685094391541

theorem tailTrace_2204366 : CollatzResearch.WordTrace tailWord_2204366 prefixEnd_2204366 754599530952685094391541 := by
  unfold tailWord_2204366
  simp only [CollatzResearch.WordTrace]
  refine ⟨10049979141495741573143119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53599888754643955056763301 10049979141495741573143119)
  ·
    refine ⟨15074968712243612359714679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10049979141495741573143119 15074968712243612359714679)
    ·
      refine ⟨22612453068365418539572019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15074968712243612359714679 22612453068365418539572019)
      ·
        refine ⟨33918679602548127809358029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22612453068365418539572019 33918679602548127809358029)
        ·
          refine ⟨12719504850955547928509261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33918679602548127809358029 12719504850955547928509261)
          ·
            refine ⟨4769814319108330473190973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12719504850955547928509261 4769814319108330473190973)
            ·
              refine ⟨1788680369665623927446615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4769814319108330473190973 1788680369665623927446615)
              ·
                refine ⟨2683020554498435891169923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788680369665623927446615 2683020554498435891169923)
                ·
                  refine ⟨4024530831747653836754885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683020554498435891169923 4024530831747653836754885)
                  ·
                    refine ⟨754599530952685094391541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4024530831747653836754885 754599530952685094391541)
                    ·
                      rfl

theorem cell22_2204366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_2204366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204366 prefixEnd_2204366 := by exact prefixLift 2204366
  have htrace : WordTrace (prefixWord ++ tailWord_2204366) baseStart_2204366 baseEnd_2204366 := by
    simpa [prefixWord, tailWord_2204366, baseEnd_2204366] using wordTrace_append hprefix tailTrace_2204366
  have hstable : (prefixWord ++ tailWord_2204366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204366).length < 2 ^ (prefixWord ++ tailWord_2204366).sum := by decide
  have hdescent : baseEnd_2204366 < baseStart_2204366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204375 : List Nat := [1, 1, 3, 2, 1, 14]
def baseStart_2204375 : Nat := 118140960795 + 2204375 * 2 ^ 59
def prefixEnd_2204375 : Nat := 4983230072969 + 3 ^ 40 * 2204375 * 2
def baseEnd_2204375 : Nat := 9316081627612494702673

theorem tailTrace_2204375 : CollatzResearch.WordTrace tailWord_2204375 prefixEnd_2204375 9316081627612494702673 := by
  unfold tailWord_2204375
  simp only [CollatzResearch.WordTrace]
  refine ⟨80400161388933327122222579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53600107592622218081481719 80400161388933327122222579)
  ·
    refine ⟨120600242083399990683333869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80400161388933327122222579 120600242083399990683333869)
    ·
      refine ⟨45225090781274996506250201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120600242083399990683333869 45225090781274996506250201)
      ·
        refine ⟨33918818085956247379687651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45225090781274996506250201 33918818085956247379687651)
        ·
          refine ⟨50878227128934371069531477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33918818085956247379687651 50878227128934371069531477)
          ·
            refine ⟨9316081627612494702673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 50878227128934371069531477 9316081627612494702673)
            ·
              rfl

theorem cell22_2204375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 14].length) (baseStart_2204375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204375 prefixEnd_2204375 := by exact prefixLift 2204375
  have htrace : WordTrace (prefixWord ++ tailWord_2204375) baseStart_2204375 baseEnd_2204375 := by
    simpa [prefixWord, tailWord_2204375, baseEnd_2204375] using wordTrace_append hprefix tailTrace_2204375
  have hstable : (prefixWord ++ tailWord_2204375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204375).length < 2 ^ (prefixWord ++ tailWord_2204375).sum := by decide
  have hdescent : baseEnd_2204375 < baseStart_2204375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204377 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_2204377 : Nat := 118140960795 + 2204377 * 2 ^ 59
def prefixEnd_2204377 : Nat := 4983230072969 + 3 ^ 40 * 2204377 * 2
def baseEnd_2204377 : Nat := 754603296477484732366507

theorem tailTrace_2204377 : CollatzResearch.WordTrace tailWord_2204377 prefixEnd_2204377 754603296477484732366507 := by
  unfold tailWord_2204377
  simp only [CollatzResearch.WordTrace]
  refine ⟨80400234334926081463795385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53600156223284054309196923 80400234334926081463795385)
  ·
    refine ⟨60300175751194561097846539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80400234334926081463795385 60300175751194561097846539)
    ·
      refine ⟨90450263626791841646769809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60300175751194561097846539 90450263626791841646769809)
      ·
        refine ⟨67837697720093881235077357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90450263626791841646769809 67837697720093881235077357)
        ·
          refine ⟨25439136645035205463154009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67837697720093881235077357 25439136645035205463154009)
          ·
            refine ⟨19079352483776404097365507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25439136645035205463154009 19079352483776404097365507)
            ·
              refine ⟨28619028725664606146048261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19079352483776404097365507 28619028725664606146048261)
              ·
                refine ⟨5366067886062113652384049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28619028725664606146048261 5366067886062113652384049)
                ·
                  refine ⟨4024550914546585239288037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5366067886062113652384049 4024550914546585239288037)
                  ·
                    refine ⟨754603296477484732366507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4024550914546585239288037 754603296477484732366507)
                    ·
                      rfl

theorem cell22_2204377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_2204377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204377 prefixEnd_2204377 := by exact prefixLift 2204377
  have htrace : WordTrace (prefixWord ++ tailWord_2204377) baseStart_2204377 baseEnd_2204377 := by
    simpa [prefixWord, tailWord_2204377, baseEnd_2204377] using wordTrace_append hprefix tailTrace_2204377
  have hstable : (prefixWord ++ tailWord_2204377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204377).length < 2 ^ (prefixWord ++ tailWord_2204377).sum := by decide
  have hdescent : baseEnd_2204377 < baseStart_2204377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204437 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 7]
def baseStart_2204437 : Nat := 118140960795 + 2204437 * 2 ^ 59
def prefixEnd_2204437 : Nat := 4983230072969 + 3 ^ 40 * 2204437 * 2
def baseEnd_2204437 : Nat := 251541278567888191955441

theorem tailTrace_2204437 : CollatzResearch.WordTrace tailWord_2204437 prefixEnd_2204437 251541278567888191955441 := by
  unfold tailWord_2204437
  simp only [CollatzResearch.WordTrace]
  refine ⟨80402422714708711710979565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53601615143139141140653043 80402422714708711710979565)
  ·
    refine ⟨30150908518015766891617337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80402422714708711710979565 30150908518015766891617337)
    ·
      refine ⟨22613181388511825168713003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30150908518015766891617337 22613181388511825168713003)
      ·
        refine ⟨33919772082767737753069505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22613181388511825168713003 33919772082767737753069505)
        ·
          refine ⟨25439829062075803314802129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33919772082767737753069505 25439829062075803314802129)
          ·
            refine ⟨19079871796556852486101597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25439829062075803314802129 19079871796556852486101597)
            ·
              refine ⟨7154951923708819682288099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19079871796556852486101597 7154951923708819682288099)
              ·
                refine ⟨10732427885563229523432149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7154951923708819682288099 10732427885563229523432149)
                ·
                  refine ⟨251541278567888191955441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10732427885563229523432149 251541278567888191955441)
                  ·
                    rfl

theorem cell22_2204437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_2204437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204437 prefixEnd_2204437 := by exact prefixLift 2204437
  have htrace : WordTrace (prefixWord ++ tailWord_2204437) baseStart_2204437 baseEnd_2204437 := by
    simpa [prefixWord, tailWord_2204437, baseEnd_2204437] using wordTrace_append hprefix tailTrace_2204437
  have hstable : (prefixWord ++ tailWord_2204437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204437).length < 2 ^ (prefixWord ++ tailWord_2204437).sum := by decide
  have hdescent : baseEnd_2204437 < baseStart_2204437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204499 : List Nat := [1, 1, 1, 2, 1, 1, 3, 8, 4]
def baseStart_2204499 : Nat := 118140960795 + 2204499 * 2 ^ 59
def prefixEnd_2204499 : Nat := 4983230072969 + 3 ^ 40 * 2204499 * 2
def baseEnd_2204499 : Nat := 251548353190239026938711

theorem tailTrace_2204499 : CollatzResearch.WordTrace tailWord_2204499 prefixEnd_2204499 251548353190239026938711 := by
  unfold tailWord_2204499
  simp only [CollatzResearch.WordTrace]
  refine ⟨80404684040484096299736551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53603122693656064199824367 80404684040484096299736551)
  ·
    refine ⟨120607026060726144449604827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80404684040484096299736551 120607026060726144449604827)
    ·
      refine ⟨180910539091089216674407241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120607026060726144449604827 180910539091089216674407241)
      ·
        refine ⟨135682904318316912505805431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180910539091089216674407241 135682904318316912505805431)
        ·
          refine ⟨203524356477475368758708147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135682904318316912505805431 203524356477475368758708147)
          ·
            refine ⟨305286534716213053138062221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203524356477475368758708147 305286534716213053138062221)
            ·
              refine ⟨114482450518579894926773333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305286534716213053138062221 114482450518579894926773333)
              ·
                refine ⟨1341591217014608143673125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 114482450518579894926773333 1341591217014608143673125)
                ·
                  refine ⟨251548353190239026938711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341591217014608143673125 251548353190239026938711)
                  ·
                    rfl

theorem cell22_2204499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 4].length) (baseStart_2204499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204499 prefixEnd_2204499 := by exact prefixLift 2204499
  have htrace : WordTrace (prefixWord ++ tailWord_2204499) baseStart_2204499 baseEnd_2204499 := by
    simpa [prefixWord, tailWord_2204499, baseEnd_2204499] using wordTrace_append hprefix tailTrace_2204499
  have hstable : (prefixWord ++ tailWord_2204499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204499).length < 2 ^ (prefixWord ++ tailWord_2204499).sum := by decide
  have hdescent : baseEnd_2204499 < baseStart_2204499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204529 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_2204529 : Nat := 118140960795 + 2204529 * 2 ^ 59
def prefixEnd_2204529 : Nat := 4983230072969 + 3 ^ 40 * 2204529 * 2
def baseEnd_2204529 : Nat := 754655329183807002566041

theorem tailTrace_2204529 : CollatzResearch.WordTrace tailWord_2204529 prefixEnd_2204529 754655329183807002566041 := by
  unfold tailWord_2204529
  simp only [CollatzResearch.WordTrace]
  refine ⟨80405778230375411423328641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53603852153583607615552427 80405778230375411423328641)
  ·
    refine ⟨60304333672781558567496481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80405778230375411423328641 60304333672781558567496481)
    ·
      refine ⟨45228250254586168925622361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60304333672781558567496481 45228250254586168925622361)
      ·
        refine ⟨33921187690939626694216771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45228250254586168925622361 33921187690939626694216771)
        ·
          refine ⟨50881781536409440041325157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33921187690939626694216771 50881781536409440041325157)
          ·
            refine ⟨9540334038076770007748467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50881781536409440041325157 9540334038076770007748467)
            ·
              refine ⟨14310501057115155011622701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9540334038076770007748467 14310501057115155011622701)
              ·
                refine ⟨5366437896418183129358513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14310501057115155011622701 5366437896418183129358513)
                ·
                  refine ⟨4024828422313637347018885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5366437896418183129358513 4024828422313637347018885)
                  ·
                    refine ⟨754655329183807002566041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4024828422313637347018885 754655329183807002566041)
                    ·
                      rfl

theorem cell22_2204529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_2204529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204529 prefixEnd_2204529 := by exact prefixLift 2204529
  have htrace : WordTrace (prefixWord ++ tailWord_2204529) baseStart_2204529 baseEnd_2204529 := by
    simpa [prefixWord, tailWord_2204529, baseEnd_2204529] using wordTrace_append hprefix tailTrace_2204529
  have hstable : (prefixWord ++ tailWord_2204529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204529).length < 2 ^ (prefixWord ++ tailWord_2204529).sum := by decide
  have hdescent : baseEnd_2204529 < baseStart_2204529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204674 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2204674 : Nat := 118140960795 + 2204674 * 2 ^ 59
def prefixEnd_2204674 : Nat := 4983230072969 + 3 ^ 40 * 2204674 * 2
def baseEnd_2204674 : Nat := 251568321882358319230199

theorem tailTrace_2204674 : CollatzResearch.WordTrace tailWord_2204674 prefixEnd_2204674 251568321882358319230199 := by
  unfold tailWord_2204674
  simp only [CollatzResearch.WordTrace]
  refine ⟨20102766703712525296839269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53607377876566734124904717 20102766703712525296839269)
  ·
    refine ⟨3769268756946098493157363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20102766703712525296839269 3769268756946098493157363)
    ·
      refine ⟨5653903135419147739736045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3769268756946098493157363 5653903135419147739736045)
      ·
        refine ⟨2120213675782180402401017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5653903135419147739736045 2120213675782180402401017)
        ·
          refine ⟨1590160256836635301800763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2120213675782180402401017 1590160256836635301800763)
          ·
            refine ⟨2385240385254952952701145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590160256836635301800763 2385240385254952952701145)
            ·
              refine ⟨1788930288941214714525859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2385240385254952952701145 1788930288941214714525859)
              ·
                refine ⟨2683395433411822071788789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788930288941214714525859 2683395433411822071788789)
                ·
                  refine ⟨251568321882358319230199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2683395433411822071788789 251568321882358319230199)
                  ·
                    rfl

theorem cell22_2204674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2204674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204674 prefixEnd_2204674 := by exact prefixLift 2204674
  have htrace : WordTrace (prefixWord ++ tailWord_2204674) baseStart_2204674 baseEnd_2204674 := by
    simpa [prefixWord, tailWord_2204674, baseEnd_2204674] using wordTrace_append hprefix tailTrace_2204674
  have hstable : (prefixWord ++ tailWord_2204674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204674).length < 2 ^ (prefixWord ++ tailWord_2204674).sum := by decide
  have hdescent : baseEnd_2204674 < baseStart_2204674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204683 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 2, 3]
def baseStart_2204683 : Nat := 118140960795 + 2204683 * 2 ^ 59
def prefixEnd_2204683 : Nat := 4983230072969 + 3 ^ 40 * 2204683 * 2
def baseEnd_2204683 : Nat := 754708046531001934215569

theorem tailTrace_2204683 : CollatzResearch.WordTrace tailWord_2204683 prefixEnd_2204683 754708046531001934215569 := by
  unfold tailWord_2204683
  simp only [CollatzResearch.WordTrace]
  refine ⟨80411395071817495724434703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53607596714544997149623135 80411395071817495724434703)
  ·
    refine ⟨120617092607726243586652055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80411395071817495724434703 120617092607726243586652055)
    ·
      refine ⟨180925638911589365379978083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120617092607726243586652055 180925638911589365379978083)
      ·
        refine ⟨271388458367384048069967125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180925638911589365379978083 271388458367384048069967125)
        ·
          refine ⟨12721333985971127253279709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 271388458367384048069967125 12721333985971127253279709)
          ·
            refine ⟨4770500244739172719979891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12721333985971127253279709 4770500244739172719979891)
            ·
              refine ⟨7155750367108759079969837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770500244739172719979891 7155750367108759079969837)
              ·
                refine ⟨2683406387665784654988689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7155750367108759079969837 2683406387665784654988689)
                ·
                  refine ⟨2012554790749338491241517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2683406387665784654988689 2012554790749338491241517)
                  ·
                    refine ⟨754708046531001934215569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2012554790749338491241517 754708046531001934215569)
                    ·
                      rfl

theorem cell22_2204683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 3].length) (baseStart_2204683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204683 prefixEnd_2204683 := by exact prefixLift 2204683
  have htrace : WordTrace (prefixWord ++ tailWord_2204683) baseStart_2204683 baseEnd_2204683 := by
    simpa [prefixWord, tailWord_2204683, baseEnd_2204683] using wordTrace_append hprefix tailTrace_2204683
  have hstable : (prefixWord ++ tailWord_2204683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204683).length < 2 ^ (prefixWord ++ tailWord_2204683).sum := by decide
  have hdescent : baseEnd_2204683 < baseStart_2204683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204741 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 5]
def baseStart_2204741 : Nat := 118140960795 + 2204741 * 2 ^ 59
def prefixEnd_2204741 : Nat := 4983230072969 + 3 ^ 40 * 2204741 * 2
def baseEnd_2204741 : Nat := 251575967038769705421797

theorem tailTrace_2204741 : CollatzResearch.WordTrace tailWord_2204741 prefixEnd_2204741 251575967038769705421797 := by
  unfold tailWord_2204741
  simp only [CollatzResearch.WordTrace]
  refine ⟨80413510505607371630046077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53609007003738247753364051 80413510505607371630046077)
  ·
    refine ⟨30155066439602764361267279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80413510505607371630046077 30155066439602764361267279)
    ·
      refine ⟨45232599659404146541900919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30155066439602764361267279 45232599659404146541900919)
      ·
        refine ⟨67848899489106219812851379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45232599659404146541900919 67848899489106219812851379)
        ·
          refine ⟨101773349233659329719277069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67848899489106219812851379 101773349233659329719277069)
          ·
            refine ⟨38165005962622248644728901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101773349233659329719277069 38165005962622248644728901)
            ·
              refine ⟨7155938617991671620886669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38165005962622248644728901 7155938617991671620886669)
              ·
                refine ⟨2683476981746876857832501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7155938617991671620886669 2683476981746876857832501)
                ·
                  refine ⟨251575967038769705421797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2683476981746876857832501 251575967038769705421797)
                  ·
                    rfl

theorem cell22_2204741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_2204741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204741 prefixEnd_2204741 := by exact prefixLift 2204741
  have htrace : WordTrace (prefixWord ++ tailWord_2204741) baseStart_2204741 baseEnd_2204741 := by
    simpa [prefixWord, tailWord_2204741, baseEnd_2204741] using wordTrace_append hprefix tailTrace_2204741
  have hstable : (prefixWord ++ tailWord_2204741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204741).length < 2 ^ (prefixWord ++ tailWord_2204741).sum := by decide
  have hdescent : baseEnd_2204741 < baseStart_2204741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204805 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_2204805 : Nat := 118140960795 + 2204805 * 2 ^ 59
def prefixEnd_2204805 : Nat := 4983230072969 + 3 ^ 40 * 2204805 * 2
def baseEnd_2204805 : Nat := 754749809624234282665195

theorem tailTrace_2204805 : CollatzResearch.WordTrace tailWord_2204805 prefixEnd_2204805 754749809624234282665195 := by
  unfold tailWord_2204805
  simp only [CollatzResearch.WordTrace]
  refine ⟨80415844777375510560375869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53610563184917007040250579 80415844777375510560375869)
  ·
    refine ⟨30155941791515816460140951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80415844777375510560375869 30155941791515816460140951)
    ·
      refine ⟨45233912687273724690211427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30155941791515816460140951 45233912687273724690211427)
      ·
        refine ⟨67850869030910587035317141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45233912687273724690211427 67850869030910587035317141)
        ·
          refine ⟨3180509485823933767280491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67850869030910587035317141 3180509485823933767280491)
          ·
            refine ⟨4770764228735900650920737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180509485823933767280491 4770764228735900650920737)
            ·
              refine ⟨3578073171551925488190553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4770764228735900650920737 3578073171551925488190553)
              ·
                refine ⟨2683554878663944116142915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3578073171551925488190553 2683554878663944116142915)
                ·
                  refine ⟨4025332317995916174214373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683554878663944116142915 4025332317995916174214373)
                  ·
                    refine ⟨754749809624234282665195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025332317995916174214373 754749809624234282665195)
                    ·
                      rfl

theorem cell22_2204805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_2204805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204805 prefixEnd_2204805 := by exact prefixLift 2204805
  have htrace : WordTrace (prefixWord ++ tailWord_2204805) baseStart_2204805 baseEnd_2204805 := by
    simpa [prefixWord, tailWord_2204805, baseEnd_2204805] using wordTrace_append hprefix tailTrace_2204805
  have hstable : (prefixWord ++ tailWord_2204805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204805).length < 2 ^ (prefixWord ++ tailWord_2204805).sum := by decide
  have hdescent : baseEnd_2204805 < baseStart_2204805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204833 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2204833 : Nat := 118140960795 + 2204833 * 2 ^ 59
def prefixEnd_2204833 : Nat := 4983230072969 + 3 ^ 40 * 2204833 * 2
def baseEnd_2204833 : Nat := 754759394596451542965109

theorem tailTrace_2204833 : CollatzResearch.WordTrace tailWord_2204833 prefixEnd_2204833 754759394596451542965109 := by
  unfold tailWord_2204833
  simp only [CollatzResearch.WordTrace]
  refine ⟨80416866021274071342395153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53611244014182714228263435 80416866021274071342395153)
  ·
    refine ⟨60312649515955553506796365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80416866021274071342395153 60312649515955553506796365)
    ·
      refine ⟨22617243568483332565048637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60312649515955553506796365 22617243568483332565048637)
      ·
        refine ⟨8481466338181249711893239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22617243568483332565048637 8481466338181249711893239)
        ·
          refine ⟨12722199507271874567839859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8481466338181249711893239 12722199507271874567839859)
          ·
            refine ⟨19083299260907811851759789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12722199507271874567839859 19083299260907811851759789)
            ·
              refine ⟨7156237222840429444409921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19083299260907811851759789 7156237222840429444409921)
              ·
                refine ⟨5367177917130322083307441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7156237222840429444409921 5367177917130322083307441)
                ·
                  refine ⟨4025383437847741562480581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5367177917130322083307441 4025383437847741562480581)
                  ·
                    refine ⟨754759394596451542965109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025383437847741562480581 754759394596451542965109)
                    ·
                      rfl

theorem cell22_2204833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2204833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204833 prefixEnd_2204833 := by exact prefixLift 2204833
  have htrace : WordTrace (prefixWord ++ tailWord_2204833) baseStart_2204833 baseEnd_2204833 := by
    simpa [prefixWord, tailWord_2204833, baseEnd_2204833] using wordTrace_append hprefix tailTrace_2204833
  have hstable : (prefixWord ++ tailWord_2204833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204833).length < 2 ^ (prefixWord ++ tailWord_2204833).sum := by decide
  have hdescent : baseEnd_2204833 < baseStart_2204833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204863 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 3, 3]
def baseStart_2204863 : Nat := 118140960795 + 2204863 * 2 ^ 59
def prefixEnd_2204863 : Nat := 4983230072969 + 3 ^ 40 * 2204863 * 2
def baseEnd_2204863 : Nat := 754769664209541464715017

theorem tailTrace_2204863 : CollatzResearch.WordTrace tailWord_2204863 prefixEnd_2204863 754769664209541464715017 := by
  unfold tailWord_2204863
  simp only [CollatzResearch.WordTrace]
  refine ⟨80417960211165386465987243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53611973474110257643991495 80417960211165386465987243)
  ·
    refine ⟨120626940316748079698980865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80417960211165386465987243 120626940316748079698980865)
    ·
      refine ⟨90470205237561059774235649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120626940316748079698980865 90470205237561059774235649)
      ·
        refine ⟨67852653928170794830676737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90470205237561059774235649 67852653928170794830676737)
        ·
          refine ⟨50889490446128096123007553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67852653928170794830676737 50889490446128096123007553)
          ·
            refine ⟨38167117834596072092255665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50889490446128096123007553 38167117834596072092255665)
            ·
              refine ⟨28625338375947054069191749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38167117834596072092255665 28625338375947054069191749)
              ·
                refine ⟨5367250945490072637973453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28625338375947054069191749 5367250945490072637973453)
                ·
                  refine ⟨2012719104558777239240045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5367250945490072637973453 2012719104558777239240045)
                  ·
                    refine ⟨754769664209541464715017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2012719104558777239240045 754769664209541464715017)
                    ·
                      rfl

theorem cell22_2204863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_2204863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204863 prefixEnd_2204863 := by exact prefixLift 2204863
  have htrace : WordTrace (prefixWord ++ tailWord_2204863) baseStart_2204863 baseEnd_2204863 := by
    simpa [prefixWord, tailWord_2204863, baseEnd_2204863] using wordTrace_append hprefix tailTrace_2204863
  have hstable : (prefixWord ++ tailWord_2204863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204863).length < 2 ^ (prefixWord ++ tailWord_2204863).sum := by decide
  have hdescent : baseEnd_2204863 < baseStart_2204863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204897 : List Nat := [1, 2, 3, 1, 3, 3, 1, 4, 1, 3]
def baseStart_2204897 : Nat := 118140960795 + 2204897 * 2 ^ 59
def prefixEnd_2204897 : Nat := 4983230072969 + 3 ^ 40 * 2204897 * 2
def baseEnd_2204897 : Nat := 754781303104376709364913

theorem tailTrace_2204897 : CollatzResearch.WordTrace tailWord_2204897 prefixEnd_2204897 754781303104376709364913 := by
  unfold tailWord_2204897
  simp only [CollatzResearch.WordTrace]
  refine ⟨80419200293042210272724945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53612800195361473515149963 80419200293042210272724945)
  ·
    refine ⟨60314400219781657704543709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80419200293042210272724945 60314400219781657704543709)
    ·
      refine ⟨22617900082418121639203891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60314400219781657704543709 22617900082418121639203891)
      ·
        refine ⟨33926850123627182458805837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22617900082418121639203891 33926850123627182458805837)
        ·
          refine ⟨12722568796360193422052189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33926850123627182458805837 12722568796360193422052189)
          ·
            refine ⟨4770963298635072533269571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12722568796360193422052189 4770963298635072533269571)
            ·
              refine ⟨7156444947952608799904357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770963298635072533269571 7156444947952608799904357)
              ·
                refine ⟨1341833427741114149982067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7156444947952608799904357 1341833427741114149982067)
                ·
                  refine ⟨2012750141611671224973101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341833427741114149982067 2012750141611671224973101)
                  ·
                    refine ⟨754781303104376709364913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2012750141611671224973101 754781303104376709364913)
                    ·
                      rfl

theorem cell22_2204897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_2204897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204897 prefixEnd_2204897 := by exact prefixLift 2204897
  have htrace : WordTrace (prefixWord ++ tailWord_2204897) baseStart_2204897 baseEnd_2204897 := by
    simpa [prefixWord, tailWord_2204897, baseEnd_2204897] using wordTrace_append hprefix tailTrace_2204897
  have hstable : (prefixWord ++ tailWord_2204897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204897).length < 2 ^ (prefixWord ++ tailWord_2204897).sum := by decide
  have hdescent : baseEnd_2204897 < baseStart_2204897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204908 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_2204908 : Nat := 118140960795 + 2204908 * 2 ^ 59
def prefixEnd_2204908 : Nat := 4983230072969 + 3 ^ 40 * 2204908 * 2
def baseEnd_2204908 : Nat := 754785068629176347339879

theorem tailTrace_2204908 : CollatzResearch.WordTrace tailWord_2204908 prefixEnd_2204908 754785068629176347339879 := by
  unfold tailWord_2204908
  simp only [CollatzResearch.WordTrace]
  refine ⟨40209800748001179575687689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53613067664001572767583585 40209800748001179575687689)
  ·
    refine ⟨30157350561000884681765767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40209800748001179575687689 30157350561000884681765767)
    ·
      refine ⟨45236025841501327022648651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30157350561000884681765767 45236025841501327022648651)
      ·
        refine ⟨67854038762251990533972977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45236025841501327022648651 67854038762251990533972977)
        ·
          refine ⟨50890529071688992900479733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67854038762251990533972977 50890529071688992900479733)
          ·
            refine ⟨4770987100470843084419975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50890529071688992900479733 4770987100470843084419975)
            ·
              refine ⟨7156480650706264626629963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770987100470843084419975 7156480650706264626629963)
              ·
                refine ⟨10734720976059396939944945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7156480650706264626629963 10734720976059396939944945)
                ·
                  refine ⟨8051040732044547704958709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10734720976059396939944945 8051040732044547704958709)
                  ·
                    refine ⟨754785068629176347339879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8051040732044547704958709 754785068629176347339879)
                    ·
                      rfl

theorem cell22_2204908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_2204908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204908 prefixEnd_2204908 := by exact prefixLift 2204908
  have htrace : WordTrace (prefixWord ++ tailWord_2204908) baseStart_2204908 baseEnd_2204908 := by
    simpa [prefixWord, tailWord_2204908, baseEnd_2204908] using wordTrace_append hprefix tailTrace_2204908
  have hstable : (prefixWord ++ tailWord_2204908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204908).length < 2 ^ (prefixWord ++ tailWord_2204908).sum := by decide
  have hdescent : baseEnd_2204908 < baseStart_2204908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204940 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_2204940 : Nat := 118140960795 + 2204940 * 2 ^ 59
def prefixEnd_2204940 : Nat := 4983230072969 + 3 ^ 40 * 2204940 * 2
def baseEnd_2204940 : Nat := 754796022883138930539781

theorem tailTrace_2204940 : CollatzResearch.WordTrace tailWord_2204940 prefixEnd_2204940 754796022883138930539781 := by
  unfold tailWord_2204940
  simp only [CollatzResearch.WordTrace]
  refine ⟨40210384315943214308270137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53613845754590952411026849 40210384315943214308270137)
  ·
    refine ⟨30157788236957410731202603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40210384315943214308270137 30157788236957410731202603)
    ·
      refine ⟨45236682355436116096803905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30157788236957410731202603 45236682355436116096803905)
      ·
        refine ⟨33927511766577087072602929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45236682355436116096803905 33927511766577087072602929)
        ·
          refine ⟨25445633824932815304452197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33927511766577087072602929 25445633824932815304452197)
          ·
            refine ⟨4771056342174902869584787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25445633824932815304452197 4771056342174902869584787)
            ·
              refine ⟨7156584513262354304377181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4771056342174902869584787 7156584513262354304377181)
              ·
                refine ⟨2683719192473382864141443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7156584513262354304377181 2683719192473382864141443)
                ·
                  refine ⟨4025578788710074296212165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683719192473382864141443 4025578788710074296212165)
                  ·
                    refine ⟨754796022883138930539781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025578788710074296212165 754796022883138930539781)
                    ·
                      rfl

theorem cell22_2204940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_2204940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2204940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2204940 prefixEnd_2204940 := by exact prefixLift 2204940
  have htrace : WordTrace (prefixWord ++ tailWord_2204940) baseStart_2204940 baseEnd_2204940 := by
    simpa [prefixWord, tailWord_2204940, baseEnd_2204940] using wordTrace_append hprefix tailTrace_2204940
  have hstable : (prefixWord ++ tailWord_2204940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204940).length < 2 ^ (prefixWord ++ tailWord_2204940).sum := by decide
  have hdescent : baseEnd_2204940 < baseStart_2204940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205090 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_2205090 : Nat := 118140960795 + 2205090 * 2 ^ 59
def prefixEnd_2205090 : Nat := 4983230072969 + 3 ^ 40 * 2205090 * 2
def baseEnd_2205090 : Nat := 251615790316196179763107

theorem tailTrace_2205090 : CollatzResearch.WordTrace tailWord_2205090 prefixEnd_2205090 251615790316196179763107 := by
  unfold tailWord_2205090
  simp only [CollatzResearch.WordTrace]
  refine ⟨20106559895335751058625181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53617493054228669489667149 20106559895335751058625181)
  ·
    refine ⟨7539959960750906646984443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20106559895335751058625181 7539959960750906646984443)
    ·
      refine ⟨11309939941126359970476665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7539959960750906646984443 11309939941126359970476665)
      ·
        refine ⟨8482454955844769977857499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11309939941126359970476665 8482454955844769977857499)
        ·
          refine ⟨12723682433767154966786249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8482454955844769977857499 12723682433767154966786249)
          ·
            refine ⟨9542761825325366225089687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12723682433767154966786249 9542761825325366225089687)
            ·
              refine ⟨14314142737988049337634531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9542761825325366225089687 14314142737988049337634531)
              ·
                refine ⟨21471214106982074006451797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14314142737988049337634531 21471214106982074006451797)
                ·
                  refine ⟨251615790316196179763107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21471214106982074006451797 251615790316196179763107)
                  ·
                    rfl

theorem cell22_2205090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_2205090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205090 prefixEnd_2205090 := by exact prefixLift 2205090
  have htrace : WordTrace (prefixWord ++ tailWord_2205090) baseStart_2205090 baseEnd_2205090 := by
    simpa [prefixWord, tailWord_2205090, baseEnd_2205090] using wordTrace_append hprefix tailTrace_2205090
  have hstable : (prefixWord ++ tailWord_2205090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205090).length < 2 ^ (prefixWord ++ tailWord_2205090).sum := by decide
  have hdescent : baseEnd_2205090 < baseStart_2205090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205105 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_2205105 : Nat := 118140960795 + 2205105 * 2 ^ 59
def prefixEnd_2205105 : Nat := 4983230072969 + 3 ^ 40 * 2205105 * 2
def baseEnd_2205105 : Nat := 754852505755133500164275

theorem tailTrace_2205105 : CollatzResearch.WordTrace tailWord_2205105 prefixEnd_2205105 754852505755133500164275 := by
  unfold tailWord_2205105
  simp only [CollatzResearch.WordTrace]
  refine ⟨80426786676288661796296769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53617857784192441197531179 80426786676288661796296769)
  ·
    refine ⟨60320090007216496347222577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80426786676288661796296769 60320090007216496347222577)
    ·
      refine ⟨45240067505412372260416933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60320090007216496347222577 45240067505412372260416933)
      ·
        refine ⟨8482512657264819798828175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45240067505412372260416933 8482512657264819798828175)
        ·
          refine ⟨12723768985897229698242263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8482512657264819798828175 12723768985897229698242263)
          ·
            refine ⟨19085653478845844547363395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12723768985897229698242263 19085653478845844547363395)
            ·
              refine ⟨28628480218268766821045093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19085653478845844547363395 28628480218268766821045093)
              ·
                refine ⟨5367840040925393778945955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28628480218268766821045093 5367840040925393778945955)
                ·
                  refine ⟨8051760061388090668418933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5367840040925393778945955 8051760061388090668418933)
                  ·
                    refine ⟨754852505755133500164275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8051760061388090668418933 754852505755133500164275)
                    ·
                      rfl

theorem cell22_2205105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_2205105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205105 prefixEnd_2205105 := by exact prefixLift 2205105
  have htrace : WordTrace (prefixWord ++ tailWord_2205105) baseStart_2205105 baseEnd_2205105 := by
    simpa [prefixWord, tailWord_2205105, baseEnd_2205105] using wordTrace_append hprefix tailTrace_2205105
  have hstable : (prefixWord ++ tailWord_2205105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205105).length < 2 ^ (prefixWord ++ tailWord_2205105).sum := by decide
  have hdescent : baseEnd_2205105 < baseStart_2205105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205109 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2205109 : Nat := 118140960795 + 2205109 * 2 ^ 59
def prefixEnd_2205109 : Nat := 4983230072969 + 3 ^ 40 * 2205109 * 2
def baseEnd_2205109 : Nat := 754853875036878823064263

theorem tailTrace_2205109 : CollatzResearch.WordTrace tailWord_2205109 prefixEnd_2205109 754853875036878823064263 := by
  unfold tailWord_2205109
  simp only [CollatzResearch.WordTrace]
  refine ⟨80426932568274170479442381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53617955045516113652961587 80426932568274170479442381)
  ·
    refine ⟨30160099713102813929790893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80426932568274170479442381 30160099713102813929790893)
    ·
      refine ⟨11310037392413555223671585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30160099713102813929790893 11310037392413555223671585)
      ·
        refine ⟨8482528044310166417753689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11310037392413555223671585 8482528044310166417753689)
        ·
          refine ⟨6361896033232624813315267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8482528044310166417753689 6361896033232624813315267)
          ·
            refine ⟨9542844049848937219972901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6361896033232624813315267 9542844049848937219972901)
            ·
              refine ⟨1789283259346675728744919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9542844049848937219972901 1789283259346675728744919)
              ·
                refine ⟨2683924889020013593117379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789283259346675728744919 2683924889020013593117379)
                ·
                  refine ⟨4025887333530020389676069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683924889020013593117379 4025887333530020389676069)
                  ·
                    refine ⟨754853875036878823064263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025887333530020389676069 754853875036878823064263)
                    ·
                      rfl

theorem cell22_2205109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2205109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205109 prefixEnd_2205109 := by exact prefixLift 2205109
  have htrace : WordTrace (prefixWord ++ tailWord_2205109) baseStart_2205109 baseEnd_2205109 := by
    simpa [prefixWord, tailWord_2205109, baseEnd_2205109] using wordTrace_append hprefix tailTrace_2205109
  have hstable : (prefixWord ++ tailWord_2205109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205109).length < 2 ^ (prefixWord ++ tailWord_2205109).sum := by decide
  have hdescent : baseEnd_2205109 < baseStart_2205109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205120 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_2205120 : Nat := 118140960795 + 2205120 * 2 ^ 59
def prefixEnd_2205120 : Nat := 4983230072969 + 3 ^ 40 * 2205120 * 2
def baseEnd_2205120 : Nat := 754857640561678461039229

theorem tailTrace_2205120 : CollatzResearch.WordTrace tailWord_2205120 prefixEnd_2205120 754857640561678461039229 := by
  unfold tailWord_2205120
  simp only [CollatzResearch.WordTrace]
  refine ⟨40213666885617159679046407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53618222514156212905395209 40213666885617159679046407)
  ·
    refine ⟨60320500328425739518569611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40213666885617159679046407 60320500328425739518569611)
    ·
      refine ⟨90480750492638609277854417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60320500328425739518569611 90480750492638609277854417)
      ·
        refine ⟨67860562869478956958390813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90480750492638609277854417 67860562869478956958390813)
        ·
          refine ⟨25447711076054608859396555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67860562869478956958390813 25447711076054608859396555)
          ·
            refine ⟨38171566614081913289094833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25447711076054608859396555 38171566614081913289094833)
            ·
              refine ⟨28628674960561434966821125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38171566614081913289094833 28628674960561434966821125)
              ·
                refine ⟨5367876555105269056278961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28628674960561434966821125 5367876555105269056278961)
                ·
                  refine ⟨4025907416328951792209221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5367876555105269056278961 4025907416328951792209221)
                  ·
                    refine ⟨754857640561678461039229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4025907416328951792209221 754857640561678461039229)
                    ·
                      rfl

theorem cell22_2205120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_2205120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205120 prefixEnd_2205120 := by exact prefixLift 2205120
  have htrace : WordTrace (prefixWord ++ tailWord_2205120) baseStart_2205120 baseEnd_2205120 := by
    simpa [prefixWord, tailWord_2205120, baseEnd_2205120] using wordTrace_append hprefix tailTrace_2205120
  have hstable : (prefixWord ++ tailWord_2205120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205120).length < 2 ^ (prefixWord ++ tailWord_2205120).sum := by decide
  have hdescent : baseEnd_2205120 < baseStart_2205120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205124 : List Nat := [2, 3, 3, 2, 1, 1, 2, 4, 4]
def baseStart_2205124 : Nat := 118140960795 + 2205124 * 2 ^ 59
def prefixEnd_2205124 : Nat := 4983230072969 + 3 ^ 40 * 2205124 * 2
def baseEnd_2205124 : Nat := 251619669947807927979739

theorem tailTrace_2205124 : CollatzResearch.WordTrace tailWord_2205124 prefixEnd_2205124 251619669947807927979739 := by
  unfold tailWord_2205124
  simp only [CollatzResearch.WordTrace]
  refine ⟨40213739831609914020619213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53618319775479885360825617 40213739831609914020619213)
  ·
    refine ⟨15080152436853717757732205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40213739831609914020619213 15080152436853717757732205)
    ·
      refine ⟨5655057163820144159149577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15080152436853717757732205 5655057163820144159149577)
      ·
        refine ⟨4241292872865108119362183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5655057163820144159149577 4241292872865108119362183)
        ·
          refine ⟨6361939309297662179043275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4241292872865108119362183 6361939309297662179043275)
          ·
            refine ⟨9542908963946493268564913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6361939309297662179043275 9542908963946493268564913)
            ·
              refine ⟨7157181722959869951423685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9542908963946493268564913 7157181722959869951423685)
              ·
                refine ⟨1341971573054975615891941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7157181722959869951423685 1341971573054975615891941)
                ·
                  refine ⟨251619669947807927979739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341971573054975615891941 251619669947807927979739)
                  ·
                    rfl

theorem cell22_2205124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_2205124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205124 prefixEnd_2205124 := by exact prefixLift 2205124
  have htrace : WordTrace (prefixWord ++ tailWord_2205124) baseStart_2205124 baseEnd_2205124 := by
    simpa [prefixWord, tailWord_2205124, baseEnd_2205124] using wordTrace_append hprefix tailTrace_2205124
  have hstable : (prefixWord ++ tailWord_2205124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205124).length < 2 ^ (prefixWord ++ tailWord_2205124).sum := by decide
  have hdescent : baseEnd_2205124 < baseStart_2205124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205180 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 7]
def baseStart_2205180 : Nat := 118140960795 + 2205180 * 2 ^ 59
def prefixEnd_2205180 : Nat := 4983230072969 + 3 ^ 40 * 2205180 * 2
def baseEnd_2205180 : Nat := 251626059929286101513015

theorem tailTrace_2205180 : CollatzResearch.WordTrace tailWord_2205180 prefixEnd_2205180 251626059929286101513015 := by
  unfold tailWord_2205180
  simp only [CollatzResearch.WordTrace]
  refine ⟨40214761075508474802638497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53619681434011299736851329 40214761075508474802638497)
  ·
    refine ⟨30161070806631356101978873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40214761075508474802638497 30161070806631356101978873)
    ·
      refine ⟨22620803104973517076484155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30161070806631356101978873 22620803104973517076484155)
      ·
        refine ⟨33931204657460275614726233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22620803104973517076484155 33931204657460275614726233)
        ·
          refine ⟨25448403493095206711044675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33931204657460275614726233 25448403493095206711044675)
          ·
            refine ⟨38172605239642810066567013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25448403493095206711044675 38172605239642810066567013)
            ·
              refine ⟨7157363482433026887481315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38172605239642810066567013 7157363482433026887481315)
              ·
                refine ⟨10736045223649540331221973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7157363482433026887481315 10736045223649540331221973)
                ·
                  refine ⟨251626059929286101513015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10736045223649540331221973 251626059929286101513015)
                  ·
                    rfl

theorem cell22_2205180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_2205180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205180 prefixEnd_2205180 := by exact prefixLift 2205180
  have htrace : WordTrace (prefixWord ++ tailWord_2205180) baseStart_2205180 baseEnd_2205180 := by
    simpa [prefixWord, tailWord_2205180, baseEnd_2205180] using wordTrace_append hprefix tailTrace_2205180
  have hstable : (prefixWord ++ tailWord_2205180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205180).length < 2 ^ (prefixWord ++ tailWord_2205180).sum := by decide
  have hdescent : baseEnd_2205180 < baseStart_2205180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205190 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2205190 : Nat := 118140960795 + 2205190 * 2 ^ 59
def prefixEnd_2205190 : Nat := 4983230072969 + 3 ^ 40 * 2205190 * 2
def baseEnd_2205190 : Nat := 754881602992221611789015

theorem tailTrace_2205190 : CollatzResearch.WordTrace tailWord_2205190 prefixEnd_2205190 754881602992221611789015 := by
  unfold tailWord_2205190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2513433965030647541035657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53619924587320480875427349 2513433965030647541035657)
  ·
    refine ⟨1885075473772985655776743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2513433965030647541035657 1885075473772985655776743)
    ·
      refine ⟨2827613210659478483665115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885075473772985655776743 2827613210659478483665115)
      ·
        refine ⟨4241419815989217725497673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827613210659478483665115 4241419815989217725497673)
        ·
          refine ⟨3181064861991913294123255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4241419815989217725497673 3181064861991913294123255)
          ·
            refine ⟨4771597292987869941184883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181064861991913294123255 4771597292987869941184883)
            ·
              refine ⟨7157395939481804911777325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4771597292987869941184883 7157395939481804911777325)
              ·
                refine ⟨2684023477305676841916497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7157395939481804911777325 2684023477305676841916497)
                ·
                  refine ⟨2013017607979257631437373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2684023477305676841916497 2013017607979257631437373)
                  ·
                    refine ⟨754881602992221611789015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013017607979257631437373 754881602992221611789015)
                    ·
                      rfl

theorem cell22_2205190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2205190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205190 prefixEnd_2205190 := by exact prefixLift 2205190
  have htrace : WordTrace (prefixWord ++ tailWord_2205190) baseStart_2205190 baseEnd_2205190 := by
    simpa [prefixWord, tailWord_2205190, baseEnd_2205190] using wordTrace_append hprefix tailTrace_2205190
  have hstable : (prefixWord ++ tailWord_2205190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205190).length < 2 ^ (prefixWord ++ tailWord_2205190).sum := by decide
  have hdescent : baseEnd_2205190 < baseStart_2205190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205276 : List Nat := [2, 2, 4, 1, 2, 2, 2, 3, 4]
def baseStart_2205276 : Nat := 118140960795 + 2205276 * 2 ^ 59
def prefixEnd_2205276 : Nat := 4983230072969 + 3 ^ 40 * 2205276 * 2
def baseEnd_2205276 : Nat := 251637014183248684712917

theorem tailTrace_2205276 : CollatzResearch.WordTrace tailWord_2205276 prefixEnd_2205276 251637014183248684712917 := by
  unfold tailWord_2205276
  simp only [CollatzResearch.WordTrace]
  refine ⟨40216511779334579000385841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53622015705779438667181121 40216511779334579000385841)
  ·
    refine ⟨30162383834500934250289381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40216511779334579000385841 30162383834500934250289381)
    ·
      refine ⟨5655446968968925171929259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30162383834500934250289381 5655446968968925171929259)
      ·
        refine ⟨8483170453453387757893889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5655446968968925171929259 8483170453453387757893889)
        ·
          refine ⟨6362377840090040818420417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8483170453453387757893889 6362377840090040818420417)
          ·
            refine ⟨4771783380067530613815313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6362377840090040818420417 4771783380067530613815313)
            ·
              refine ⟨3578837535050647960361485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4771783380067530613815313 3578837535050647960361485)
              ·
                refine ⟨1342064075643992985135557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3578837535050647960361485 1342064075643992985135557)
                ·
                  refine ⟨251637014183248684712917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342064075643992985135557 251637014183248684712917)
                  ·
                    rfl

theorem cell22_2205276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_2205276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205276 prefixEnd_2205276 := by exact prefixLift 2205276
  have htrace : WordTrace (prefixWord ++ tailWord_2205276) baseStart_2205276 baseEnd_2205276 := by
    simpa [prefixWord, tailWord_2205276, baseEnd_2205276] using wordTrace_append hprefix tailTrace_2205276
  have hstable : (prefixWord ++ tailWord_2205276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205276).length < 2 ^ (prefixWord ++ tailWord_2205276).sum := by decide
  have hdescent : baseEnd_2205276 < baseStart_2205276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205319 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2205319 : Nat := 118140960795 + 2205319 * 2 ^ 59
def prefixEnd_2205319 : Nat := 4983230072969 + 3 ^ 40 * 2205319 * 2
def baseEnd_2205319 : Nat := 754925762328508275313619

theorem tailTrace_2205319 : CollatzResearch.WordTrace tailWord_2205319 prefixEnd_2205319 754925762328508275313619 := by
  unfold tailWord_2205319
  simp only [CollatzResearch.WordTrace]
  refine ⟨80434591897513376344587011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53623061265008917563058007 80434591897513376344587011)
  ·
    refine ⟨120651887846270064516880517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80434591897513376344587011 120651887846270064516880517)
    ·
      refine ⟨22622228971175637096915097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120651887846270064516880517 22622228971175637096915097)
      ·
        refine ⟨16966671728381727822686323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22622228971175637096915097 16966671728381727822686323)
        ·
          refine ⟨25450007592572591734029485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16966671728381727822686323 25450007592572591734029485)
          ·
            refine ⟨9543752847214721900261057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25450007592572591734029485 9543752847214721900261057)
            ·
              refine ⟨7157814635411041425195793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9543752847214721900261057 7157814635411041425195793)
              ·
                refine ⟨5368360976558281068896845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7157814635411041425195793 5368360976558281068896845)
                ·
                  refine ⟨2013135366209355400836317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5368360976558281068896845 2013135366209355400836317)
                  ·
                    refine ⟨754925762328508275313619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013135366209355400836317 754925762328508275313619)
                    ·
                      rfl

theorem cell22_2205319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2205319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205319 prefixEnd_2205319 := by exact prefixLift 2205319
  have htrace : WordTrace (prefixWord ++ tailWord_2205319) baseStart_2205319 baseEnd_2205319 := by
    simpa [prefixWord, tailWord_2205319, baseEnd_2205319] using wordTrace_append hprefix tailTrace_2205319
  have hstable : (prefixWord ++ tailWord_2205319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205319).length < 2 ^ (prefixWord ++ tailWord_2205319).sum := by decide
  have hdescent : baseEnd_2205319 < baseStart_2205319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205404 : List Nat := [2, 2, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2205404 : Nat := 118140960795 + 2205404 * 2 ^ 59
def prefixEnd_2205404 : Nat := 4983230072969 + 3 ^ 40 * 2205404 * 2
def baseEnd_2205404 : Nat := 754954859565596386938359

theorem tailTrace_2205404 : CollatzResearch.WordTrace tailWord_2205404 prefixEnd_2205404 754954859565596386938359 := by
  unfold tailWord_2205404
  simp only [CollatzResearch.WordTrace]
  refine ⟨40218846051102717930715633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53625128068136957240954177 40218846051102717930715633)
  ·
    refine ⟨30164134538327038448036725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40218846051102717930715633 30164134538327038448036725)
    ·
      refine ⟨2827887612968159854503443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30164134538327038448036725 2827887612968159854503443)
      ·
        refine ⟨4241831419452239781755165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827887612968159854503443 4241831419452239781755165)
        ·
          refine ⟨1590686782294589918158187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4241831419452239781755165 1590686782294589918158187)
          ·
            refine ⟨2386030173441884877237281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590686782294589918158187 2386030173441884877237281)
            ·
              refine ⟨1789522630081413657927961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2386030173441884877237281 1789522630081413657927961)
              ·
                refine ⟨1342141972561060243445971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789522630081413657927961 1342141972561060243445971)
                ·
                  refine ⟨2013212958841590365168957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342141972561060243445971 2013212958841590365168957)
                  ·
                    refine ⟨754954859565596386938359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013212958841590365168957 754954859565596386938359)
                    ·
                      rfl

theorem cell22_2205404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2205404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205404 prefixEnd_2205404 := by exact prefixLift 2205404
  have htrace : WordTrace (prefixWord ++ tailWord_2205404) baseStart_2205404 baseEnd_2205404 := by
    simpa [prefixWord, tailWord_2205404, baseEnd_2205404] using wordTrace_append hprefix tailTrace_2205404
  have hstable : (prefixWord ++ tailWord_2205404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205404).length < 2 ^ (prefixWord ++ tailWord_2205404).sum := by decide
  have hdescent : baseEnd_2205404 < baseStart_2205404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205426 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_2205426 : Nat := 118140960795 + 2205426 * 2 ^ 59
def prefixEnd_2205426 : Nat := 4983230072969 + 3 ^ 40 * 2205426 * 2
def baseEnd_2205426 : Nat := 754962390615195662888291

theorem tailTrace_2205426 : CollatzResearch.WordTrace tailWord_2205426 prefixEnd_2205426 754962390615195662888291 := by
  unfold tailWord_2205426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20109623627031433404683033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53625663005417155745821421 20109623627031433404683033)
  ·
    refine ⟨15082217720273575053512275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20109623627031433404683033 15082217720273575053512275)
    ·
      refine ⟨22623326580410362580268413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15082217720273575053512275 22623326580410362580268413)
      ·
        refine ⟨8483747467653885967600655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22623326580410362580268413 8483747467653885967600655)
        ·
          refine ⟨12725621201480828951400983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8483747467653885967600655 12725621201480828951400983)
          ·
            refine ⟨19088431802221243427101475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12725621201480828951400983 19088431802221243427101475)
            ·
              refine ⟨28632647703331865140652213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19088431802221243427101475 28632647703331865140652213)
              ·
                refine ⟨2684310722187362356936145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28632647703331865140652213 2684310722187362356936145)
                ·
                  refine ⟨2013233041640521767702109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2684310722187362356936145 2013233041640521767702109)
                  ·
                    refine ⟨754962390615195662888291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013233041640521767702109 754962390615195662888291)
                    ·
                      rfl

theorem cell22_2205426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_2205426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205426 prefixEnd_2205426 := by exact prefixLift 2205426
  have htrace : WordTrace (prefixWord ++ tailWord_2205426) baseStart_2205426 baseEnd_2205426 := by
    simpa [prefixWord, tailWord_2205426, baseEnd_2205426] using wordTrace_append hprefix tailTrace_2205426
  have hstable : (prefixWord ++ tailWord_2205426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205426).length < 2 ^ (prefixWord ++ tailWord_2205426).sum := by decide
  have hdescent : baseEnd_2205426 < baseStart_2205426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205428 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2205428 : Nat := 118140960795 + 2205428 * 2 ^ 59
def prefixEnd_2205428 : Nat := 4983230072969 + 3 ^ 40 * 2205428 * 2
def baseEnd_2205428 : Nat := 251654358418689441446095

theorem tailTrace_2205428 : CollatzResearch.WordTrace tailWord_2205428 prefixEnd_2205428 251654358418689441446095 := by
  unfold tailWord_2205428
  simp only [CollatzResearch.WordTrace]
  refine ⟨40219283727059243980152469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53625711636078991973536625 40219283727059243980152469)
  ·
    refine ⟨1885278924705902061569647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40219283727059243980152469 1885278924705902061569647)
    ·
      refine ⟨2827918387058853092354471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885278924705902061569647 2827918387058853092354471)
      ·
        refine ⟨4241877580588279638531707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827918387058853092354471 4241877580588279638531707)
        ·
          refine ⟨6362816370882419457797561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4241877580588279638531707 6362816370882419457797561)
          ·
            refine ⟨4772112278161814593348171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6362816370882419457797561 4772112278161814593348171)
            ·
              refine ⟨7158168417242721890022257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4772112278161814593348171 7158168417242721890022257)
              ·
                refine ⟨5368626312932041417516693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7158168417242721890022257 5368626312932041417516693)
                ·
                  refine ⟨251654358418689441446095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5368626312932041417516693 251654358418689441446095)
                  ·
                    rfl

theorem cell22_2205428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2205428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205428 prefixEnd_2205428 := by exact prefixLift 2205428
  have htrace : WordTrace (prefixWord ++ tailWord_2205428) baseStart_2205428 baseEnd_2205428 := by
    simpa [prefixWord, tailWord_2205428, baseEnd_2205428] using wordTrace_append hprefix tailTrace_2205428
  have hstable : (prefixWord ++ tailWord_2205428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205428).length < 2 ^ (prefixWord ++ tailWord_2205428).sum := by decide
  have hdescent : baseEnd_2205428 < baseStart_2205428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205437 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_2205437 : Nat := 118140960795 + 2205437 * 2 ^ 59
def prefixEnd_2205437 : Nat := 4983230072969 + 3 ^ 40 * 2205437 * 2
def baseEnd_2205437 : Nat := 754966156139995300863257

theorem tailTrace_2205437 : CollatzResearch.WordTrace tailWord_2205437 prefixEnd_2205437 754966156139995300863257 := by
  unfold tailWord_2205437
  simp only [CollatzResearch.WordTrace]
  refine ⟨80438895711085882497382565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53625930474057254998255043 80438895711085882497382565)
  ·
    refine ⟨15082292945828602968259231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80438895711085882497382565 15082292945828602968259231)
    ·
      refine ⟨22623439418742904452388847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15082292945828602968259231 22623439418742904452388847)
      ·
        refine ⟨33935159128114356678583271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22623439418742904452388847 33935159128114356678583271)
        ·
          refine ⟨50902738692171535017874907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33935159128114356678583271 50902738692171535017874907)
          ·
            refine ⟨76354108038257302526812361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50902738692171535017874907 76354108038257302526812361)
            ·
              refine ⟨57265581028692976895109271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76354108038257302526812361 57265581028692976895109271)
              ·
                refine ⟨85898371543039465342663907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57265581028692976895109271 85898371543039465342663907)
                ·
                  refine ⟨128847557314559198013995861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85898371543039465342663907 128847557314559198013995861)
                  ·
                    refine ⟨754966156139995300863257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 128847557314559198013995861 754966156139995300863257)
                    ·
                      rfl

theorem cell22_2205437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_2205437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205437 prefixEnd_2205437 := by exact prefixLift 2205437
  have htrace : WordTrace (prefixWord ++ tailWord_2205437) baseStart_2205437 baseEnd_2205437 := by
    simpa [prefixWord, tailWord_2205437, baseEnd_2205437] using wordTrace_append hprefix tailTrace_2205437
  have hstable : (prefixWord ++ tailWord_2205437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205437).length < 2 ^ (prefixWord ++ tailWord_2205437).sum := by decide
  have hdescent : baseEnd_2205437 < baseStart_2205437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205467 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 7]
def baseStart_2205467 : Nat := 118140960795 + 2205467 * 2 ^ 59
def prefixEnd_2205467 : Nat := 4983230072969 + 3 ^ 40 * 2205467 * 2
def baseEnd_2205467 : Nat := 251658808584361740871055

theorem tailTrace_2205467 : CollatzResearch.WordTrace tailWord_2205467 prefixEnd_2205467 251658808584361740871055 := by
  unfold tailWord_2205467
  simp only [CollatzResearch.WordTrace]
  refine ⟨80439989900977197620974655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53626659933984798413983103 80439989900977197620974655)
  ·
    refine ⟨120659984851465796431461983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80439989900977197620974655 120659984851465796431461983)
    ·
      refine ⟨180989977277198694647192975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120659984851465796431461983 180989977277198694647192975)
      ·
        refine ⟨271484965915798041970789463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180989977277198694647192975 271484965915798041970789463)
        ·
          refine ⟨407227448873697062956184195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271484965915798041970789463 407227448873697062956184195)
          ·
            refine ⟨610841173310545594434276293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407227448873697062956184195 610841173310545594434276293)
            ·
              refine ⟨114532719995727298956426805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 610841173310545594434276293 114532719995727298956426805)
              ·
                refine ⟨10737442499599434277165013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114532719995727298956426805 10737442499599434277165013)
                ·
                  refine ⟨251658808584361740871055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10737442499599434277165013 251658808584361740871055)
                  ·
                    rfl

theorem cell22_2205467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 7].length) (baseStart_2205467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205467 prefixEnd_2205467 := by exact prefixLift 2205467
  have htrace : WordTrace (prefixWord ++ tailWord_2205467) baseStart_2205467 baseEnd_2205467 := by
    simpa [prefixWord, tailWord_2205467, baseEnd_2205467] using wordTrace_append hprefix tailTrace_2205467
  have hstable : (prefixWord ++ tailWord_2205467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205467).length < 2 ^ (prefixWord ++ tailWord_2205467).sum := by decide
  have hdescent : baseEnd_2205467 < baseStart_2205467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205471 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 3, 3]
def baseStart_2205471 : Nat := 118140960795 + 2205471 * 2 ^ 59
def prefixEnd_2205471 : Nat := 4983230072969 + 3 ^ 40 * 2205471 * 2
def baseEnd_2205471 : Nat := 754977795034830545513153

theorem tailTrace_2205471 : CollatzResearch.WordTrace tailWord_2205471 prefixEnd_2205471 754977795034830545513153 := by
  unfold tailWord_2205471
  simp only [CollatzResearch.WordTrace]
  refine ⟨80440135792962706304120267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53626757195308470869413511 80440135792962706304120267)
  ·
    refine ⟨120660203689444059456180401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80440135792962706304120267 120660203689444059456180401)
    ·
      refine ⟨90495152767083044592135301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120660203689444059456180401 90495152767083044592135301)
      ·
        refine ⟨16967841143828070861025369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90495152767083044592135301 16967841143828070861025369)
        ·
          refine ⟨12725880857871053145769027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16967841143828070861025369 12725880857871053145769027)
          ·
            refine ⟨19088821286806579718653541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12725880857871053145769027 19088821286806579718653541)
            ·
              refine ⟨3579153991276233697247539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19088821286806579718653541 3579153991276233697247539)
              ·
                refine ⟨5368730986914350545871309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3579153991276233697247539 5368730986914350545871309)
                ·
                  refine ⟨2013274120092881454701741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5368730986914350545871309 2013274120092881454701741)
                  ·
                    refine ⟨754977795034830545513153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013274120092881454701741 754977795034830545513153)
                    ·
                      rfl

theorem cell22_2205471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_2205471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205471 prefixEnd_2205471 := by exact prefixLift 2205471
  have htrace : WordTrace (prefixWord ++ tailWord_2205471) baseStart_2205471 baseEnd_2205471 := by
    simpa [prefixWord, tailWord_2205471, baseEnd_2205471] using wordTrace_append hprefix tailTrace_2205471
  have hstable : (prefixWord ++ tailWord_2205471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205471).length < 2 ^ (prefixWord ++ tailWord_2205471).sum := by decide
  have hdescent : baseEnd_2205471 < baseStart_2205471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205548 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_2205548 : Nat := 118140960795 + 2205548 * 2 ^ 59
def prefixEnd_2205548 : Nat := 4983230072969 + 3 ^ 40 * 2205548 * 2
def baseEnd_2205548 : Nat := 755004153708428011337917

theorem tailTrace_2205548 : CollatzResearch.WordTrace tailWord_2205548 prefixEnd_2205548 755004153708428011337917 := by
  unfold tailWord_2205548
  simp only [CollatzResearch.WordTrace]
  refine ⟨40221472106841874227336649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53628629475789165636448865 40221472106841874227336649)
  ·
    refine ⟨30166104080131405670502487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40221472106841874227336649 30166104080131405670502487)
    ·
      refine ⟨45249156120197108505753731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30166104080131405670502487 45249156120197108505753731)
      ·
        refine ⟨67873734180295662758630597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45249156120197108505753731 67873734180295662758630597)
        ·
          refine ⟨12726325158805436767243237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67873734180295662758630597 12726325158805436767243237)
          ·
            refine ⟨2386185967276019393858107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12726325158805436767243237 2386185967276019393858107)
            ·
              refine ⟨3579278950914029090787161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386185967276019393858107 3579278950914029090787161)
              ·
                refine ⟨2684459213185521818090371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3579278950914029090787161 2684459213185521818090371)
                ·
                  refine ⟨4026688819778282727135557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684459213185521818090371 4026688819778282727135557)
                  ·
                    refine ⟨755004153708428011337917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4026688819778282727135557 755004153708428011337917)
                    ·
                      rfl

theorem cell22_2205548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_2205548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205548 prefixEnd_2205548 := by exact prefixLift 2205548
  have htrace : WordTrace (prefixWord ++ tailWord_2205548) baseStart_2205548 baseEnd_2205548 := by
    simpa [prefixWord, tailWord_2205548, baseEnd_2205548] using wordTrace_append hprefix tailTrace_2205548
  have hstable : (prefixWord ++ tailWord_2205548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205548).length < 2 ^ (prefixWord ++ tailWord_2205548).sum := by decide
  have hdescent : baseEnd_2205548 < baseStart_2205548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205591 : List Nat := [1, 1, 3, 3, 1, 5, 1, 7]
def baseStart_2205591 : Nat := 118140960795 + 2205591 * 2 ^ 59
def prefixEnd_2205591 : Nat := 4983230072969 + 3 ^ 40 * 2205591 * 2
def baseEnd_2205591 : Nat := 83890985943021136945865

theorem tailTrace_2205591 : CollatzResearch.WordTrace tailWord_2205591 prefixEnd_2205591 83890985943021136945865 := by
  unfold tailWord_2205591
  simp only [CollatzResearch.WordTrace]
  refine ⟨80444512552527966798488627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53629675035018644532325751 80444512552527966798488627)
  ·
    refine ⟨120666768828791950197732941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80444512552527966798488627 120666768828791950197732941)
    ·
      refine ⟨45250038310796981324149853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120666768828791950197732941 45250038310796981324149853)
      ·
        refine ⟨16968764366548867996556195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45250038310796981324149853 16968764366548867996556195)
        ·
          refine ⟨25453146549823301994834293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16968764366548867996556195 25453146549823301994834293)
          ·
            refine ⟨2386232489045934562015715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25453146549823301994834293 2386232489045934562015715)
            ·
              refine ⟨3579348733568901843023573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386232489045934562015715 3579348733568901843023573)
              ·
                refine ⟨83890985943021136945865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3579348733568901843023573 83890985943021136945865)
                ·
                  rfl

theorem cell22_2205591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 7].length) (baseStart_2205591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205591 prefixEnd_2205591 := by exact prefixLift 2205591
  have htrace : WordTrace (prefixWord ++ tailWord_2205591) baseStart_2205591 baseEnd_2205591 := by
    simpa [prefixWord, tailWord_2205591, baseEnd_2205591] using wordTrace_append hprefix tailTrace_2205591
  have hstable : (prefixWord ++ tailWord_2205591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205591).length < 2 ^ (prefixWord ++ tailWord_2205591).sum := by decide
  have hdescent : baseEnd_2205591 < baseStart_2205591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205614 : List Nat := [4, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_2205614 : Nat := 118140960795 + 2205614 * 2 ^ 59
def prefixEnd_2205614 : Nat := 4983230072969 + 3 ^ 40 * 2205614 * 2
def baseEnd_2205614 : Nat := 251675582285741946395905

theorem tailTrace_2205614 : CollatzResearch.WordTrace tailWord_2205614 prefixEnd_2205614 251675582285741946395905 := by
  unfold tailWord_2205614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055668928930580215821987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53630234287629761151050597 10055668928930580215821987)
  ·
    refine ⟨15083503393395870323732981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10055668928930580215821987 15083503393395870323732981)
    ·
      refine ⟨1414078443130862842849967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15083503393395870323732981 1414078443130862842849967)
      ·
        refine ⟨2121117664696294264274951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414078443130862842849967 2121117664696294264274951)
        ·
          refine ⟨3181676497044441396412427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121117664696294264274951 3181676497044441396412427)
          ·
            refine ⟨4772514745566662094618641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181676497044441396412427 4772514745566662094618641)
            ·
              refine ⟨3579386059174996570963981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4772514745566662094618641 3579386059174996570963981)
              ·
                refine ⟨1342269772190623714111493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3579386059174996570963981 1342269772190623714111493)
                ·
                  refine ⟨251675582285741946395905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342269772190623714111493 251675582285741946395905)
                  ·
                    rfl

theorem cell22_2205614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_2205614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205614 prefixEnd_2205614 := by exact prefixLift 2205614
  have htrace : WordTrace (prefixWord ++ tailWord_2205614) baseStart_2205614 baseEnd_2205614 := by
    simpa [prefixWord, tailWord_2205614, baseEnd_2205614] using wordTrace_append hprefix tailTrace_2205614
  have hstable : (prefixWord ++ tailWord_2205614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205614).length < 2 ^ (prefixWord ++ tailWord_2205614).sum := by decide
  have hdescent : baseEnd_2205614 < baseStart_2205614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205619 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 7]
def baseStart_2205619 : Nat := 118140960795 + 2205619 * 2 ^ 59
def prefixEnd_2205619 : Nat := 4983230072969 + 3 ^ 40 * 2205619 * 2
def baseEnd_2205619 : Nat := 251676152819802497604233

theorem tailTrace_2205619 : CollatzResearch.WordTrace tailWord_2205619 prefixEnd_2205619 251676152819802497604233 := by
  unfold tailWord_2205619
  simp only [CollatzResearch.WordTrace]
  refine ⟨80445533796426527580507911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53630355864284351720338607 80445533796426527580507911)
  ·
    refine ⟨120668300694639791370761867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80445533796426527580507911 120668300694639791370761867)
    ·
      refine ⟨181002451041959687056142801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120668300694639791370761867 181002451041959687056142801)
      ·
        refine ⟨135751838281469765292107101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181002451041959687056142801 135751838281469765292107101)
        ·
          refine ⟨50906939355551161984540163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135751838281469765292107101 50906939355551161984540163)
          ·
            refine ⟨76360409033326742976810245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50906939355551161984540163 76360409033326742976810245)
            ·
              refine ⟨14317576693748764308151921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76360409033326742976810245 14317576693748764308151921)
              ·
                refine ⟨10738182520311573231113941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14317576693748764308151921 10738182520311573231113941)
                ·
                  refine ⟨251676152819802497604233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10738182520311573231113941 251676152819802497604233)
                  ·
                    rfl

theorem cell22_2205619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 7].length) (baseStart_2205619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205619 prefixEnd_2205619 := by exact prefixLift 2205619
  have htrace : WordTrace (prefixWord ++ tailWord_2205619) baseStart_2205619 baseEnd_2205619 := by
    simpa [prefixWord, tailWord_2205619, baseEnd_2205619] using wordTrace_append hprefix tailTrace_2205619
  have hstable : (prefixWord ++ tailWord_2205619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205619).length < 2 ^ (prefixWord ++ tailWord_2205619).sum := by decide
  have hdescent : baseEnd_2205619 < baseStart_2205619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205640 : List Nat := [2, 1, 3, 1, 4, 1, 2, 4, 1, 3]
def baseStart_2205640 : Nat := 118140960795 + 2205640 * 2 ^ 59
def prefixEnd_2205640 : Nat := 4983230072969 + 3 ^ 40 * 2205640 * 2
def baseEnd_2205640 : Nat := 755035647188570438037635

theorem tailTrace_2205640 : CollatzResearch.WordTrace tailWord_2205640 prefixEnd_2205640 755035647188570438037635 := by
  unfold tailWord_2205640
  simp only [CollatzResearch.WordTrace]
  refine ⟨40223149864675224083511187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53630866486233632111348249 40223149864675224083511187)
  ·
    refine ⟨60334724797012836125266781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40223149864675224083511187 60334724797012836125266781)
    ·
      refine ⟨22625521798879813546975043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60334724797012836125266781 22625521798879813546975043)
      ·
        refine ⟨33938282698319720320462565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22625521798879813546975043 33938282698319720320462565)
        ·
          refine ⟨6363428005934947560086731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33938282698319720320462565 6363428005934947560086731)
          ·
            refine ⟨9545142008902421340130097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6363428005934947560086731 9545142008902421340130097)
            ·
              refine ⟨7158856506676816005097573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9545142008902421340130097 7158856506676816005097573)
              ·
                refine ⟨1342285595001903000955795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7158856506676816005097573 1342285595001903000955795)
                ·
                  refine ⟨2013428392502854501433693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342285595001903000955795 2013428392502854501433693)
                  ·
                    refine ⟨755035647188570438037635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013428392502854501433693 755035647188570438037635)
                    ·
                      rfl

theorem cell22_2205640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_2205640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205640 prefixEnd_2205640 := by exact prefixLift 2205640
  have htrace : WordTrace (prefixWord ++ tailWord_2205640) baseStart_2205640 baseEnd_2205640 := by
    simpa [prefixWord, tailWord_2205640, baseEnd_2205640] using wordTrace_append hprefix tailTrace_2205640
  have hstable : (prefixWord ++ tailWord_2205640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205640).length < 2 ^ (prefixWord ++ tailWord_2205640).sum := by decide
  have hdescent : baseEnd_2205640 < baseStart_2205640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205649 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_2205649 : Nat := 118140960795 + 2205649 * 2 ^ 59
def prefixEnd_2205649 : Nat := 4983230072969 + 3 ^ 40 * 2205649 * 2
def baseEnd_2205649 : Nat := 755038728072497414562607

theorem tailTrace_2205649 : CollatzResearch.WordTrace tailWord_2205649 prefixEnd_2205649 755038728072497414562607 := by
  unfold tailWord_2205649
  simp only [CollatzResearch.WordTrace]
  refine ⟨80446627986317842704100001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53631085324211895136066667 80446627986317842704100001)
  ·
    refine ⟨60334970989738382028075001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80446627986317842704100001 60334970989738382028075001)
    ·
      refine ⟨45251228242303786521056251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60334970989738382028075001 45251228242303786521056251)
      ·
        refine ⟨67876842363455679781584377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45251228242303786521056251 67876842363455679781584377)
        ·
          refine ⟨50907631772591759836188283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67876842363455679781584377 50907631772591759836188283)
          ·
            refine ⟨76361447658887639754282425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50907631772591759836188283 76361447658887639754282425)
            ·
              refine ⟨57271085744165729815711819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76361447658887639754282425 57271085744165729815711819)
              ·
                refine ⟨85906628616248594723567729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57271085744165729815711819 85906628616248594723567729)
                ·
                  refine ⟨64429971462186446042675797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85906628616248594723567729 64429971462186446042675797)
                  ·
                    refine ⟨755038728072497414562607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64429971462186446042675797 755038728072497414562607)
                    ·
                      rfl

theorem cell22_2205649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_2205649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205649 prefixEnd_2205649 := by exact prefixLift 2205649
  have htrace : WordTrace (prefixWord ++ tailWord_2205649) baseStart_2205649 baseEnd_2205649 := by
    simpa [prefixWord, tailWord_2205649, baseEnd_2205649] using wordTrace_append hprefix tailTrace_2205649
  have hstable : (prefixWord ++ tailWord_2205649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205649).length < 2 ^ (prefixWord ++ tailWord_2205649).sum := by decide
  have hdescent : baseEnd_2205649 < baseStart_2205649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205717 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_2205717 : Nat := 118140960795 + 2205717 * 2 ^ 59
def prefixEnd_2205717 : Nat := 4983230072969 + 3 ^ 40 * 2205717 * 2
def baseEnd_2205717 : Nat := 755062005862167903862399

theorem tailTrace_2205717 : CollatzResearch.WordTrace tailWord_2205717 prefixEnd_2205717 755062005862167903862399 := by
  unfold tailWord_2205717
  simp only [CollatzResearch.WordTrace]
  refine ⟨80449108150071490317575405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53632738766714326878383603 80449108150071490317575405)
  ·
    refine ⟨30168415556276808869090777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80449108150071490317575405 30168415556276808869090777)
    ·
      refine ⟨22626311667207606651818083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30168415556276808869090777 22626311667207606651818083)
      ·
        refine ⟨33939467500811409977727125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22626311667207606651818083 33939467500811409977727125)
        ·
          refine ⟨1590912539100534842705959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33939467500811409977727125 1590912539100534842705959)
          ·
            refine ⟨2386368808650802264058939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590912539100534842705959 2386368808650802264058939)
            ·
              refine ⟨3579553212976203396088409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386368808650802264058939 3579553212976203396088409)
              ·
                refine ⟨2684664909732152547066307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3579553212976203396088409 2684664909732152547066307)
                ·
                  refine ⟨4026997364598228820599461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684664909732152547066307 4026997364598228820599461)
                  ·
                    refine ⟨755062005862167903862399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4026997364598228820599461 755062005862167903862399)
                    ·
                      rfl

theorem cell22_2205717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_2205717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205717 prefixEnd_2205717 := by exact prefixLift 2205717
  have htrace : WordTrace (prefixWord ++ tailWord_2205717) baseStart_2205717 baseEnd_2205717 := by
    simpa [prefixWord, tailWord_2205717, baseEnd_2205717] using wordTrace_append hprefix tailTrace_2205717
  have hstable : (prefixWord ++ tailWord_2205717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205717).length < 2 ^ (prefixWord ++ tailWord_2205717).sum := by decide
  have hdescent : baseEnd_2205717 < baseStart_2205717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205756 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_2205756 : Nat := 118140960795 + 2205756 * 2 ^ 59
def prefixEnd_2205756 : Nat := 4983230072969 + 3 ^ 40 * 2205756 * 2
def baseEnd_2205756 : Nat := 755075356359184802137279

theorem tailTrace_2205756 : CollatzResearch.WordTrace tailWord_2205756 prefixEnd_2205756 755075356359184802137279 := by
  unfold tailWord_2205756
  simp only [CollatzResearch.WordTrace]
  refine ⟨40225265298465099989122561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53633687064620133318830081 40225265298465099989122561)
  ·
    refine ⟨30168948973848824991841921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40225265298465099989122561 30168948973848824991841921)
    ·
      refine ⟨22626711730386618743881441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30168948973848824991841921 22626711730386618743881441)
      ·
        refine ⟨16970033797789964057911081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22626711730386618743881441 16970033797789964057911081)
        ·
          refine ⟨12727525348342473043433311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16970033797789964057911081 12727525348342473043433311)
          ·
            refine ⟨19091288022513709565149967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12727525348342473043433311 19091288022513709565149967)
            ·
              refine ⟨28636932033770564347724951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19091288022513709565149967 28636932033770564347724951)
              ·
                refine ⟨42955398050655846521587427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28636932033770564347724951 42955398050655846521587427)
                ·
                  refine ⟨64433097075983769782381141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42955398050655846521587427 64433097075983769782381141)
                  ·
                    refine ⟨755075356359184802137279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64433097075983769782381141 755075356359184802137279)
                    ·
                      rfl

theorem cell22_2205756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_2205756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205756 prefixEnd_2205756 := by exact prefixLift 2205756
  have htrace : WordTrace (prefixWord ++ tailWord_2205756) baseStart_2205756 baseEnd_2205756 := by
    simpa [prefixWord, tailWord_2205756, baseEnd_2205756] using wordTrace_append hprefix tailTrace_2205756
  have hstable : (prefixWord ++ tailWord_2205756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205756).length < 2 ^ (prefixWord ++ tailWord_2205756).sum := by decide
  have hdescent : baseEnd_2205756 < baseStart_2205756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205773 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2205773 : Nat := 118140960795 + 2205773 * 2 ^ 59
def prefixEnd_2205773 : Nat := 4983230072969 + 3 ^ 40 * 2205773 * 2
def baseEnd_2205773 : Nat := 755081175806602424462227

theorem tailTrace_2205773 : CollatzResearch.WordTrace tailWord_2205773 prefixEnd_2205773 755081175806602424462227 := by
  unfold tailWord_2205773
  simp only [CollatzResearch.WordTrace]
  refine ⟨80451150637868611881613973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53634100425245741254409315 80451150637868611881613973)
  ·
    refine ⟨3771147686150091181950655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80451150637868611881613973 3771147686150091181950655)
    ·
      refine ⟨5656721529225136772925983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3771147686150091181950655 5656721529225136772925983)
      ·
        refine ⟨8485082293837705159388975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5656721529225136772925983 8485082293837705159388975)
        ·
          refine ⟨12727623440756557739083463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8485082293837705159388975 12727623440756557739083463)
          ·
            refine ⟨19091435161134836608625195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12727623440756557739083463 19091435161134836608625195)
            ·
              refine ⟨28637152741702254912937793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19091435161134836608625195 28637152741702254912937793)
              ·
                refine ⟨21477864556276691184703345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28637152741702254912937793 21477864556276691184703345)
                ·
                  refine ⟨16108398417207518388527509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21477864556276691184703345 16108398417207518388527509)
                  ·
                    refine ⟨755081175806602424462227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16108398417207518388527509 755081175806602424462227)
                    ·
                      rfl

theorem cell22_2205773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2205773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205773 prefixEnd_2205773 := by exact prefixLift 2205773
  have htrace : WordTrace (prefixWord ++ tailWord_2205773) baseStart_2205773 baseEnd_2205773 := by
    simpa [prefixWord, tailWord_2205773, baseEnd_2205773] using wordTrace_append hprefix tailTrace_2205773
  have hstable : (prefixWord ++ tailWord_2205773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205773).length < 2 ^ (prefixWord ++ tailWord_2205773).sum := by decide
  have hdescent : baseEnd_2205773 < baseStart_2205773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205786 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_2205786 : Nat := 118140960795 + 2205786 * 2 ^ 59
def prefixEnd_2205786 : Nat := 4983230072969 + 3 ^ 40 * 2205786 * 2
def baseEnd_2205786 : Nat := 755085625972274723887187

theorem tailTrace_2205786 : CollatzResearch.WordTrace tailWord_2205786 prefixEnd_2205786 755085625972274723887187 := by
  unfold tailWord_2205786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20112906196705378775459303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53634416524547676734558141 20112906196705378775459303)
  ·
    refine ⟨30169359295058068163188955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20112906196705378775459303 30169359295058068163188955)
    ·
      refine ⟨45254038942587102244783433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30169359295058068163188955 45254038942587102244783433)
      ·
        refine ⟨33940529206940326683587575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45254038942587102244783433 33940529206940326683587575)
        ·
          refine ⟨50910793810410490025381363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33940529206940326683587575 50910793810410490025381363)
          ·
            refine ⟨76366190715615735038072045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50910793810410490025381363 76366190715615735038072045)
            ·
              refine ⟨28637321518355900639277017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76366190715615735038072045 28637321518355900639277017)
              ·
                refine ⟨21477991138766925479457763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28637321518355900639277017 21477991138766925479457763)
                ·
                  refine ⟨32216986708150388219186645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21477991138766925479457763 32216986708150388219186645)
                  ·
                    refine ⟨755085625972274723887187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32216986708150388219186645 755085625972274723887187)
                    ·
                      rfl

theorem cell22_2205786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_2205786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205786 prefixEnd_2205786 := by exact prefixLift 2205786
  have htrace : WordTrace (prefixWord ++ tailWord_2205786) baseStart_2205786 baseEnd_2205786 := by
    simpa [prefixWord, tailWord_2205786, baseEnd_2205786] using wordTrace_append hprefix tailTrace_2205786
  have hstable : (prefixWord ++ tailWord_2205786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205786).length < 2 ^ (prefixWord ++ tailWord_2205786).sum := by decide
  have hdescent : baseEnd_2205786 < baseStart_2205786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205792 : List Nat := [2, 1, 1, 3, 2, 4, 2, 3, 1, 3]
def baseStart_2205792 : Nat := 118140960795 + 2205792 * 2 ^ 59
def prefixEnd_2205792 : Nat := 4983230072969 + 3 ^ 40 * 2205792 * 2
def baseEnd_2205792 : Nat := 755087679894892708237169

theorem tailTrace_2205792 : CollatzResearch.WordTrace tailWord_2205792 prefixEnd_2205792 755087679894892708237169 := by
  unfold tailWord_2205792
  simp only [CollatzResearch.WordTrace]
  refine ⟨40225921812399889063277815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53634562416533185417703753 40225921812399889063277815)
  ·
    refine ⟨60338882718599833594916723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40225921812399889063277815 60338882718599833594916723)
    ·
      refine ⟨90508324077899750392375085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60338882718599833594916723 90508324077899750392375085)
      ·
        refine ⟨33940621529212406397140657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90508324077899750392375085 33940621529212406397140657)
        ·
          refine ⟨25455466146909304797855493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33940621529212406397140657 25455466146909304797855493)
          ·
            refine ⟨4772899902545494649597905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25455466146909304797855493 4772899902545494649597905)
            ·
              refine ⟨3579674926909120987198429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4772899902545494649597905 3579674926909120987198429)
              ·
                refine ⟨1342378097590920370199411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3579674926909120987198429 1342378097590920370199411)
                ·
                  refine ⟨2013567146386380555299117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342378097590920370199411 2013567146386380555299117)
                  ·
                    refine ⟨755087679894892708237169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013567146386380555299117 755087679894892708237169)
                    ·
                      rfl

theorem cell22_2205792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 3].length) (baseStart_2205792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205792 prefixEnd_2205792 := by exact prefixLift 2205792
  have htrace : WordTrace (prefixWord ++ tailWord_2205792) baseStart_2205792 baseEnd_2205792 := by
    simpa [prefixWord, tailWord_2205792, baseEnd_2205792] using wordTrace_append hprefix tailTrace_2205792
  have hstable : (prefixWord ++ tailWord_2205792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205792).length < 2 ^ (prefixWord ++ tailWord_2205792).sum := by decide
  have hdescent : baseEnd_2205792 < baseStart_2205792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205882 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_2205882 : Nat := 118140960795 + 2205882 * 2 ^ 59
def prefixEnd_2205882 : Nat := 4983230072969 + 3 ^ 40 * 2205882 * 2
def baseEnd_2205882 : Nat := 755118488734162473486893

theorem tailTrace_2205882 : CollatzResearch.WordTrace tailWord_2205882 prefixEnd_2205882 755118488734162473486893 := by
  unfold tailWord_2205882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20113781548618430874332975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53636750796315815664887933 20113781548618430874332975)
  ·
    refine ⟨30170672322927646311499463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20113781548618430874332975 30170672322927646311499463)
    ·
      refine ⟨45256008484391469467249195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30170672322927646311499463 45256008484391469467249195)
      ·
        refine ⟨67884012726587204200873793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45256008484391469467249195 67884012726587204200873793)
        ·
          refine ⟨50913009544940403150655345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67884012726587204200873793 50913009544940403150655345)
          ·
            refine ⟨38184757158705302362991509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50913009544940403150655345 38184757158705302362991509)
            ·
              refine ⟨1789910491814311048265227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38184757158705302362991509 1789910491814311048265227)
              ·
                refine ⟨2684865737721466572397841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789910491814311048265227 2684865737721466572397841)
                ·
                  refine ⟨2013649303291099929298381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2684865737721466572397841 2013649303291099929298381)
                  ·
                    refine ⟨755118488734162473486893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013649303291099929298381 755118488734162473486893)
                    ·
                      rfl

theorem cell22_2205882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_2205882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205882 prefixEnd_2205882 := by exact prefixLift 2205882
  have htrace : WordTrace (prefixWord ++ tailWord_2205882) baseStart_2205882 baseEnd_2205882 := by
    simpa [prefixWord, tailWord_2205882, baseEnd_2205882] using wordTrace_append hprefix tailTrace_2205882
  have hstable : (prefixWord ++ tailWord_2205882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205882).length < 2 ^ (prefixWord ++ tailWord_2205882).sum := by decide
  have hdescent : baseEnd_2205882 < baseStart_2205882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205916 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2205916 : Nat := 118140960795 + 2205916 * 2 ^ 59
def prefixEnd_2205916 : Nat := 4983230072969 + 3 ^ 40 * 2205916 * 2
def baseEnd_2205916 : Nat := 755130127628997718136789

theorem tailTrace_2205916 : CollatzResearch.WordTrace tailWord_2205916 prefixEnd_2205916 755130127628997718136789 := by
  unfold tailWord_2205916
  simp only [CollatzResearch.WordTrace]
  refine ⟨40228183138175273652034801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53637577517567031536046401 40228183138175273652034801)
  ·
    refine ⟨30171137353631455239026101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40228183138175273652034801 30171137353631455239026101)
    ·
      refine ⟨2828544126902948928658697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30171137353631455239026101 2828544126902948928658697)
      ·
        refine ⟨2121408095177211696494023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2828544126902948928658697 2121408095177211696494023)
        ·
          refine ⟨3182112142765817544741035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121408095177211696494023 3182112142765817544741035)
          ·
            refine ⟨4773168214148726317111553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182112142765817544741035 4773168214148726317111553)
            ·
              refine ⟨3579876160611544737833665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4773168214148726317111553 3579876160611544737833665)
              ·
                refine ⟨2684907120458658553375249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3579876160611544737833665 2684907120458658553375249)
                ·
                  refine ⟨2013680340343993915031437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2684907120458658553375249 2013680340343993915031437)
                  ·
                    refine ⟨755130127628997718136789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013680340343993915031437 755130127628997718136789)
                    ·
                      rfl

theorem cell22_2205916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2205916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2205916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2205916 prefixEnd_2205916 := by exact prefixLift 2205916
  have htrace : WordTrace (prefixWord ++ tailWord_2205916) baseStart_2205916 baseEnd_2205916 := by
    simpa [prefixWord, tailWord_2205916, baseEnd_2205916] using wordTrace_append hprefix tailTrace_2205916
  have hstable : (prefixWord ++ tailWord_2205916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205916).length < 2 ^ (prefixWord ++ tailWord_2205916).sum := by decide
  have hdescent : baseEnd_2205916 < baseStart_2205916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206004 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2206004 : Nat := 118140960795 + 2206004 * 2 ^ 59
def prefixEnd_2206004 : Nat := 4983230072969 + 3 ^ 40 * 2206004 * 2
def baseEnd_2206004 : Nat := 755160251827394821936519

theorem tailTrace_2206004 : CollatzResearch.WordTrace tailWord_2206004 prefixEnd_2206004 755160251827394821936519 := by
  unfold tailWord_2206004
  simp only [CollatzResearch.WordTrace]
  refine ⟨40229787950015869166636533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53639717266687825555515377 40229787950015869166636533)
  ·
    refine ⟨3771542620313987734372175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40229787950015869166636533 3771542620313987734372175)
    ·
      refine ⟨5657313930470981601558263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3771542620313987734372175 5657313930470981601558263)
      ·
        refine ⟨8485970895706472402337395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657313930470981601558263 8485970895706472402337395)
        ·
          refine ⟨12728956343559708603506093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8485970895706472402337395 12728956343559708603506093)
          ·
            refine ⟨4773358628834890726314785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12728956343559708603506093 4773358628834890726314785)
            ·
              refine ⟨3580018971626168044736089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4773358628834890726314785 3580018971626168044736089)
              ·
                refine ⟨2685014228719626033552067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3580018971626168044736089 2685014228719626033552067)
                ·
                  refine ⟨4027521343079439050328101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685014228719626033552067 4027521343079439050328101)
                  ·
                    refine ⟨755160251827394821936519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4027521343079439050328101 755160251827394821936519)
                    ·
                      rfl

theorem cell22_2206004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2206004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206004 prefixEnd_2206004 := by exact prefixLift 2206004
  have htrace : WordTrace (prefixWord ++ tailWord_2206004) baseStart_2206004 baseEnd_2206004 := by
    simpa [prefixWord, tailWord_2206004, baseEnd_2206004] using wordTrace_append hprefix tailTrace_2206004
  have hstable : (prefixWord ++ tailWord_2206004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206004).length < 2 ^ (prefixWord ++ tailWord_2206004).sum := by decide
  have hdescent : baseEnd_2206004 < baseStart_2206004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206015 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 2, 4]
def baseStart_2206015 : Nat := 118140960795 + 2206015 * 2 ^ 59
def prefixEnd_2206015 : Nat := 4983230072969 + 3 ^ 40 * 2206015 * 2
def baseEnd_2206015 : Nat := 755164017352194459911485

theorem tailTrace_2206015 : CollatzResearch.WordTrace tailWord_2206015 prefixEnd_2206015 755164017352194459911485 := by
  unfold tailWord_2206015
  simp only [CollatzResearch.WordTrace]
  refine ⟨80459977102991887211923499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53639984735327924807948999 80459977102991887211923499)
  ·
    refine ⟨120689965654487830817885249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80459977102991887211923499 120689965654487830817885249)
    ·
      refine ⟨90517474240865873113413937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120689965654487830817885249 90517474240865873113413937)
      ·
        refine ⟨67888105680649404835060453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90517474240865873113413937 67888105680649404835060453)
        ·
          refine ⟨12729019815121763406573835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67888105680649404835060453 12729019815121763406573835)
          ·
            refine ⟨19093529722682645109860753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12729019815121763406573835 19093529722682645109860753)
            ·
              refine ⟨14320147292011983832395565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19093529722682645109860753 14320147292011983832395565)
              ·
                refine ⟨5370055234504493937148337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14320147292011983832395565 5370055234504493937148337)
                ·
                  refine ⟨4027541425878370452861253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5370055234504493937148337 4027541425878370452861253)
                  ·
                    refine ⟨755164017352194459911485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4027541425878370452861253 755164017352194459911485)
                    ·
                      rfl

theorem cell22_2206015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_2206015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206015 prefixEnd_2206015 := by exact prefixLift 2206015
  have htrace : WordTrace (prefixWord ++ tailWord_2206015) baseStart_2206015 baseEnd_2206015 := by
    simpa [prefixWord, tailWord_2206015, baseEnd_2206015] using wordTrace_append hprefix tailTrace_2206015
  have hstable : (prefixWord ++ tailWord_2206015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206015).length < 2 ^ (prefixWord ++ tailWord_2206015).sum := by decide
  have hdescent : baseEnd_2206015 < baseStart_2206015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206092 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 5]
def baseStart_2206092 : Nat := 118140960795 + 2206092 * 2 ^ 59
def prefixEnd_2206092 : Nat := 4983230072969 + 3 ^ 40 * 2206092 * 2
def baseEnd_2206092 : Nat := 251730125341930641912083

theorem tailTrace_2206092 : CollatzResearch.WordTrace tailWord_2206092 prefixEnd_2206092 251730125341930641912083 := by
  unfold tailWord_2206092
  simp only [CollatzResearch.WordTrace]
  refine ⟨40231392761856464681238265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53641857015808619574984353 40231392761856464681238265)
  ·
    refine ⟨30173544571392348510928699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40231392761856464681238265 30173544571392348510928699)
    ·
      refine ⟨45260316857088522766393049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30173544571392348510928699 45260316857088522766393049)
      ·
        refine ⟨33945237642816392074794787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45260316857088522766393049 33945237642816392074794787)
        ·
          refine ⟨50917856464224588112192181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33945237642816392074794787 50917856464224588112192181)
          ·
            refine ⟨4773549043521055135518017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50917856464224588112192181 4773549043521055135518017)
            ·
              refine ⟨3580161782640791351638513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4773549043521055135518017 3580161782640791351638513)
              ·
                refine ⟨2685121336980593513728885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3580161782640791351638513 2685121336980593513728885)
                ·
                  refine ⟨251730125341930641912083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2685121336980593513728885 251730125341930641912083)
                  ·
                    rfl

theorem cell22_2206092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_2206092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206092 prefixEnd_2206092 := by exact prefixLift 2206092
  have htrace : WordTrace (prefixWord ++ tailWord_2206092) baseStart_2206092 baseEnd_2206092 := by
    simpa [prefixWord, tailWord_2206092, baseEnd_2206092] using wordTrace_append hprefix tailTrace_2206092
  have hstable : (prefixWord ++ tailWord_2206092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206092).length < 2 ^ (prefixWord ++ tailWord_2206092).sum := by decide
  have hdescent : baseEnd_2206092 < baseStart_2206092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206105 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_2206105 : Nat := 118140960795 + 2206105 * 2 ^ 59
def prefixEnd_2206105 : Nat := 4983230072969 + 3 ^ 40 * 2206105 * 2
def baseEnd_2206105 : Nat := 755194826191464225161209

theorem tailTrace_2206105 : CollatzResearch.WordTrace tailWord_2206105 prefixEnd_2206105 755194826191464225161209 := by
  unfold tailWord_2206105
  simp only [CollatzResearch.WordTrace]
  refine ⟨80463259672665832582699769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53642173115110555055133179 80463259672665832582699769)
  ·
    refine ⟨60347444754499374437024827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80463259672665832582699769 60347444754499374437024827)
    ·
      refine ⟨90521167131749061655537241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60347444754499374437024827 90521167131749061655537241)
      ·
        refine ⟨67890875348811796241652931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90521167131749061655537241 67890875348811796241652931)
        ·
          refine ⟨101836313023217694362479397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67890875348811796241652931 101836313023217694362479397)
          ·
            refine ⟨19094308691853317692964887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101836313023217694362479397 19094308691853317692964887)
            ·
              refine ⟨28641463037779976539447331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19094308691853317692964887 28641463037779976539447331)
              ·
                refine ⟨42962194556669964809170997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28641463037779976539447331 42962194556669964809170997)
                ·
                  refine ⟨4027705739687809200859781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42962194556669964809170997 4027705739687809200859781)
                  ·
                    refine ⟨755194826191464225161209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4027705739687809200859781 755194826191464225161209)
                    ·
                      rfl

theorem cell22_2206105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_2206105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206105 prefixEnd_2206105 := by exact prefixLift 2206105
  have htrace : WordTrace (prefixWord ++ tailWord_2206105) baseStart_2206105 baseEnd_2206105 := by
    simpa [prefixWord, tailWord_2206105, baseEnd_2206105] using wordTrace_append hprefix tailTrace_2206105
  have hstable : (prefixWord ++ tailWord_2206105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206105).length < 2 ^ (prefixWord ++ tailWord_2206105).sum := by decide
  have hdescent : baseEnd_2206105 < baseStart_2206105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206227 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 5]
def baseStart_2206227 : Nat := 118140960795 + 2206227 * 2 ^ 59
def prefixEnd_2206227 : Nat := 4983230072969 + 3 ^ 40 * 2206227 * 2
def baseEnd_2206227 : Nat := 251745529761565524536945

theorem tailTrace_2206227 : CollatzResearch.WordTrace tailWord_2206227 prefixEnd_2206227 251745529761565524536945 := by
  unfold tailWord_2206227
  simp only [CollatzResearch.WordTrace]
  refine ⟨80467709378223847418640935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53645139585482564945760623 80467709378223847418640935)
  ·
    refine ⟨120701564067335771127961403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80467709378223847418640935 120701564067335771127961403)
    ·
      refine ⟨181052346101003656691942105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120701564067335771127961403 181052346101003656691942105)
      ·
        refine ⟨135789259575752742518956579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181052346101003656691942105 135789259575752742518956579)
        ·
          refine ⟨203683889363629113778434869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135789259575752742518956579 203683889363629113778434869)
          ·
            refine ⟨19095364627840229416728269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 203683889363629113778434869 19095364627840229416728269)
            ·
              refine ⟨7160761735440086031273101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19095364627840229416728269 7160761735440086031273101)
              ·
                refine ⟨2685285650790032261727413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7160761735440086031273101 2685285650790032261727413)
                ·
                  refine ⟨251745529761565524536945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2685285650790032261727413 251745529761565524536945)
                  ·
                    rfl

theorem cell22_2206227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 5].length) (baseStart_2206227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206227 prefixEnd_2206227 := by exact prefixLift 2206227
  have htrace : WordTrace (prefixWord ++ tailWord_2206227) baseStart_2206227 baseEnd_2206227 := by
    simpa [prefixWord, tailWord_2206227, baseEnd_2206227] using wordTrace_append hprefix tailTrace_2206227
  have hstable : (prefixWord ++ tailWord_2206227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206227).length < 2 ^ (prefixWord ++ tailWord_2206227).sum := by decide
  have hdescent : baseEnd_2206227 < baseStart_2206227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206242 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2206242 : Nat := 118140960795 + 2206242 * 2 ^ 59
def prefixEnd_2206242 : Nat := 4983230072969 + 3 ^ 40 * 2206242 * 2
def baseEnd_2206242 : Nat := 755241724091241534485789

theorem tailTrace_2206242 : CollatzResearch.WordTrace tailWord_2206242 prefixEnd_2206242 755241724091241534485789 := by
  unfold tailWord_2206242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20117064118292376245109245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53645504315446336653624653 20117064118292376245109245)
  ·
    refine ⟨7543899044359641091915967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20117064118292376245109245 7543899044359641091915967)
    ·
      refine ⟨11315848566539461637873951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7543899044359641091915967 11315848566539461637873951)
      ·
        refine ⟨16973772849809192456810927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11315848566539461637873951 16973772849809192456810927)
        ·
          refine ⟨25460659274713788685216391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16973772849809192456810927 25460659274713788685216391)
          ·
            refine ⟨38190988912070683027824587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25460659274713788685216391 38190988912070683027824587)
            ·
              refine ⟨57286483368106024541736881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38190988912070683027824587 57286483368106024541736881)
              ·
                refine ⟨42964862526079518406302661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57286483368106024541736881 42964862526079518406302661)
                ·
                  refine ⟨8055911723639909701181749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42964862526079518406302661 8055911723639909701181749)
                  ·
                    refine ⟨755241724091241534485789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8055911723639909701181749 755241724091241534485789)
                    ·
                      rfl

theorem cell22_2206242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2206242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206242 prefixEnd_2206242 := by exact prefixLift 2206242
  have htrace : WordTrace (prefixWord ++ tailWord_2206242) baseStart_2206242 baseEnd_2206242 := by
    simpa [prefixWord, tailWord_2206242, baseEnd_2206242] using wordTrace_append hprefix tailTrace_2206242
  have hstable : (prefixWord ++ tailWord_2206242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206242).length < 2 ^ (prefixWord ++ tailWord_2206242).sum := by decide
  have hdescent : baseEnd_2206242 < baseStart_2206242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206287 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 1, 5]
def baseStart_2206287 : Nat := 118140960795 + 2206287 * 2 ^ 59
def prefixEnd_2206287 : Nat := 4983230072969 + 3 ^ 40 * 2206287 * 2
def baseEnd_2206287 : Nat := 755257128510876417110651

theorem tailTrace_2206287 : CollatzResearch.WordTrace tailWord_2206287 prefixEnd_2206287 755257128510876417110651 := by
  unfold tailWord_2206287
  simp only [CollatzResearch.WordTrace]
  refine ⟨80469897758006477665825115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53646598505337651777216743 80469897758006477665825115)
  ·
    refine ⟨120704846637009716498737673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80469897758006477665825115 120704846637009716498737673)
    ·
      refine ⟨90528634977757287374053255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120704846637009716498737673 90528634977757287374053255)
      ·
        refine ⟨135792952466635931061079883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90528634977757287374053255 135792952466635931061079883)
        ·
          refine ⟨203689428699953896591619825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135792952466635931061079883 203689428699953896591619825)
          ·
            refine ⟨152767071524965422443714869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203689428699953896591619825 152767071524965422443714869)
            ·
              refine ⟨14321912955465508354098269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152767071524965422443714869 14321912955465508354098269)
              ·
                refine ⟨5370717358299565632786851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14321912955465508354098269 5370717358299565632786851)
                ·
                  refine ⟨8056076037449348449180277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5370717358299565632786851 8056076037449348449180277)
                  ·
                    refine ⟨755257128510876417110651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8056076037449348449180277 755257128510876417110651)
                    ·
                      rfl

theorem cell22_2206287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_2206287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206287 prefixEnd_2206287 := by exact prefixLift 2206287
  have htrace : WordTrace (prefixWord ++ tailWord_2206287) baseStart_2206287 baseEnd_2206287 := by
    simpa [prefixWord, tailWord_2206287, baseEnd_2206287] using wordTrace_append hprefix tailTrace_2206287
  have hstable : (prefixWord ++ tailWord_2206287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206287).length < 2 ^ (prefixWord ++ tailWord_2206287).sum := by decide
  have hdescent : baseEnd_2206287 < baseStart_2206287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206392 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_2206392 : Nat := 118140960795 + 2206392 * 2 ^ 59
def prefixEnd_2206392 : Nat := 4983230072969 + 3 ^ 40 * 2206392 * 2
def baseEnd_2206392 : Nat := 755293072156691143235329

theorem tailTrace_2206392 : CollatzResearch.WordTrace tailWord_2206392 prefixEnd_2206392 755293072156691143235329 := by
  unfold tailWord_2206392
  simp only [CollatzResearch.WordTrace]
  refine ⟨40236863711313040299198715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53649151615084053732264953 40236863711313040299198715)
  ·
    refine ⟨60355295566969560448798073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40236863711313040299198715 60355295566969560448798073)
    ·
      refine ⟨45266471675227170336598555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60355295566969560448798073 45266471675227170336598555)
      ·
        refine ⟨67899707512840755504897833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45266471675227170336598555 67899707512840755504897833)
        ·
          refine ⟨50924780634630566628673375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67899707512840755504897833 50924780634630566628673375)
          ·
            refine ⟨76387170951945849943010063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50924780634630566628673375 76387170951945849943010063)
            ·
              refine ⟨114580756427918774914515095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76387170951945849943010063 114580756427918774914515095)
              ·
                refine ⟨171871134641878162371772643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114580756427918774914515095 171871134641878162371772643)
                ·
                  refine ⟨257806701962817243557658965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171871134641878162371772643 257806701962817243557658965)
                  ·
                    refine ⟨755293072156691143235329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 257806701962817243557658965 755293072156691143235329)
                    ·
                      rfl

theorem cell22_2206392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_2206392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206392 prefixEnd_2206392 := by exact prefixLift 2206392
  have htrace : WordTrace (prefixWord ++ tailWord_2206392) baseStart_2206392 baseEnd_2206392 := by
    simpa [prefixWord, tailWord_2206392, baseEnd_2206392] using wordTrace_append hprefix tailTrace_2206392
  have hstable : (prefixWord ++ tailWord_2206392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206392).length < 2 ^ (prefixWord ++ tailWord_2206392).sum := by decide
  have hdescent : baseEnd_2206392 < baseStart_2206392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206456 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 2, 3]
def baseStart_2206456 : Nat := 118140960795 + 2206456 * 2 ^ 59
def prefixEnd_2206456 : Nat := 4983230072969 + 3 ^ 40 * 2206456 * 2
def baseEnd_2206456 : Nat := 755314980664616309635133

theorem tailTrace_2206456 : CollatzResearch.WordTrace tailWord_2206456 prefixEnd_2206456 755314980664616309635133 := by
  unfold tailWord_2206456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40238030847197109764363611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53650707796262813019151481 40238030847197109764363611)
  ·
    refine ⟨60357046270795664646545417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40238030847197109764363611 60357046270795664646545417)
    ·
      refine ⟨45267784703096748484909063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60357046270795664646545417 45267784703096748484909063)
      ·
        refine ⟨67901677054645122727363595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45267784703096748484909063 67901677054645122727363595)
        ·
          refine ⟨101852515581967684091045393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67901677054645122727363595 101852515581967684091045393)
          ·
            refine ⟨76389386686475763068284045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101852515581967684091045393 76389386686475763068284045)
            ·
              refine ⟨28646020007428411150606517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76389386686475763068284045 28646020007428411150606517)
              ·
                refine ⟨2685564375696413545369361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28646020007428411150606517 2685564375696413545369361)
                ·
                  refine ⟨2014173281772310159027021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2685564375696413545369361 2014173281772310159027021)
                  ·
                    refine ⟨755314980664616309635133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014173281772310159027021 755314980664616309635133)
                    ·
                      rfl

theorem cell22_2206456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_2206456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206456 prefixEnd_2206456 := by exact prefixLift 2206456
  have htrace : WordTrace (prefixWord ++ tailWord_2206456) baseStart_2206456 baseEnd_2206456 := by
    simpa [prefixWord, tailWord_2206456, baseEnd_2206456] using wordTrace_append hprefix tailTrace_2206456
  have hstable : (prefixWord ++ tailWord_2206456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206456).length < 2 ^ (prefixWord ++ tailWord_2206456).sum := by decide
  have hdescent : baseEnd_2206456 < baseStart_2206456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206471 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2206471 : Nat := 118140960795 + 2206471 * 2 ^ 59
def prefixEnd_2206471 : Nat := 4983230072969 + 3 ^ 40 * 2206471 * 2
def baseEnd_2206471 : Nat := 755320115471161270510087

theorem tailTrace_2206471 : CollatzResearch.WordTrace tailWord_2206471 prefixEnd_2206471 755320115471161270510087 := by
  unfold tailWord_2206471
  simp only [CollatzResearch.WordTrace]
  refine ⟨80476608789339877090523267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53651072526226584727015511 80476608789339877090523267)
  ·
    refine ⟨120714913184009815635784901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80476608789339877090523267 120714913184009815635784901)
    ·
      refine ⟨22634046222001840431709669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120714913184009815635784901 22634046222001840431709669)
      ·
        refine ⟨4243883666625345080945563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22634046222001840431709669 4243883666625345080945563)
        ·
          refine ⟨6365825499938017621418345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243883666625345080945563 6365825499938017621418345)
          ·
            refine ⟨4774369124953513216063759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6365825499938017621418345 4774369124953513216063759)
            ·
              refine ⟨7161553687430269824095639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4774369124953513216063759 7161553687430269824095639)
              ·
                refine ⟨10742330531145404736143459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7161553687430269824095639 10742330531145404736143459)
                ·
                  refine ⟨16113495796718107104215189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10742330531145404736143459 16113495796718107104215189)
                  ·
                    refine ⟨755320115471161270510087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16113495796718107104215189 755320115471161270510087)
                    ·
                      rfl

theorem cell22_2206471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2206471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206471 prefixEnd_2206471 := by exact prefixLift 2206471
  have htrace : WordTrace (prefixWord ++ tailWord_2206471) baseStart_2206471 baseEnd_2206471 := by
    simpa [prefixWord, tailWord_2206471, baseEnd_2206471] using wordTrace_append hprefix tailTrace_2206471
  have hstable : (prefixWord ++ tailWord_2206471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206471).length < 2 ^ (prefixWord ++ tailWord_2206471).sum := by decide
  have hdescent : baseEnd_2206471 < baseStart_2206471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206578 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_2206578 : Nat := 118140960795 + 2206578 * 2 ^ 59
def prefixEnd_2206578 : Nat := 4983230072969 + 3 ^ 40 * 2206578 * 2
def baseEnd_2206578 : Nat := 755356743757848658084759

theorem tailTrace_2206578 : CollatzResearch.WordTrace tailWord_2206578 prefixEnd_2206578 755356743757848658084759 := by
  unfold tailWord_2206578
  simp only [CollatzResearch.WordTrace]
  refine ⟨20120127849988058591167097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53653674266634822909778925 20120127849988058591167097)
  ·
    refine ⟨15090095887491043943375323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20120127849988058591167097 15090095887491043943375323)
    ·
      refine ⟨22635143831236565915062985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15090095887491043943375323 22635143831236565915062985)
      ·
        refine ⟨16976357873427424436297239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22635143831236565915062985 16976357873427424436297239)
        ·
          refine ⟨25464536810141136654445859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16976357873427424436297239 25464536810141136654445859)
          ·
            refine ⟨38196805215211704981668789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25464536810141136654445859 38196805215211704981668789)
            ·
              refine ⟨3580950488926097342031449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38196805215211704981668789 3580950488926097342031449)
              ·
                refine ⟨2685712866694573006523587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3580950488926097342031449 2685712866694573006523587)
                ·
                  refine ⟨4028569300041859509785381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685712866694573006523587 4028569300041859509785381)
                  ·
                    refine ⟨755356743757848658084759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4028569300041859509785381 755356743757848658084759)
                    ·
                      rfl

theorem cell22_2206578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_2206578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206578 prefixEnd_2206578 := by exact prefixLift 2206578
  have htrace : WordTrace (prefixWord ++ tailWord_2206578) baseStart_2206578 baseEnd_2206578 := by
    simpa [prefixWord, tailWord_2206578, baseEnd_2206578] using wordTrace_append hprefix tailTrace_2206578
  have hstable : (prefixWord ++ tailWord_2206578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206578).length < 2 ^ (prefixWord ++ tailWord_2206578).sum := by decide
  have hdescent : baseEnd_2206578 < baseStart_2206578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206591 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 6, 3]
def baseStart_2206591 : Nat := 118140960795 + 2206591 * 2 ^ 59
def prefixEnd_2206591 : Nat := 4983230072969 + 3 ^ 40 * 2206591 * 2
def baseEnd_2206591 : Nat := 755361193923520957509719

theorem tailTrace_2206591 : CollatzResearch.WordTrace tailWord_2206591 prefixEnd_2206591 755361193923520957509719 := by
  unfold tailWord_2206591
  simp only [CollatzResearch.WordTrace]
  refine ⟨80480985548905137584891627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53653990365936758389927751 80480985548905137584891627)
  ·
    refine ⟨120721478323357706377337441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80480985548905137584891627 120721478323357706377337441)
    ·
      refine ⟨90541108742518279783003081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120721478323357706377337441 90541108742518279783003081)
      ·
        refine ⟨67905831556888709837252311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90541108742518279783003081 67905831556888709837252311)
        ·
          refine ⟨101858747335333064755878467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67905831556888709837252311 101858747335333064755878467)
          ·
            refine ⟨152788121002999597133817701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101858747335333064755878467 152788121002999597133817701)
            ·
              refine ⟨28647772688062424462590819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152788121002999597133817701 28647772688062424462590819)
              ·
                refine ⟨42971659032093636693886229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28647772688062424462590819 42971659032093636693886229)
                ·
                  refine ⟨2014296517129389220025917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42971659032093636693886229 2014296517129389220025917)
                  ·
                    refine ⟨755361193923520957509719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014296517129389220025917 755361193923520957509719)
                    ·
                      rfl

theorem cell22_2206591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_2206591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206591 prefixEnd_2206591 := by exact prefixLift 2206591
  have htrace : WordTrace (prefixWord ++ tailWord_2206591) baseStart_2206591 baseEnd_2206591 := by
    simpa [prefixWord, tailWord_2206591, baseEnd_2206591] using wordTrace_append hprefix tailTrace_2206591
  have hstable : (prefixWord ++ tailWord_2206591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206591).length < 2 ^ (prefixWord ++ tailWord_2206591).sum := by decide
  have hdescent : baseEnd_2206591 < baseStart_2206591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206625 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 2, 3]
def baseStart_2206625 : Nat := 118140960795 + 2206625 * 2 ^ 59
def prefixEnd_2206625 : Nat := 4983230072969 + 3 ^ 40 * 2206625 * 2
def baseEnd_2206625 : Nat := 755372832818356202159615

theorem tailTrace_2206625 : CollatzResearch.WordTrace tailWord_2206625 prefixEnd_2206625 755372832818356202159615 := by
  unfold tailWord_2206625
  simp only [CollatzResearch.WordTrace]
  refine ⟨80482225630781961391629329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53654817087187974261086219 80482225630781961391629329)
  ·
    refine ⟨60361669223086471043721997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80482225630781961391629329 60361669223086471043721997)
    ·
      refine ⟨22635625958657426641395749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60361669223086471043721997 22635625958657426641395749)
      ·
        refine ⟨4244179867248267495261703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22635625958657426641395749 4244179867248267495261703)
        ·
          refine ⟨6366269800872401242892555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244179867248267495261703 6366269800872401242892555)
          ·
            refine ⟨9549404701308601864338833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6366269800872401242892555 9549404701308601864338833)
            ·
              refine ⟨7162053525981451398254125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9549404701308601864338833 7162053525981451398254125)
              ·
                refine ⟨2685770072243044274345297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7162053525981451398254125 2685770072243044274345297)
                ·
                  refine ⟨2014327554182283205758973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2685770072243044274345297 2014327554182283205758973)
                  ·
                    refine ⟨755372832818356202159615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014327554182283205758973 755372832818356202159615)
                    ·
                      rfl

theorem cell22_2206625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_2206625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206625 prefixEnd_2206625 := by exact prefixLift 2206625
  have htrace : WordTrace (prefixWord ++ tailWord_2206625) baseStart_2206625 baseEnd_2206625 := by
    simpa [prefixWord, tailWord_2206625, baseEnd_2206625] using wordTrace_append hprefix tailTrace_2206625
  have hstable : (prefixWord ++ tailWord_2206625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206625).length < 2 ^ (prefixWord ++ tailWord_2206625).sum := by decide
  have hdescent : baseEnd_2206625 < baseStart_2206625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206670 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_2206670 : Nat := 118140960795 + 2206670 * 2 ^ 59
def prefixEnd_2206670 : Nat := 4983230072969 + 3 ^ 40 * 2206670 * 2
def baseEnd_2206670 : Nat := 755388237237991084784477

theorem tailTrace_2206670 : CollatzResearch.WordTrace tailWord_2206670 prefixEnd_2206670 755388237237991084784477 := by
  unfold tailWord_2206670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060483364452366759627183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53655911277079289384678309 10060483364452366759627183)
  ·
    refine ⟨15090725046678550139440775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10060483364452366759627183 15090725046678550139440775)
    ·
      refine ⟨22636087570017825209161163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15090725046678550139440775 22636087570017825209161163)
      ·
        refine ⟨33954131355026737813741745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22636087570017825209161163 33954131355026737813741745)
        ·
          refine ⟨25465598516270053360306309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33954131355026737813741745 25465598516270053360306309)
          ·
            refine ⟨4774799721800635005057433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25465598516270053360306309 4774799721800635005057433)
            ·
              refine ⟨3581099791350476253793075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4774799721800635005057433 3581099791350476253793075)
              ·
                refine ⟨5371649687025714380689613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581099791350476253793075 5371649687025714380689613)
                ·
                  refine ⟨2014368632634642892758605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5371649687025714380689613 2014368632634642892758605)
                  ·
                    refine ⟨755388237237991084784477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014368632634642892758605 755388237237991084784477)
                    ·
                      rfl

theorem cell22_2206670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_2206670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206670 prefixEnd_2206670 := by exact prefixLift 2206670
  have htrace : WordTrace (prefixWord ++ tailWord_2206670) baseStart_2206670 baseEnd_2206670 := by
    simpa [prefixWord, tailWord_2206670, baseEnd_2206670] using wordTrace_append hprefix tailTrace_2206670
  have hstable : (prefixWord ++ tailWord_2206670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206670).length < 2 ^ (prefixWord ++ tailWord_2206670).sum := by decide
  have hdescent : baseEnd_2206670 < baseStart_2206670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206713 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_2206713 : Nat := 118140960795 + 2206713 * 2 ^ 59
def prefixEnd_2206713 : Nat := 4983230072969 + 3 ^ 40 * 2206713 * 2
def baseEnd_2206713 : Nat := 755402957016753305959345

theorem tailTrace_2206713 : CollatzResearch.WordTrace tailWord_2206713 prefixEnd_2206713 755402957016753305959345 := by
  unfold tailWord_2206713
  simp only [CollatzResearch.WordTrace]
  refine ⟨80485435254463152420832793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53656956836308768280555195 80485435254463152420832793)
  ·
    refine ⟨60364076440847364315624595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80485435254463152420832793 60364076440847364315624595)
    ·
      refine ⟨90546114661271046473436893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60364076440847364315624595 90546114661271046473436893)
      ·
        refine ⟨33954792997976642427538835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90546114661271046473436893 33954792997976642427538835)
        ·
          refine ⟨50932189496964963641308253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33954792997976642427538835 50932189496964963641308253)
          ·
            refine ⟨19099571061361861365490595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50932189496964963641308253 19099571061361861365490595)
            ·
              refine ⟨28649356592042792048235893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19099571061361861365490595 28649356592042792048235893)
              ·
                refine ⟨2685877180504011754522115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28649356592042792048235893 2685877180504011754522115)
                ·
                  refine ⟨4028815770756017631783173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685877180504011754522115 4028815770756017631783173)
                  ·
                    refine ⟨755402957016753305959345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4028815770756017631783173 755402957016753305959345)
                    ·
                      rfl

theorem cell22_2206713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_2206713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206713 prefixEnd_2206713 := by exact prefixLift 2206713
  have htrace : WordTrace (prefixWord ++ tailWord_2206713) baseStart_2206713 baseEnd_2206713 := by
    simpa [prefixWord, tailWord_2206713, baseEnd_2206713] using wordTrace_append hprefix tailTrace_2206713
  have hstable : (prefixWord ++ tailWord_2206713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206713).length < 2 ^ (prefixWord ++ tailWord_2206713).sum := by decide
  have hdescent : baseEnd_2206713 < baseStart_2206713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206728 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 6]
def baseStart_2206728 : Nat := 118140960795 + 2206728 * 2 ^ 59
def prefixEnd_2206728 : Nat := 4983230072969 + 3 ^ 40 * 2206728 * 2
def baseEnd_2206728 : Nat := 251802697274432755611433

theorem tailTrace_2206728 : CollatzResearch.WordTrace tailWord_2206728 prefixEnd_2206728 251802697274432755611433 := by
  unfold tailWord_2206728
  simp only [CollatzResearch.WordTrace]
  refine ⟨40242991174704404991314419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53657321566272539988419225 40242991174704404991314419)
  ·
    refine ⟨60364486762056607486971629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40242991174704404991314419 60364486762056607486971629)
    ·
      refine ⟨22636682535771227807614361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60364486762056607486971629 22636682535771227807614361)
      ·
        refine ⟨16977511901828420855710771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22636682535771227807614361 16977511901828420855710771)
        ·
          refine ⟨25466267852742631283566157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16977511901828420855710771 25466267852742631283566157)
          ·
            refine ⟨9549850444778486731337309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25466267852742631283566157 9549850444778486731337309)
            ·
              refine ⟨3581193916791932524251491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9549850444778486731337309 3581193916791932524251491)
              ·
                refine ⟨5371790875187898786377237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581193916791932524251491 5371790875187898786377237)
                ·
                  refine ⟨251802697274432755611433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5371790875187898786377237 251802697274432755611433)
                  ·
                    rfl

theorem cell22_2206728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_2206728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206728 prefixEnd_2206728 := by exact prefixLift 2206728
  have htrace : WordTrace (prefixWord ++ tailWord_2206728) baseStart_2206728 baseEnd_2206728 := by
    simpa [prefixWord, tailWord_2206728, baseEnd_2206728] using wordTrace_append hprefix tailTrace_2206728
  have hstable : (prefixWord ++ tailWord_2206728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206728).length < 2 ^ (prefixWord ++ tailWord_2206728).sum := by decide
  have hdescent : baseEnd_2206728 < baseStart_2206728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206777 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 2, 3]
def baseStart_2206777 : Nat := 118140960795 + 2206777 * 2 ^ 59
def prefixEnd_2206777 : Nat := 4983230072969 + 3 ^ 40 * 2206777 * 2
def baseEnd_2206777 : Nat := 755424865524678472359149

theorem tailTrace_2206777 : CollatzResearch.WordTrace tailWord_2206777 prefixEnd_2206777 755424865524678472359149 := by
  unfold tailWord_2206777
  simp only [CollatzResearch.WordTrace]
  refine ⟨80487769526231291351162585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53658513017487527567441723 80487769526231291351162585)
  ·
    refine ⟨60365827144673468513371939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80487769526231291351162585 60365827144673468513371939)
    ·
      refine ⟨90548740717010202770057909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60365827144673468513371939 90548740717010202770057909)
      ·
        refine ⟨8488944442219706509692929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90548740717010202770057909 8488944442219706509692929)
        ·
          refine ⟨6366708331664779882269697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8488944442219706509692929 6366708331664779882269697)
          ·
            refine ⟨4775031248748584911702273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6366708331664779882269697 4775031248748584911702273)
            ·
              refine ⟨3581273436561438683776705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4775031248748584911702273 3581273436561438683776705)
              ·
                refine ⟨2685955077421079012832529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3581273436561438683776705 2685955077421079012832529)
                ·
                  refine ⟨2014466308065809259624397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2685955077421079012832529 2014466308065809259624397)
                  ·
                    refine ⟨755424865524678472359149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014466308065809259624397 755424865524678472359149)
                    ·
                      rfl

theorem cell22_2206777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_2206777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206777 prefixEnd_2206777 := by exact prefixLift 2206777
  have htrace : WordTrace (prefixWord ++ tailWord_2206777) baseStart_2206777 baseEnd_2206777 := by
    simpa [prefixWord, tailWord_2206777, baseEnd_2206777] using wordTrace_append hprefix tailTrace_2206777
  have hstable : (prefixWord ++ tailWord_2206777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206777).length < 2 ^ (prefixWord ++ tailWord_2206777).sum := by decide
  have hdescent : baseEnd_2206777 < baseStart_2206777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206805 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_2206805 : Nat := 118140960795 + 2206805 * 2 ^ 59
def prefixEnd_2206805 : Nat := 4983230072969 + 3 ^ 40 * 2206805 * 2
def baseEnd_2206805 : Nat := 755434450496895732659063

theorem tailTrace_2206805 : CollatzResearch.WordTrace tailWord_2206805 prefixEnd_2206805 755434450496895732659063 := by
  unfold tailWord_2206805
  simp only [CollatzResearch.WordTrace]
  refine ⟨80488790770129852133181869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53659193846753234755454579 80488790770129852133181869)
  ·
    refine ⟨30183296538798694549943201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80488790770129852133181869 30183296538798694549943201)
    ·
      refine ⟨22637472404099020912457401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30183296538798694549943201 22637472404099020912457401)
      ·
        refine ⟨16978104303074265684343051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22637472404099020912457401 16978104303074265684343051)
        ·
          refine ⟨25467156454611398526514577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16978104303074265684343051 25467156454611398526514577)
          ·
            refine ⟨19100367340958548894885933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25467156454611398526514577 19100367340958548894885933)
            ·
              refine ⟨7162637752859455835582225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19100367340958548894885933 7162637752859455835582225)
              ·
                refine ⟨5371978314644591876686669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7162637752859455835582225 5371978314644591876686669)
                ·
                  refine ⟨2014491867991721953757501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5371978314644591876686669 2014491867991721953757501)
                  ·
                    refine ⟨755434450496895732659063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014491867991721953757501 755434450496895732659063)
                    ·
                      rfl

theorem cell22_2206805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_2206805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206805 prefixEnd_2206805 := by exact prefixLift 2206805
  have htrace : WordTrace (prefixWord ++ tailWord_2206805) baseStart_2206805 baseEnd_2206805 := by
    simpa [prefixWord, tailWord_2206805, baseEnd_2206805] using wordTrace_append hprefix tailTrace_2206805
  have hstable : (prefixWord ++ tailWord_2206805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206805).length < 2 ^ (prefixWord ++ tailWord_2206805).sum := by decide
  have hdescent : baseEnd_2206805 < baseStart_2206805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206848 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_2206848 : Nat := 118140960795 + 2206848 * 2 ^ 59
def prefixEnd_2206848 : Nat := 4983230072969 + 3 ^ 40 * 2206848 * 2
def baseEnd_2206848 : Nat := 755449170275657953833931

theorem tailTrace_2206848 : CollatzResearch.WordTrace tailWord_2206848 prefixEnd_2206848 755449170275657953833931 := by
  unfold tailWord_2206848
  simp only [CollatzResearch.WordTrace]
  refine ⟨40245179554487035238498599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53660239405982713651331465 40245179554487035238498599)
  ·
    refine ⟨60367769331730552857747899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40245179554487035238498599 60367769331730552857747899)
    ·
      refine ⟨90551653997595829286621849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60367769331730552857747899 90551653997595829286621849)
      ·
        refine ⟨67913740498196871964966387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90551653997595829286621849 67913740498196871964966387)
        ·
          refine ⟨101870610747295307947449581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67913740498196871964966387 101870610747295307947449581)
          ·
            refine ⟨38201479030235740480293593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101870610747295307947449581 38201479030235740480293593)
            ·
              refine ⟨28651109272676805360220195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38201479030235740480293593 28651109272676805360220195)
              ·
                refine ⟨42976663909015208040330293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28651109272676805360220195 42976663909015208040330293)
                ·
                  refine ⟨4029062241470175753780965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42976663909015208040330293 4029062241470175753780965)
                  ·
                    refine ⟨755449170275657953833931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4029062241470175753780965 755449170275657953833931)
                    ·
                      rfl

theorem cell22_2206848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_2206848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206848 prefixEnd_2206848 := by exact prefixLift 2206848
  have htrace : WordTrace (prefixWord ++ tailWord_2206848) baseStart_2206848 baseEnd_2206848 := by
    simpa [prefixWord, tailWord_2206848, baseEnd_2206848] using wordTrace_append hprefix tailTrace_2206848
  have hstable : (prefixWord ++ tailWord_2206848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206848).length < 2 ^ (prefixWord ++ tailWord_2206848).sum := by decide
  have hdescent : baseEnd_2206848 < baseStart_2206848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206852 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 5]
def baseStart_2206852 : Nat := 118140960795 + 2206852 * 2 ^ 59
def prefixEnd_2206852 : Nat := 4983230072969 + 3 ^ 40 * 2206852 * 2
def baseEnd_2206852 : Nat := 251816846519134425577973

theorem tailTrace_2206852 : CollatzResearch.WordTrace tailWord_2206852 prefixEnd_2206852 251816846519134425577973 := by
  unfold tailWord_2206852
  simp only [CollatzResearch.WordTrace]
  refine ⟨40245252500479789580071405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53660336667306386106761873 40245252500479789580071405)
  ·
    refine ⟨15091969687679921092526777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40245252500479789580071405 15091969687679921092526777)
    ·
      refine ⟨11318977265759940819395083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15091969687679921092526777 11318977265759940819395083)
      ·
        refine ⟨16978465898639911229092625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11318977265759940819395083 16978465898639911229092625)
        ·
          refine ⟨12733849423979933421819469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16978465898639911229092625 12733849423979933421819469)
          ·
            refine ⟨4775193533992475033182301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12733849423979933421819469 4775193533992475033182301)
            ·
              refine ⟨1790697575247178137443363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4775193533992475033182301 1790697575247178137443363)
              ·
                refine ⟨2686046362870767206165045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790697575247178137443363 2686046362870767206165045)
                ·
                  refine ⟨251816846519134425577973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686046362870767206165045 251816846519134425577973)
                  ·
                    rfl

theorem cell22_2206852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_2206852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206852 prefixEnd_2206852 := by exact prefixLift 2206852
  have htrace : WordTrace (prefixWord ++ tailWord_2206852) baseStart_2206852 baseEnd_2206852 := by
    simpa [prefixWord, tailWord_2206852, baseEnd_2206852] using wordTrace_append hprefix tailTrace_2206852
  have hstable : (prefixWord ++ tailWord_2206852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206852).length < 2 ^ (prefixWord ++ tailWord_2206852).sum := by decide
  have hdescent : baseEnd_2206852 < baseStart_2206852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206895 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 4, 3]
def baseStart_2206895 : Nat := 118140960795 + 2206895 * 2 ^ 59
def prefixEnd_2206895 : Nat := 4983230072969 + 3 ^ 40 * 2206895 * 2
def baseEnd_2206895 : Nat := 755465259336165497908787

theorem tailTrace_2206895 : CollatzResearch.WordTrace tailWord_2206895 prefixEnd_2206895 755465259336165497908787 := by
  unfold tailWord_2206895
  simp only [CollatzResearch.WordTrace]
  refine ⟨80492073339803797503958139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53661382226535865002638759 80492073339803797503958139)
  ·
    refine ⟨120738110009705696255937209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80492073339803797503958139 120738110009705696255937209)
    ·
      refine ⟨90553582507279272191952907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120738110009705696255937209 90553582507279272191952907)
      ·
        refine ⟨135830373760918908287929361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90553582507279272191952907 135830373760918908287929361)
        ·
          refine ⟨101872780320689181215947021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135830373760918908287929361 101872780320689181215947021)
          ·
            refine ⟨38202292620258442955980133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101872780320689181215947021 38202292620258442955980133)
            ·
              refine ⟨7162929866298458054246275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38202292620258442955980133 7162929866298458054246275)
              ·
                refine ⟨10744394799447687081369413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7162929866298458054246275 10744394799447687081369413)
                ·
                  refine ⟨2014574024896441327756765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10744394799447687081369413 2014574024896441327756765)
                  ·
                    refine ⟨755465259336165497908787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014574024896441327756765 755465259336165497908787)
                    ·
                      rfl

theorem cell22_2206895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_2206895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206895 prefixEnd_2206895 := by exact prefixLift 2206895
  have htrace : WordTrace (prefixWord ++ tailWord_2206895) baseStart_2206895 baseEnd_2206895 := by
    simpa [prefixWord, tailWord_2206895, baseEnd_2206895] using wordTrace_append hprefix tailTrace_2206895
  have hstable : (prefixWord ++ tailWord_2206895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206895).length < 2 ^ (prefixWord ++ tailWord_2206895).sum := by decide
  have hdescent : baseEnd_2206895 < baseStart_2206895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206897 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 6]
def baseStart_2206897 : Nat := 118140960795 + 2206897 * 2 ^ 59
def prefixEnd_2206897 : Nat := 4983230072969 + 3 ^ 40 * 2206897 * 2
def baseEnd_2206897 : Nat := 251821981325679386452927

theorem tailTrace_2206897 : CollatzResearch.WordTrace tailWord_2206897 prefixEnd_2206897 251821981325679386452927 := by
  unfold tailWord_2206897
  simp only [CollatzResearch.WordTrace]
  refine ⟨80492146285796551845530945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53661430857197701230353963 80492146285796551845530945)
  ·
    refine ⟨60369109714347413884148209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80492146285796551845530945 60369109714347413884148209)
    ·
      refine ⟨45276832285760560413111157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60369109714347413884148209 45276832285760560413111157)
      ·
        refine ⟨4244703026790052538729171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45276832285760560413111157 4244703026790052538729171)
        ·
          refine ⟨6367054540185078808093757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244703026790052538729171 6367054540185078808093757)
          ·
            refine ⟨2387645452569404553035159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6367054540185078808093757 2387645452569404553035159)
            ·
              refine ⟨3581468178854106829552739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387645452569404553035159 3581468178854106829552739)
              ·
                refine ⟨5372202268281160244329109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581468178854106829552739 5372202268281160244329109)
                ·
                  refine ⟨251821981325679386452927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5372202268281160244329109 251821981325679386452927)
                  ·
                    rfl

theorem cell22_2206897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_2206897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206897 prefixEnd_2206897 := by exact prefixLift 2206897
  have htrace : WordTrace (prefixWord ++ tailWord_2206897) baseStart_2206897 baseEnd_2206897 := by
    simpa [prefixWord, tailWord_2206897, baseEnd_2206897] using wordTrace_append hprefix tailTrace_2206897
  have hstable : (prefixWord ++ tailWord_2206897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206897).length < 2 ^ (prefixWord ++ tailWord_2206897).sum := by decide
  have hdescent : baseEnd_2206897 < baseStart_2206897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206916 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2206916 : Nat := 118140960795 + 2206916 * 2 ^ 59
def prefixEnd_2206916 : Nat := 4983230072969 + 3 ^ 40 * 2206916 * 2
def baseEnd_2206916 : Nat := 755472448065328443133723

theorem tailTrace_2206916 : CollatzResearch.WordTrace tailWord_2206916 prefixEnd_2206916 755472448065328443133723 := by
  unfold tailWord_2206916
  simp only [CollatzResearch.WordTrace]
  refine ⟨40246419636363859045236301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53661892848485145393648401 40246419636363859045236301)
  ·
    refine ⟨15092407363636447141963613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40246419636363859045236301 15092407363636447141963613)
    ·
      refine ⟨5659652761363667678236355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15092407363636447141963613 5659652761363667678236355)
      ·
        refine ⟨8489479142045501517354533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5659652761363667678236355 8489479142045501517354533)
        ·
          refine ⟨1591777339133531534503975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8489479142045501517354533 1591777339133531534503975)
          ·
            refine ⟨2387666008700297301755963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591777339133531534503975 2387666008700297301755963)
            ·
              refine ⟨3581499013050445952633945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387666008700297301755963 3581499013050445952633945)
              ·
                refine ⟨2686124259787834464475459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3581499013050445952633945 2686124259787834464475459)
                ·
                  refine ⟨4029186389681751696713189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686124259787834464475459 4029186389681751696713189)
                  ·
                    refine ⟨755472448065328443133723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4029186389681751696713189 755472448065328443133723)
                    ·
                      rfl

theorem cell22_2206916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2206916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206916 prefixEnd_2206916 := by exact prefixLift 2206916
  have htrace : WordTrace (prefixWord ++ tailWord_2206916) baseStart_2206916 baseEnd_2206916 := by
    simpa [prefixWord, tailWord_2206916, baseEnd_2206916] using wordTrace_append hprefix tailTrace_2206916
  have hstable : (prefixWord ++ tailWord_2206916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206916).length < 2 ^ (prefixWord ++ tailWord_2206916).sum := by decide
  have hdescent : baseEnd_2206916 < baseStart_2206916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206970 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_2206970 : Nat := 118140960795 + 2206970 * 2 ^ 59
def prefixEnd_2206970 : Nat := 4983230072969 + 3 ^ 40 * 2206970 * 2
def baseEnd_2206970 : Nat := 251830311122963434094519

theorem tailTrace_2206970 : CollatzResearch.WordTrace tailWord_2206970 prefixEnd_2206970 251830311122963434094519 := by
  unfold tailWord_2206970
  simp only [CollatzResearch.WordTrace]
  refine ⟨20123702203633021328234591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53663205876354723541958909 20123702203633021328234591)
  ·
    refine ⟨30185553305449531992351887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20123702203633021328234591 30185553305449531992351887)
    ·
      refine ⟨45278329958174297988527831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30185553305449531992351887 45278329958174297988527831)
      ·
        refine ⟨67917494937261446982791747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45278329958174297988527831 67917494937261446982791747)
        ·
          refine ⟨101876242405892170474187621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67917494937261446982791747 101876242405892170474187621)
          ·
            refine ⟨19101795451104781963910179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101876242405892170474187621 19101795451104781963910179)
            ·
              refine ⟨28652693176657172945865269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19101795451104781963910179 28652693176657172945865269)
              ·
                refine ⟨2686189985311609963674869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28652693176657172945865269 2686189985311609963674869)
                ·
                  refine ⟨251830311122963434094519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686189985311609963674869 251830311122963434094519)
                  ·
                    rfl

theorem cell22_2206970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_2206970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206970 prefixEnd_2206970 := by exact prefixLift 2206970
  have htrace : WordTrace (prefixWord ++ tailWord_2206970) baseStart_2206970 baseEnd_2206970 := by
    simpa [prefixWord, tailWord_2206970, baseEnd_2206970] using wordTrace_append hprefix tailTrace_2206970
  have hstable : (prefixWord ++ tailWord_2206970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206970).length < 2 ^ (prefixWord ++ tailWord_2206970).sum := by decide
  have hdescent : baseEnd_2206970 < baseStart_2206970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2206974 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_2206974 : Nat := 118140960795 + 2206974 * 2 ^ 59
def prefixEnd_2206974 : Nat := 4983230072969 + 3 ^ 40 * 2206974 * 2
def baseEnd_2206974 : Nat := 755492302650635625183545

theorem tailTrace_2206974 : CollatzResearch.WordTrace tailWord_2206974 prefixEnd_2206974 755492302650635625183545 := by
  unfold tailWord_2206974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10061869338314699249510497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53663303137678395997389317 10061869338314699249510497)
  ·
    refine ⟨7546402003736024437132873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10061869338314699249510497 7546402003736024437132873)
    ·
      refine ⟨5659801502802018327849655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7546402003736024437132873 5659801502802018327849655)
      ·
        refine ⟨8489702254203027491774483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5659801502802018327849655 8489702254203027491774483)
        ·
          refine ⟨12734553381304541237661725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8489702254203027491774483 12734553381304541237661725)
          ·
            refine ⟨4775457517989202964123147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12734553381304541237661725 4775457517989202964123147)
            ·
              refine ⟨7163186276983804446184721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775457517989202964123147 7163186276983804446184721)
              ·
                refine ⟨5372389707737853334638541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163186276983804446184721 5372389707737853334638541)
                ·
                  refine ⟨2014646140401695000489453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5372389707737853334638541 2014646140401695000489453)
                  ·
                    refine ⟨755492302650635625183545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014646140401695000489453 755492302650635625183545)
                    ·
                      rfl

theorem cell22_2206974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_2206974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2206974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2206974 prefixEnd_2206974 := by exact prefixLift 2206974
  have htrace : WordTrace (prefixWord ++ tailWord_2206974) baseStart_2206974 baseEnd_2206974 := by
    simpa [prefixWord, tailWord_2206974, baseEnd_2206974] using wordTrace_append hprefix tailTrace_2206974
  have hstable : (prefixWord ++ tailWord_2206974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2206974).length < 2 ^ (prefixWord ++ tailWord_2206974).sum := by decide
  have hdescent : baseEnd_2206974 < baseStart_2206974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2206974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207021 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 5]
def baseStart_2207021 : Nat := 118140960795 + 2207021 * 2 ^ 59
def prefixEnd_2207021 : Nat := 4983230072969 + 3 ^ 40 * 2207021 * 2
def baseEnd_2207021 : Nat := 251836130570381056419467

theorem tailTrace_2207021 : CollatzResearch.WordTrace tailWord_2207021 prefixEnd_2207021 251836130570381056419467 := by
  unfold tailWord_2207021
  simp only [CollatzResearch.WordTrace]
  refine ⟨80496668937347321023044917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53664445958231547348696611 80496668937347321023044917)
  ·
    refine ⟨7546562712876311345910461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80496668937347321023044917 7546562712876311345910461)
    ·
      refine ⟨2829961017328616754716423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7546562712876311345910461 2829961017328616754716423)
      ·
        refine ⟨4244941525992925132074635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829961017328616754716423 4244941525992925132074635)
        ·
          refine ⟨6367412288989387698111953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244941525992925132074635 6367412288989387698111953)
          ·
            refine ⟨4775559216742040773583965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6367412288989387698111953 4775559216742040773583965)
            ·
              refine ⟨1790834706278265290093987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4775559216742040773583965 1790834706278265290093987)
              ·
                refine ⟨2686252059417397935140981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790834706278265290093987 2686252059417397935140981)
                ·
                  refine ⟨251836130570381056419467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686252059417397935140981 251836130570381056419467)
                  ·
                    rfl

theorem cell22_2207021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_2207021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207021 prefixEnd_2207021 := by exact prefixLift 2207021
  have htrace : WordTrace (prefixWord ++ tailWord_2207021) baseStart_2207021 baseEnd_2207021 := by
    simpa [prefixWord, tailWord_2207021, baseEnd_2207021] using wordTrace_append hprefix tailTrace_2207021
  have hstable : (prefixWord ++ tailWord_2207021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207021).length < 2 ^ (prefixWord ++ tailWord_2207021).sum := by decide
  have hdescent : baseEnd_2207021 < baseStart_2207021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207045 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_2207045 : Nat := 118140960795 + 2207045 * 2 ^ 59
def prefixEnd_2207045 : Nat := 4983230072969 + 3 ^ 40 * 2207045 * 2
def baseEnd_2207045 : Nat := 755516607401615106658327

theorem tailTrace_2207045 : CollatzResearch.WordTrace tailWord_2207045 prefixEnd_2207045 755516607401615106658327 := by
  unfold tailWord_2207045
  simp only [CollatzResearch.WordTrace]
  refine ⟨80497544289260373121918589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53665029526173582081279059 80497544289260373121918589)
  ·
    refine ⟨30186579108472639920719471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80497544289260373121918589 30186579108472639920719471)
    ·
      refine ⟨45279868662708959881079207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30186579108472639920719471 45279868662708959881079207)
      ·
        refine ⟨67919802994063439821618811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45279868662708959881079207 67919802994063439821618811)
        ·
          refine ⟨101879704491095159732428217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67919802994063439821618811 101879704491095159732428217)
          ·
            refine ⟨76409778368321369799321163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101879704491095159732428217 76409778368321369799321163)
            ·
              refine ⟨114614667552482054698981745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76409778368321369799321163 114614667552482054698981745)
              ·
                refine ⟨85961000664361541024236309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114614667552482054698981745 85961000664361541024236309)
                ·
                  refine ⟨4029421906141947235511077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85961000664361541024236309 4029421906141947235511077)
                  ·
                    refine ⟨755516607401615106658327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4029421906141947235511077 755516607401615106658327)
                    ·
                      rfl

theorem cell22_2207045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_2207045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207045 prefixEnd_2207045 := by exact prefixLift 2207045
  have htrace : WordTrace (prefixWord ++ tailWord_2207045) baseStart_2207045 baseEnd_2207045 := by
    simpa [prefixWord, tailWord_2207045, baseEnd_2207045] using wordTrace_append hprefix tailTrace_2207045
  have hstable : (prefixWord ++ tailWord_2207045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207045).length < 2 ^ (prefixWord ++ tailWord_2207045).sum := by decide
  have hdescent : baseEnd_2207045 < baseStart_2207045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207047 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2207047 : Nat := 118140960795 + 2207047 * 2 ^ 59
def prefixEnd_2207047 : Nat := 4983230072969 + 3 ^ 40 * 2207047 * 2
def baseEnd_2207047 : Nat := 755517292042487768108321

theorem tailTrace_2207047 : CollatzResearch.WordTrace tailWord_2207047 prefixEnd_2207047 755517292042487768108321 := by
  unfold tailWord_2207047
  simp only [CollatzResearch.WordTrace]
  refine ⟨80497617235253127463491395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53665078156835418308994263 80497617235253127463491395)
  ·
    refine ⟨120746425852879691195237093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80497617235253127463491395 120746425852879691195237093)
    ·
      refine ⟨22639954847414942099106955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120746425852879691195237093 22639954847414942099106955)
      ·
        refine ⟨33959932271122413148660433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22639954847414942099106955 33959932271122413148660433)
        ·
          refine ⟨25469949203341809861495325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33959932271122413148660433 25469949203341809861495325)
          ·
            refine ⟨9551230951253178698060747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25469949203341809861495325 9551230951253178698060747)
            ·
              refine ⟨14326846426879768047091121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9551230951253178698060747 14326846426879768047091121)
              ·
                refine ⟨10745134820159826035318341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14326846426879768047091121 10745134820159826035318341)
                ·
                  refine ⟨2014712778779967381622189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10745134820159826035318341 2014712778779967381622189)
                  ·
                    refine ⟨755517292042487768108321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014712778779967381622189 755517292042487768108321)
                    ·
                      rfl

theorem cell22_2207047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2207047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207047 prefixEnd_2207047 := by exact prefixLift 2207047
  have htrace : WordTrace (prefixWord ++ tailWord_2207047) baseStart_2207047 baseEnd_2207047 := by
    simpa [prefixWord, tailWord_2207047, baseEnd_2207047] using wordTrace_append hprefix tailTrace_2207047
  have hstable : (prefixWord ++ tailWord_2207047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207047).length < 2 ^ (prefixWord ++ tailWord_2207047).sum := by decide
  have hdescent : baseEnd_2207047 < baseStart_2207047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207182 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2207182 : Nat := 118140960795 + 2207182 * 2 ^ 59
def prefixEnd_2207182 : Nat := 4983230072969 + 3 ^ 40 * 2207182 * 2
def baseEnd_2207182 : Nat := 755563505301392415982907

theorem tailTrace_2207182 : CollatzResearch.WordTrace tailWord_2207182 prefixEnd_2207182 755563505301392415982907 := by
  unfold tailWord_2207182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10062817636220505689956975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53668360726509363679770533 10062817636220505689956975)
  ·
    refine ⟨15094226454330758534935463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10062817636220505689956975 15094226454330758534935463)
    ·
      refine ⟨22641339681496137802403195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15094226454330758534935463 22641339681496137802403195)
      ·
        refine ⟨33962009522244206703604793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22641339681496137802403195 33962009522244206703604793)
        ·
          refine ⟨25471507141683155027703595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33962009522244206703604793 25471507141683155027703595)
          ·
            refine ⟨38207260712524732541555393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25471507141683155027703595 38207260712524732541555393)
            ·
              refine ⟨28655445534393549406166545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38207260712524732541555393 28655445534393549406166545)
              ·
                refine ⟨21491584150795162054624909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28655445534393549406166545 21491584150795162054624909)
                ·
                  refine ⟨8059344056548185770484341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21491584150795162054624909 8059344056548185770484341)
                  ·
                    refine ⟨755563505301392415982907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8059344056548185770484341 755563505301392415982907)
                    ·
                      rfl

theorem cell22_2207182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2207182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207182 prefixEnd_2207182 := by exact prefixLift 2207182
  have htrace : WordTrace (prefixWord ++ tailWord_2207182) baseStart_2207182 baseEnd_2207182 := by
    simpa [prefixWord, tailWord_2207182, baseEnd_2207182] using wordTrace_append hprefix tailTrace_2207182
  have hstable : (prefixWord ++ tailWord_2207182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207182).length < 2 ^ (prefixWord ++ tailWord_2207182).sum := by decide
  have hdescent : baseEnd_2207182 < baseStart_2207182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207214 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2207214 : Nat := 118140960795 + 2207214 * 2 ^ 59
def prefixEnd_2207214 : Nat := 4983230072969 + 3 ^ 40 * 2207214 * 2
def baseEnd_2207214 : Nat := 755574459555354999182809

theorem tailTrace_2207214 : CollatzResearch.WordTrace tailWord_2207214 prefixEnd_2207214 755574459555354999182809 := by
  unfold tailWord_2207214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10062963528206014373102587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53669138817098743323213797 10062963528206014373102587)
  ·
    refine ⟨15094445292309021559653881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10062963528206014373102587 15094445292309021559653881)
    ·
      refine ⟨11320833969231766169740411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15094445292309021559653881 11320833969231766169740411)
      ·
        refine ⟨16981250953847649254610617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11320833969231766169740411 16981250953847649254610617)
        ·
          refine ⟨12735938215385736940957963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16981250953847649254610617 12735938215385736940957963)
          ·
            refine ⟨19103907323078605411436945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12735938215385736940957963 19103907323078605411436945)
            ·
              refine ⟨14327930492308954058577709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19103907323078605411436945 14327930492308954058577709)
              ·
                refine ⟨5372973934615857771966641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14327930492308954058577709 5372973934615857771966641)
                ·
                  refine ⟨4029730450961893328974981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5372973934615857771966641 4029730450961893328974981)
                  ·
                    refine ⟨755574459555354999182809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4029730450961893328974981 755574459555354999182809)
                    ·
                      rfl

theorem cell22_2207214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2207214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207214 prefixEnd_2207214 := by exact prefixLift 2207214
  have htrace : WordTrace (prefixWord ++ tailWord_2207214) baseStart_2207214 baseEnd_2207214 := by
    simpa [prefixWord, tailWord_2207214, baseEnd_2207214] using wordTrace_append hprefix tailTrace_2207214
  have hstable : (prefixWord ++ tailWord_2207214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207214).length < 2 ^ (prefixWord ++ tailWord_2207214).sum := by decide
  have hdescent : baseEnd_2207214 < baseStart_2207214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207218 : List Nat := [3, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_2207218 : Nat := 118140960795 + 2207218 * 2 ^ 59
def prefixEnd_2207218 : Nat := 4983230072969 + 3 ^ 40 * 2207218 * 2
def baseEnd_2207218 : Nat := 251858609612366774027599

theorem tailTrace_2207218 : CollatzResearch.WordTrace tailWord_2207218 prefixEnd_2207218 251858609612366774027599 := by
  unfold tailWord_2207218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20125963529408405916991577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53669236078422415778644205 20125963529408405916991577)
  ·
    refine ⟨15094472647056304437743683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20125963529408405916991577 15094472647056304437743683)
    ·
      refine ⟨22641708970584456656615525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15094472647056304437743683 22641708970584456656615525)
      ·
        refine ⟨4245320431984585623115411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22641708970584456656615525 4245320431984585623115411)
        ·
          refine ⟨6367980647976878434673117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245320431984585623115411 6367980647976878434673117)
          ·
            refine ⟨2387992742991329413002419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6367980647976878434673117 2387992742991329413002419)
            ·
              refine ⟨3581989114486994119503629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387992742991329413002419 3581989114486994119503629)
              ·
                refine ⟨1343245917932622794813861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3581989114486994119503629 1343245917932622794813861)
                ·
                  refine ⟨251858609612366774027599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343245917932622794813861 251858609612366774027599)
                  ·
                    rfl

theorem cell22_2207218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_2207218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207218 prefixEnd_2207218 := by exact prefixLift 2207218
  have htrace : WordTrace (prefixWord ++ tailWord_2207218) baseStart_2207218 baseEnd_2207218 := by
    simpa [prefixWord, tailWord_2207218, baseEnd_2207218] using wordTrace_append hprefix tailTrace_2207218
  have hstable : (prefixWord ++ tailWord_2207218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207218).length < 2 ^ (prefixWord ++ tailWord_2207218).sum := by decide
  have hdescent : baseEnd_2207218 < baseStart_2207218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207295 : List Nat := [1, 1, 2, 2, 3, 5, 2, 2, 1, 3]
def baseStart_2207295 : Nat := 118140960795 + 2207295 * 2 ^ 59
def prefixEnd_2207295 : Nat := 4983230072969 + 3 ^ 40 * 2207295 * 2
def baseEnd_2207295 : Nat := 755602187510697787907561

theorem tailTrace_2207295 : CollatzResearch.WordTrace tailWord_2207295 prefixEnd_2207295 755602187510697787907561 := by
  unfold tailWord_2207295
  simp only [CollatzResearch.WordTrace]
  refine ⟨80506662538354665818519339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53671108358903110545679559 80506662538354665818519339)
  ·
    refine ⟨120759993807531998727779009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80506662538354665818519339 120759993807531998727779009)
    ·
      refine ⟨90569995355648999045834257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120759993807531998727779009 90569995355648999045834257)
      ·
        refine ⟨67927496516736749284375693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90569995355648999045834257 67927496516736749284375693)
        ·
          refine ⟨25472811193776280981640885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67927496516736749284375693 25472811193776280981640885)
          ·
            refine ⟨2388076049416526342028833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25472811193776280981640885 2388076049416526342028833)
            ·
              refine ⟨1791057037062394756521625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388076049416526342028833 1791057037062394756521625)
              ·
                refine ⟨1343292777796796067391219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791057037062394756521625 1343292777796796067391219)
                ·
                  refine ⟨2014939166695194101086829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343292777796796067391219 2014939166695194101086829)
                  ·
                    refine ⟨755602187510697787907561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014939166695194101086829 755602187510697787907561)
                    ·
                      rfl

theorem cell22_2207295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 3].length) (baseStart_2207295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207295 prefixEnd_2207295 := by exact prefixLift 2207295
  have htrace : WordTrace (prefixWord ++ tailWord_2207295) baseStart_2207295 baseEnd_2207295 := by
    simpa [prefixWord, tailWord_2207295, baseEnd_2207295] using wordTrace_append hprefix tailTrace_2207295
  have hstable : (prefixWord ++ tailWord_2207295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207295).length < 2 ^ (prefixWord ++ tailWord_2207295).sum := by decide
  have hdescent : baseEnd_2207295 < baseStart_2207295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207319 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 6]
def baseStart_2207319 : Nat := 118140960795 + 2207319 * 2 ^ 59
def prefixEnd_2207319 : Nat := 4983230072969 + 3 ^ 40 * 2207319 * 2
def baseEnd_2207319 : Nat := 251870134400389908435829

theorem tailTrace_2207319 : CollatzResearch.WordTrace tailWord_2207319 prefixEnd_2207319 251870134400389908435829 := by
  unfold tailWord_2207319
  simp only [CollatzResearch.WordTrace]
  refine ⟨80507537890267717917393011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53671691926845145278262007 80507537890267717917393011)
  ·
    refine ⟨120761306835401576876089517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80507537890267717917393011 120761306835401576876089517)
    ·
      refine ⟨45285490063275591328533569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120761306835401576876089517 45285490063275591328533569)
      ·
        refine ⟨33964117547456693496400177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45285490063275591328533569 33964117547456693496400177)
        ·
          refine ⟨25473088160592520122300133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33964117547456693496400177 25473088160592520122300133)
          ·
            refine ⟨4776204030111097522931275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25473088160592520122300133 4776204030111097522931275)
            ·
              refine ⟨7164306045166646284396913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776204030111097522931275 7164306045166646284396913)
              ·
                refine ⟨5373229533874984713297685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7164306045166646284396913 5373229533874984713297685)
                ·
                  refine ⟨251870134400389908435829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5373229533874984713297685 251870134400389908435829)
                  ·
                    rfl

theorem cell22_2207319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 6].length) (baseStart_2207319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207319 prefixEnd_2207319 := by exact prefixLift 2207319
  have htrace : WordTrace (prefixWord ++ tailWord_2207319) baseStart_2207319 baseEnd_2207319 := by
    simpa [prefixWord, tailWord_2207319, baseEnd_2207319] using wordTrace_append hprefix tailTrace_2207319
  have hstable : (prefixWord ++ tailWord_2207319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207319).length < 2 ^ (prefixWord ++ tailWord_2207319).sum := by decide
  have hdescent : baseEnd_2207319 < baseStart_2207319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207338 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_2207338 : Nat := 118140960795 + 2207338 * 2 ^ 59
def prefixEnd_2207338 : Nat := 4983230072969 + 3 ^ 40 * 2207338 * 2
def baseEnd_2207338 : Nat := 755616907289460009082429

theorem tailTrace_2207338 : CollatzResearch.WordTrace tailWord_2207338 prefixEnd_2207338 755616907289460009082429 := by
  unfold tailWord_2207338
  simp only [CollatzResearch.WordTrace]
  refine ⟨20127057719299721040583667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53672153918132589441556445 20127057719299721040583667)
  ·
    refine ⟨30190586578949581560875501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20127057719299721040583667 30190586578949581560875501)
    ·
      refine ⟨11321469967106093085328313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30190586578949581560875501 11321469967106093085328313)
      ·
        refine ⟨8491102475329569813996235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11321469967106093085328313 8491102475329569813996235)
        ·
          refine ⟨12736653712994354720994353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8491102475329569813996235 12736653712994354720994353)
          ·
            refine ⟨9552490284745766040745765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12736653712994354720994353 9552490284745766040745765)
            ·
              refine ⟨1791091928389831132639831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9552490284745766040745765 1791091928389831132639831)
              ·
                refine ⟨2686637892584746698959747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791091928389831132639831 2686637892584746698959747)
                ·
                  refine ⟨4029956838877120048439621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686637892584746698959747 4029956838877120048439621)
                  ·
                    refine ⟨755616907289460009082429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4029956838877120048439621 755616907289460009082429)
                    ·
                      rfl

theorem cell22_2207338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_2207338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207338 prefixEnd_2207338 := by exact prefixLift 2207338
  have htrace : WordTrace (prefixWord ++ tailWord_2207338) baseStart_2207338 baseEnd_2207338 := by
    simpa [prefixWord, tailWord_2207338, baseEnd_2207338] using wordTrace_append hprefix tailTrace_2207338
  have hstable : (prefixWord ++ tailWord_2207338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207338).length < 2 ^ (prefixWord ++ tailWord_2207338).sum := by decide
  have hdescent : baseEnd_2207338 < baseStart_2207338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207424 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_2207424 : Nat := 118140960795 + 2207424 * 2 ^ 59
def prefixEnd_2207424 : Nat := 4983230072969 + 3 ^ 40 * 2207424 * 2
def baseEnd_2207424 : Nat := 755646346846984451432165

theorem tailTrace_2207424 : CollatzResearch.WordTrace tailWord_2207424 prefixEnd_2207424 755646346846984451432165 := by
  unfold tailWord_2207424
  simp only [CollatzResearch.WordTrace]
  refine ⟨40255683777443660424982663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53674245036591547233310217 40255683777443660424982663)
  ·
    refine ⟨60383525666165490637473995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40255683777443660424982663 60383525666165490637473995)
    ·
      refine ⟨90575288499248235956210993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60383525666165490637473995 90575288499248235956210993)
      ·
        refine ⟨67931466374436176967158245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90575288499248235956210993 67931466374436176967158245)
        ·
          refine ⟨12737149945206783181342171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67931466374436176967158245 12737149945206783181342171)
          ·
            refine ⟨19105724917810174772013257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12737149945206783181342171 19105724917810174772013257)
            ·
              refine ⟨14329293688357631079009943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19105724917810174772013257 14329293688357631079009943)
              ·
                refine ⟨21493940532536446618514915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14329293688357631079009943 21493940532536446618514915)
                ·
                  refine ⟨32240910798804669927772373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21493940532536446618514915 32240910798804669927772373)
                  ·
                    refine ⟨755646346846984451432165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32240910798804669927772373 755646346846984451432165)
                    ·
                      rfl

theorem cell22_2207424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_2207424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207424 prefixEnd_2207424 := by exact prefixLift 2207424
  have htrace : WordTrace (prefixWord ++ tailWord_2207424) baseStart_2207424 baseEnd_2207424 := by
    simpa [prefixWord, tailWord_2207424, baseEnd_2207424] using wordTrace_append hprefix tailTrace_2207424
  have hstable : (prefixWord ++ tailWord_2207424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207424).length < 2 ^ (prefixWord ++ tailWord_2207424).sum := by decide
  have hdescent : baseEnd_2207424 < baseStart_2207424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207456 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_2207456 : Nat := 118140960795 + 2207456 * 2 ^ 59
def prefixEnd_2207456 : Nat := 4983230072969 + 3 ^ 40 * 2207456 * 2
def baseEnd_2207456 : Nat := 755657301100947034632067

theorem tailTrace_2207456 : CollatzResearch.WordTrace tailWord_2207456 prefixEnd_2207456 755657301100947034632067 := by
  unfold tailWord_2207456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40256267345385695157565111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53675023127180926876753481 40256267345385695157565111)
  ·
    refine ⟨60384401018078542736347667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40256267345385695157565111 60384401018078542736347667)
    ·
      refine ⟨90576601527117814104521501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60384401018078542736347667 90576601527117814104521501)
      ·
        refine ⟨33966225572669180289195563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90576601527117814104521501 33966225572669180289195563)
        ·
          refine ⟨50949338359003770433793345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33966225572669180289195563 50949338359003770433793345)
          ·
            refine ⟨38212003769252827825345009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50949338359003770433793345 38212003769252827825345009)
            ·
              refine ⟨28659002826939620869008757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38212003769252827825345009 28659002826939620869008757)
              ·
                refine ⟨2686781515025589456469571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28659002826939620869008757 2686781515025589456469571)
                ·
                  refine ⟨4030172272538384184704357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686781515025589456469571 4030172272538384184704357)
                  ·
                    refine ⟨755657301100947034632067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4030172272538384184704357 755657301100947034632067)
                    ·
                      rfl

theorem cell22_2207456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_2207456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207456 prefixEnd_2207456 := by exact prefixLift 2207456
  have htrace : WordTrace (prefixWord ++ tailWord_2207456) baseStart_2207456 baseEnd_2207456 := by
    simpa [prefixWord, tailWord_2207456, baseEnd_2207456] using wordTrace_append hprefix tailTrace_2207456
  have hstable : (prefixWord ++ tailWord_2207456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207456).length < 2 ^ (prefixWord ++ tailWord_2207456).sum := by decide
  have hdescent : baseEnd_2207456 < baseStart_2207456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207499 : List Nat := [1, 1, 1, 1, 5, 1, 2, 10]
def baseStart_2207499 : Nat := 118140960795 + 2207499 * 2 ^ 59
def prefixEnd_2207499 : Nat := 4983230072969 + 3 ^ 40 * 2207499 * 2
def baseEnd_2207499 : Nat := 83963557875523250645215

theorem tailTrace_2207499 : CollatzResearch.WordTrace tailWord_2207499 prefixEnd_2207499 83963557875523250645215 := by
  unfold tailWord_2207499
  simp only [CollatzResearch.WordTrace]
  refine ⟨80514103029615608658945551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53676068686410405772630367 80514103029615608658945551)
  ·
    refine ⟨120771154544423412988418327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80514103029615608658945551 120771154544423412988418327)
    ·
      refine ⟨181156731816635119482627491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120771154544423412988418327 181156731816635119482627491)
      ·
        refine ⟨271735097724952679223941237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181156731816635119482627491 271735097724952679223941237)
        ·
          refine ⟨25475165411714313677244491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 271735097724952679223941237 25475165411714313677244491)
          ·
            refine ⟨38212748117571470515866737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25475165411714313677244491 38212748117571470515866737)
            ·
              refine ⟨28659561088178602886900053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38212748117571470515866737 28659561088178602886900053)
              ·
                refine ⟨83963557875523250645215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28659561088178602886900053 83963557875523250645215)
                ·
                  rfl

theorem cell22_2207499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 10].length) (baseStart_2207499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207499 prefixEnd_2207499 := by exact prefixLift 2207499
  have htrace : WordTrace (prefixWord ++ tailWord_2207499) baseStart_2207499 baseEnd_2207499 := by
    simpa [prefixWord, tailWord_2207499, baseEnd_2207499] using wordTrace_append hprefix tailTrace_2207499
  have hstable : (prefixWord ++ tailWord_2207499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207499).length < 2 ^ (prefixWord ++ tailWord_2207499).sum := by decide
  have hdescent : baseEnd_2207499 < baseStart_2207499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207548 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_2207548 : Nat := 118140960795 + 2207548 * 2 ^ 59
def prefixEnd_2207548 : Nat := 4983230072969 + 3 ^ 40 * 2207548 * 2
def baseEnd_2207548 : Nat := 755688794581089461331785

theorem tailTrace_2207548 : CollatzResearch.WordTrace tailWord_2207548 prefixEnd_2207548 755688794581089461331785 := by
  unfold tailWord_2207548
  simp only [CollatzResearch.WordTrace]
  refine ⟨40257945103219045013739649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53677260137625393351652865 40257945103219045013739649)
  ·
    refine ⟨30193458827414283760304737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40257945103219045013739649 30193458827414283760304737)
    ·
      refine ⟨22645094120560712820228553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30193458827414283760304737 22645094120560712820228553)
      ·
        refine ⟨16983820590420534615171415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22645094120560712820228553 16983820590420534615171415)
        ·
          refine ⟨25475730885630801922757123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16983820590420534615171415 25475730885630801922757123)
          ·
            refine ⟨38213596328446202884135685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25475730885630801922757123 38213596328446202884135685)
            ·
              refine ⟨7165049311583663040775441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38213596328446202884135685 7165049311583663040775441)
              ·
                refine ⟨5373786983687747280581581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7165049311583663040775441 5373786983687747280581581)
                ·
                  refine ⟨2015170118882905230218093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5373786983687747280581581 2015170118882905230218093)
                  ·
                    refine ⟨755688794581089461331785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2015170118882905230218093 755688794581089461331785)
                    ·
                      rfl

theorem cell22_2207548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_2207548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207548 prefixEnd_2207548 := by exact prefixLift 2207548
  have htrace : WordTrace (prefixWord ++ tailWord_2207548) baseStart_2207548 baseEnd_2207548 := by
    simpa [prefixWord, tailWord_2207548, baseEnd_2207548] using wordTrace_append hprefix tailTrace_2207548
  have hstable : (prefixWord ++ tailWord_2207548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207548).length < 2 ^ (prefixWord ++ tailWord_2207548).sum := by decide
  have hdescent : baseEnd_2207548 < baseStart_2207548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207550 : List Nat := [4, 2, 1, 2, 2, 3, 2, 6]
def baseStart_2207550 : Nat := 118140960795 + 2207550 * 2 ^ 59
def prefixEnd_2207550 : Nat := 4983230072969 + 3 ^ 40 * 2207550 * 2
def baseEnd_2207550 : Nat := 83965497691329124753531

theorem tailTrace_2207550 : CollatzResearch.WordTrace tailWord_2207550 prefixEnd_2207550 83965497691329124753531 := by
  unfold tailWord_2207550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064495394053855546131513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53677308768287229579368069 10064495394053855546131513)
  ·
    refine ⟨7548371545540391659598635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10064495394053855546131513 7548371545540391659598635)
    ·
      refine ⟨11322557318310587489397953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7548371545540391659598635 11322557318310587489397953)
      ·
        refine ⟨8491917988732940617048465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11322557318310587489397953 8491917988732940617048465)
        ·
          refine ⟨6368938491549705462786349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8491917988732940617048465 6368938491549705462786349)
          ·
            refine ⟨2388351934331139548544881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6368938491549705462786349 2388351934331139548544881)
            ·
              refine ⟨1791263950748354661408661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388351934331139548544881 1791263950748354661408661)
              ·
                refine ⟨83965497691329124753531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1791263950748354661408661 83965497691329124753531)
                ·
                  rfl

theorem cell22_2207550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_2207550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207550 prefixEnd_2207550 := by exact prefixLift 2207550
  have htrace : WordTrace (prefixWord ++ tailWord_2207550) baseStart_2207550 baseEnd_2207550 := by
    simpa [prefixWord, tailWord_2207550, baseEnd_2207550] using wordTrace_append hprefix tailTrace_2207550
  have hstable : (prefixWord ++ tailWord_2207550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207550).length < 2 ^ (prefixWord ++ tailWord_2207550).sum := by decide
  have hdescent : baseEnd_2207550 < baseStart_2207550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207625 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 1, 4]
def baseStart_2207625 : Nat := 118140960795 + 2207625 * 2 ^ 59
def prefixEnd_2207625 : Nat := 4983230072969 + 3 ^ 40 * 2207625 * 2
def baseEnd_2207625 : Nat := 755715153254686927156549

theorem tailTrace_2207625 : CollatzResearch.WordTrace tailWord_2207625 prefixEnd_2207625 755715153254686927156549 := by
  unfold tailWord_2207625
  simp only [CollatzResearch.WordTrace]
  refine ⟨80518698627159132178032329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53679132418106088118688219 80518698627159132178032329)
  ·
    refine ⟨60389023970369349133524247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80518698627159132178032329 60389023970369349133524247)
    ·
      refine ⟨90583535955554023700286371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60389023970369349133524247 90583535955554023700286371)
      ·
        refine ⟨135875303933331035550429557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90583535955554023700286371 135875303933331035550429557)
        ·
          refine ⟨12738309743749784582852771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135875303933331035550429557 12738309743749784582852771)
          ·
            refine ⟨19107464615624676874279157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12738309743749784582852771 19107464615624676874279157)
            ·
              refine ⟨1791324807714813456963671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19107464615624676874279157 1791324807714813456963671)
              ·
                refine ⟨2686987211572220185445507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791324807714813456963671 2686987211572220185445507)
                ·
                  refine ⟨4030480817358330278168261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686987211572220185445507 4030480817358330278168261)
                  ·
                    refine ⟨755715153254686927156549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4030480817358330278168261 755715153254686927156549)
                    ·
                      rfl

theorem cell22_2207625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 4].length) (baseStart_2207625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207625 prefixEnd_2207625 := by exact prefixLift 2207625
  have htrace : WordTrace (prefixWord ++ tailWord_2207625) baseStart_2207625 baseEnd_2207625 := by
    simpa [prefixWord, tailWord_2207625, baseEnd_2207625] using wordTrace_append hprefix tailTrace_2207625
  have hstable : (prefixWord ++ tailWord_2207625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207625).length < 2 ^ (prefixWord ++ tailWord_2207625).sum := by decide
  have hdescent : baseEnd_2207625 < baseStart_2207625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207655 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2207655 : Nat := 118140960795 + 2207655 * 2 ^ 59
def prefixEnd_2207655 : Nat := 4983230072969 + 3 ^ 40 * 2207655 * 2
def baseEnd_2207655 : Nat := 755725422867776848906457

theorem tailTrace_2207655 : CollatzResearch.WordTrace tailWord_2207655 prefixEnd_2207655 755725422867776848906457 := by
  unfold tailWord_2207655
  simp only [CollatzResearch.WordTrace]
  refine ⟨80519792817050447301624419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53679861878033631534416279 80519792817050447301624419)
  ·
    refine ⟨120779689225575670952436629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80519792817050447301624419 120779689225575670952436629)
    ·
      refine ⟨5661547932448859575895467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120779689225575670952436629 5661547932448859575895467)
      ·
        refine ⟨8492321898673289363843201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5661547932448859575895467 8492321898673289363843201)
        ·
          refine ⟨6369241424004967022882401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8492321898673289363843201 6369241424004967022882401)
          ·
            refine ⟨4776931068003725267161801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6369241424004967022882401 4776931068003725267161801)
            ·
              refine ⟨3582698301002793950371351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4776931068003725267161801 3582698301002793950371351)
              ·
                refine ⟨5374047451504190925557027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582698301002793950371351 5374047451504190925557027)
                ·
                  refine ⟨8061071177256286388335541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5374047451504190925557027 8061071177256286388335541)
                  ·
                    refine ⟨755725422867776848906457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8061071177256286388335541 755725422867776848906457)
                    ·
                      rfl

theorem cell22_2207655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2207655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207655 prefixEnd_2207655 := by exact prefixLift 2207655
  have htrace : WordTrace (prefixWord ++ tailWord_2207655) baseStart_2207655 baseEnd_2207655 := by
    simpa [prefixWord, tailWord_2207655, baseEnd_2207655] using wordTrace_append hprefix tailTrace_2207655
  have hstable : (prefixWord ++ tailWord_2207655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207655).length < 2 ^ (prefixWord ++ tailWord_2207655).sum := by decide
  have hdescent : baseEnd_2207655 < baseStart_2207655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207676 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_2207676 : Nat := 118140960795 + 2207676 * 2 ^ 59
def prefixEnd_2207676 : Nat := 4983230072969 + 3 ^ 40 * 2207676 * 2
def baseEnd_2207676 : Nat := 755732611596939794131393

theorem tailTrace_2207676 : CollatzResearch.WordTrace tailWord_2207676 prefixEnd_2207676 755732611596939794131393 := by
  unfold tailWord_2207676
  simp only [CollatzResearch.WordTrace]
  refine ⟨40260279374987183944069441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53680372499982911925425921 40260279374987183944069441)
  ·
    refine ⟨30195209531240387958052081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40260279374987183944069441 30195209531240387958052081)
    ·
      refine ⟨22646407148430290968539061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30195209531240387958052081 22646407148430290968539061)
      ·
        refine ⟨2123100670165339778300537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22646407148430290968539061 2123100670165339778300537)
        ·
          refine ⟨1592325502624004833725403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2123100670165339778300537 1592325502624004833725403)
          ·
            refine ⟨2388488253936007250588105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592325502624004833725403 2388488253936007250588105)
            ·
              refine ⟨1791366190452005437941079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388488253936007250588105 1791366190452005437941079)
              ·
                refine ⟨2687049285678008156911619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791366190452005437941079 2687049285678008156911619)
                ·
                  refine ⟨4030573928517012235367429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2687049285678008156911619 4030573928517012235367429)
                  ·
                    refine ⟨755732611596939794131393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4030573928517012235367429 755732611596939794131393)
                    ·
                      rfl

theorem cell22_2207676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_2207676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207676 prefixEnd_2207676 := by exact prefixLift 2207676
  have htrace : WordTrace (prefixWord ++ tailWord_2207676) baseStart_2207676 baseEnd_2207676 := by
    simpa [prefixWord, tailWord_2207676, baseEnd_2207676] using wordTrace_append hprefix tailTrace_2207676
  have hstable : (prefixWord ++ tailWord_2207676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207676).length < 2 ^ (prefixWord ++ tailWord_2207676).sum := by decide
  have hdescent : baseEnd_2207676 < baseStart_2207676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207713 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 5]
def baseStart_2207713 : Nat := 118140960795 + 2207713 * 2 ^ 59
def prefixEnd_2207713 : Nat := 4983230072969 + 3 ^ 40 * 2207713 * 2
def baseEnd_2207713 : Nat := 251915092484361343652093

theorem tailTrace_2207713 : CollatzResearch.WordTrace tailWord_2207713 prefixEnd_2207713 251915092484361343652093 := by
  unfold tailWord_2207713
  simp only [CollatzResearch.WordTrace]
  refine ⟨80521908250840323207235793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53681272167226882138157195 80521908250840323207235793)
  ·
    refine ⟨60391431188130242405426845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80521908250840323207235793 60391431188130242405426845)
    ·
      refine ⟨22646786695548840902035067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60391431188130242405426845 22646786695548840902035067)
      ·
        refine ⟨33970180043323261353052601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22646786695548840902035067 33970180043323261353052601)
        ·
          refine ⟨25477635032492446014789451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33970180043323261353052601 25477635032492446014789451)
          ·
            refine ⟨38216452548738669022184177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25477635032492446014789451 38216452548738669022184177)
            ·
              refine ⟨28662339411554001766638133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38216452548738669022184177 28662339411554001766638133)
              ·
                refine ⟨2687094319833187665622325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28662339411554001766638133 2687094319833187665622325)
                ·
                  refine ⟨251915092484361343652093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2687094319833187665622325 251915092484361343652093)
                  ·
                    rfl

theorem cell22_2207713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_2207713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207713 prefixEnd_2207713 := by exact prefixLift 2207713
  have htrace : WordTrace (prefixWord ++ tailWord_2207713) baseStart_2207713 baseEnd_2207713 := by
    simpa [prefixWord, tailWord_2207713, baseEnd_2207713] using wordTrace_append hprefix tailTrace_2207713
  have hstable : (prefixWord ++ tailWord_2207713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207713).length < 2 ^ (prefixWord ++ tailWord_2207713).sum := by decide
  have hdescent : baseEnd_2207713 < baseStart_2207713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207764 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 5]
def baseStart_2207764 : Nat := 118140960795 + 2207764 * 2 ^ 59
def prefixEnd_2207764 : Nat := 4983230072969 + 3 ^ 40 * 2207764 * 2
def baseEnd_2207764 : Nat := 251920911931778965977041

theorem tailTrace_2207764 : CollatzResearch.WordTrace tailWord_2207764 prefixEnd_2207764 251920911931778965977041 := by
  unfold tailWord_2207764
  simp only [CollatzResearch.WordTrace]
  refine ⟨40261884186827779458671173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53682512249103705944894897 40261884186827779458671173)
  ·
    refine ⟨7549103285030208648500845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40261884186827779458671173 7549103285030208648500845)
    ·
      refine ⟨2830913731886328243187817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7549103285030208648500845 2830913731886328243187817)
      ·
        refine ⟨2123185298914746182390863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2830913731886328243187817 2123185298914746182390863)
        ·
          refine ⟨3184777948372119273586295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123185298914746182390863 3184777948372119273586295)
          ·
            refine ⟨4777166922558178910379443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184777948372119273586295 4777166922558178910379443)
            ·
              refine ⟨7165750383837268365569165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777166922558178910379443 7165750383837268365569165)
              ·
                refine ⟨2687156393938975637088437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7165750383837268365569165 2687156393938975637088437)
                ·
                  refine ⟨251920911931778965977041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2687156393938975637088437 251920911931778965977041)
                  ·
                    rfl

theorem cell22_2207764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_2207764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207764 prefixEnd_2207764 := by exact prefixLift 2207764
  have htrace : WordTrace (prefixWord ++ tailWord_2207764) baseStart_2207764 baseEnd_2207764 := by
    simpa [prefixWord, tailWord_2207764, baseEnd_2207764] using wordTrace_append hprefix tailTrace_2207764
  have hstable : (prefixWord ++ tailWord_2207764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207764).length < 2 ^ (prefixWord ++ tailWord_2207764).sum := by decide
  have hdescent : baseEnd_2207764 < baseStart_2207764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207790 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2207790 : Nat := 118140960795 + 2207790 * 2 ^ 59
def prefixEnd_2207790 : Nat := 4983230072969 + 3 ^ 40 * 2207790 * 2
def baseEnd_2207790 : Nat := 755771636126681496781043

theorem tailTrace_2207790 : CollatzResearch.WordTrace tailWord_2207790 prefixEnd_2207790 755771636126681496781043 := by
  unfold tailWord_2207790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10065589583945170669723603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53683144447707576905192549 10065589583945170669723603)
  ·
    refine ⟨15098384375917756004585405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10065589583945170669723603 15098384375917756004585405)
    ·
      refine ⟨5661894140969158501719527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15098384375917756004585405 5661894140969158501719527)
      ·
        refine ⟨8492841211453737752579291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5661894140969158501719527 8492841211453737752579291)
        ·
          refine ⟨12739261817180606628868937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8492841211453737752579291 12739261817180606628868937)
          ·
            refine ⟨9554446362885454971651703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12739261817180606628868937 9554446362885454971651703)
            ·
              refine ⟨14331669544328182457477555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9554446362885454971651703 14331669544328182457477555)
              ·
                refine ⟨21497504316492273686216333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14331669544328182457477555 21497504316492273686216333)
                ·
                  refine ⟨8061564118684602632331125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21497504316492273686216333 8061564118684602632331125)
                  ·
                    refine ⟨755771636126681496781043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8061564118684602632331125 755771636126681496781043)
                    ·
                      rfl

theorem cell22_2207790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2207790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207790 prefixEnd_2207790 := by exact prefixLift 2207790
  have htrace : WordTrace (prefixWord ++ tailWord_2207790) baseStart_2207790 baseEnd_2207790 := by
    simpa [prefixWord, tailWord_2207790, baseEnd_2207790] using wordTrace_append hprefix tailTrace_2207790
  have hstable : (prefixWord ++ tailWord_2207790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207790).length < 2 ^ (prefixWord ++ tailWord_2207790).sum := by decide
  have hdescent : baseEnd_2207790 < baseStart_2207790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207805 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_2207805 : Nat := 118140960795 + 2207805 * 2 ^ 59
def prefixEnd_2207805 : Nat := 4983230072969 + 3 ^ 40 * 2207805 * 2
def baseEnd_2207805 : Nat := 755776770933226457655997

theorem tailTrace_2207805 : CollatzResearch.WordTrace tailWord_2207805 prefixEnd_2207805 755776770933226457655997 := by
  unfold tailWord_2207805
  simp only [CollatzResearch.WordTrace]
  refine ⟨80525263766507022919584869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53683509177671348613056579 80525263766507022919584869)
  ·
    refine ⟨15098486956220066797422163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80525263766507022919584869 15098486956220066797422163)
    ·
      refine ⟨22647730434330100196133245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15098486956220066797422163 22647730434330100196133245)
      ·
        refine ⟨8492898912873787573549967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22647730434330100196133245 8492898912873787573549967)
        ·
          refine ⟨12739348369310681360324951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8492898912873787573549967 12739348369310681360324951)
          ·
            refine ⟨19109022553966022040487427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12739348369310681360324951 19109022553966022040487427)
            ·
              refine ⟨28663533830949033060731141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19109022553966022040487427 28663533830949033060731141)
              ·
                refine ⟨5374412593302943698887089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28663533830949033060731141 5374412593302943698887089)
                ·
                  refine ⟨4030809444977207774165317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5374412593302943698887089 4030809444977207774165317)
                  ·
                    refine ⟨755776770933226457655997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4030809444977207774165317 755776770933226457655997)
                    ·
                      rfl

theorem cell22_2207805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_2207805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207805 prefixEnd_2207805 := by exact prefixLift 2207805
  have htrace : WordTrace (prefixWord ++ tailWord_2207805) baseStart_2207805 baseEnd_2207805 := by
    simpa [prefixWord, tailWord_2207805, baseEnd_2207805] using wordTrace_append hprefix tailTrace_2207805
  have hstable : (prefixWord ++ tailWord_2207805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207805).length < 2 ^ (prefixWord ++ tailWord_2207805).sum := by decide
  have hdescent : baseEnd_2207805 < baseStart_2207805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207809 : List Nat := [1, 2, 5, 1, 2, 1, 4, 2, 4]
def baseStart_2207809 : Nat := 118140960795 + 2207809 * 2 ^ 59
def prefixEnd_2207809 : Nat := 4983230072969 + 3 ^ 40 * 2207809 * 2
def baseEnd_2207809 : Nat := 251926046738323926851995

theorem tailTrace_2207809 : CollatzResearch.WordTrace tailWord_2207809 prefixEnd_2207809 251926046738323926851995 := by
  unfold tailWord_2207809
  simp only [CollatzResearch.WordTrace]
  refine ⟨80525409658492531602730481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53683606438995021068486987 80525409658492531602730481)
  ·
    refine ⟨60394057243869398702047861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80525409658492531602730481 60394057243869398702047861)
    ·
      refine ⟨5661942866612756128316987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60394057243869398702047861 5661942866612756128316987)
      ·
        refine ⟨8492914299919134192475481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5661942866612756128316987 8492914299919134192475481)
        ·
          refine ⟨6369685724939350644356611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8492914299919134192475481 6369685724939350644356611)
          ·
            refine ⟨9554528587409025966534917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6369685724939350644356611 9554528587409025966534917)
            ·
              refine ⟨1791474110139192368725297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9554528587409025966534917 1791474110139192368725297)
              ·
                refine ⟨1343605582604394276543973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791474110139192368725297 1343605582604394276543973)
                ·
                  refine ⟨251926046738323926851995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343605582604394276543973 251926046738323926851995)
                  ·
                    rfl

theorem cell22_2207809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 4].length) (baseStart_2207809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207809 prefixEnd_2207809 := by exact prefixLift 2207809
  have htrace : WordTrace (prefixWord ++ tailWord_2207809) baseStart_2207809 baseEnd_2207809 := by
    simpa [prefixWord, tailWord_2207809, baseEnd_2207809] using wordTrace_append hprefix tailTrace_2207809
  have hstable : (prefixWord ++ tailWord_2207809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207809).length < 2 ^ (prefixWord ++ tailWord_2207809).sum := by decide
  have hdescent : baseEnd_2207809 < baseStart_2207809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207818 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_2207818 : Nat := 118140960795 + 2207818 * 2 ^ 59
def prefixEnd_2207818 : Nat := 4983230072969 + 3 ^ 40 * 2207818 * 2
def baseEnd_2207818 : Nat := 755781221098898757080957

theorem tailTrace_2207818 : CollatzResearch.WordTrace tailWord_2207818 prefixEnd_2207818 755781221098898757080957 := by
  unfold tailWord_2207818
  simp only [CollatzResearch.WordTrace]
  refine ⟨20131434478864981534952027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53683825276973284093205405 20131434478864981534952027)
  ·
    refine ⟨30197151718297472302428041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20131434478864981534952027 30197151718297472302428041)
    ·
      refine ⟨22647863788723104226821031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30197151718297472302428041 22647863788723104226821031)
      ·
        refine ⟨33971795683084656340231547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22647863788723104226821031 33971795683084656340231547)
        ·
          refine ⟨50957693524626984510347321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33971795683084656340231547 50957693524626984510347321)
          ·
            refine ⟨38218270143470238382760491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50957693524626984510347321 38218270143470238382760491)
            ·
              refine ⟨57327405215205357574140737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38218270143470238382760491 57327405215205357574140737)
              ·
                refine ⟨42995553911404018180605553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57327405215205357574140737 42995553911404018180605553)
                ·
                  refine ⟨32246665433553013635454165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42995553911404018180605553 32246665433553013635454165)
                  ·
                    refine ⟨755781221098898757080957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32246665433553013635454165 755781221098898757080957)
                    ·
                      rfl

theorem cell22_2207818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_2207818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207818 prefixEnd_2207818 := by exact prefixLift 2207818
  have htrace : WordTrace (prefixWord ++ tailWord_2207818) baseStart_2207818 baseEnd_2207818 := by
    simpa [prefixWord, tailWord_2207818, baseEnd_2207818] using wordTrace_append hprefix tailTrace_2207818
  have hstable : (prefixWord ++ tailWord_2207818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207818).length < 2 ^ (prefixWord ++ tailWord_2207818).sum := by decide
  have hdescent : baseEnd_2207818 < baseStart_2207818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207833 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_2207833 : Nat := 118140960795 + 2207833 * 2 ^ 59
def prefixEnd_2207833 : Nat := 4983230072969 + 3 ^ 40 * 2207833 * 2
def baseEnd_2207833 : Nat := 755786355905443717955911

theorem tailTrace_2207833 : CollatzResearch.WordTrace tailWord_2207833 prefixEnd_2207833 755786355905443717955911 := by
  unfold tailWord_2207833
  simp only [CollatzResearch.WordTrace]
  refine ⟨80526285010405583701604153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53684190006937055801069435 80526285010405583701604153)
  ·
    refine ⟨60394713757804187776203115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80526285010405583701604153 60394713757804187776203115)
    ·
      refine ⟨90592070636706281664304673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60394713757804187776203115 90592070636706281664304673)
      ·
        refine ⟨67944052977529711248228505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90592070636706281664304673 67944052977529711248228505)
        ·
          refine ⟨50958039733147283436171379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67944052977529711248228505 50958039733147283436171379)
          ·
            refine ⟨76437059599720925154257069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50958039733147283436171379 76437059599720925154257069)
            ·
              refine ⟨28663897349895346932846401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76437059599720925154257069 28663897349895346932846401)
              ·
                refine ⟨21497923012421510199634801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28663897349895346932846401 21497923012421510199634801)
                ·
                  refine ⟨16123442259316132649726101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21497923012421510199634801 16123442259316132649726101)
                  ·
                    refine ⟨755786355905443717955911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16123442259316132649726101 755786355905443717955911)
                    ·
                      rfl

theorem cell22_2207833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_2207833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207833 prefixEnd_2207833 := by exact prefixLift 2207833
  have htrace : WordTrace (prefixWord ++ tailWord_2207833) baseStart_2207833 baseEnd_2207833 := by
    simpa [prefixWord, tailWord_2207833, baseEnd_2207833] using wordTrace_append hprefix tailTrace_2207833
  have hstable : (prefixWord ++ tailWord_2207833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207833).length < 2 ^ (prefixWord ++ tailWord_2207833).sum := by decide
  have hdescent : baseEnd_2207833 < baseStart_2207833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207865 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 7]
def baseStart_2207865 : Nat := 118140960795 + 2207865 * 2 ^ 59
def prefixEnd_2207865 : Nat := 4983230072969 + 3 ^ 40 * 2207865 * 2
def baseEnd_2207865 : Nat := 251932436719802100385271

theorem tailTrace_2207865 : CollatzResearch.WordTrace tailWord_2207865 prefixEnd_2207865 251932436719802100385271 := by
  unfold tailWord_2207865
  simp only [CollatzResearch.WordTrace]
  refine ⟨80527452146289653166769049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53684968097526435444512699 80527452146289653166769049)
  ·
    refine ⟨60395589109717239875076787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80527452146289653166769049 60395589109717239875076787)
    ·
      refine ⟨90593383664575859812615181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60395589109717239875076787 90593383664575859812615181)
      ·
        refine ⟨33972518874215947429730693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90593383664575859812615181 33972518874215947429730693)
        ·
          refine ⟨6369847288915490143074505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33972518874215947429730693 6369847288915490143074505)
          ·
            refine ⟨4777385466686617607305879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6369847288915490143074505 4777385466686617607305879)
            ·
              refine ⟨7166078200029926410958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777385466686617607305879 7166078200029926410958819)
              ·
                refine ⟨10749117300044889616438229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7166078200029926410958819 10749117300044889616438229)
                ·
                  refine ⟨251932436719802100385271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10749117300044889616438229 251932436719802100385271)
                  ·
                    rfl

theorem cell22_2207865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_2207865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207865 prefixEnd_2207865 := by exact prefixLift 2207865
  have htrace : WordTrace (prefixWord ++ tailWord_2207865) baseStart_2207865 baseEnd_2207865 := by
    simpa [prefixWord, tailWord_2207865, baseEnd_2207865] using wordTrace_append hprefix tailTrace_2207865
  have hstable : (prefixWord ++ tailWord_2207865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207865).length < 2 ^ (prefixWord ++ tailWord_2207865).sum := by decide
  have hdescent : baseEnd_2207865 < baseStart_2207865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207869 : List Nat := [1, 4, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_2207869 : Nat := 118140960795 + 2207869 * 2 ^ 59
def prefixEnd_2207869 : Nat := 4983230072969 + 3 ^ 40 * 2207869 * 2
def baseEnd_2207869 : Nat := 755798679441151624055801

theorem tailTrace_2207869 : CollatzResearch.WordTrace tailWord_2207869 prefixEnd_2207869 755798679441151624055801 := by
  unfold tailWord_2207869
  simp only [CollatzResearch.WordTrace]
  refine ⟨80527598038275161849914661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53685065358850107899943107 80527598038275161849914661)
  ·
    refine ⟨15098924632176592846858999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80527598038275161849914661 15098924632176592846858999)
    ·
      refine ⟨22648386948264889270288499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15098924632176592846858999 22648386948264889270288499)
      ·
        refine ⟨33972580422397333905432749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22648386948264889270288499 33972580422397333905432749)
        ·
          refine ⟨12739717658399000214537281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33972580422397333905432749 12739717658399000214537281)
          ·
            refine ⟨9554788243799250160902961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12739717658399000214537281 9554788243799250160902961)
            ·
              refine ⟨7166091182849437620677221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9554788243799250160902961 7166091182849437620677221)
              ·
                refine ⟨1343642096784269553876979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7166091182849437620677221 1343642096784269553876979)
                ·
                  refine ⟨2015463145176404330815469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343642096784269553876979 2015463145176404330815469)
                  ·
                    refine ⟨755798679441151624055801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2015463145176404330815469 755798679441151624055801)
                    ·
                      rfl

theorem cell22_2207869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_2207869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207869 prefixEnd_2207869 := by exact prefixLift 2207869
  have htrace : WordTrace (prefixWord ++ tailWord_2207869) baseStart_2207869 baseEnd_2207869 := by
    simpa [prefixWord, tailWord_2207869, baseEnd_2207869] using wordTrace_append hprefix tailTrace_2207869
  have hstable : (prefixWord ++ tailWord_2207869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207869).length < 2 ^ (prefixWord ++ tailWord_2207869).sum := by decide
  have hdescent : baseEnd_2207869 < baseStart_2207869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207927 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 6]
def baseStart_2207927 : Nat := 118140960795 + 2207927 * 2 ^ 59
def prefixEnd_2207927 : Nat := 4983230072969 + 3 ^ 40 * 2207927 * 2
def baseEnd_2207927 : Nat := 251939511342152935368541

theorem tailTrace_2207927 : CollatzResearch.WordTrace tailWord_2207927 prefixEnd_2207927 251939511342152935368541 := by
  unfold tailWord_2207927
  simp only [CollatzResearch.WordTrace]
  refine ⟨80529713472065037755526035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53686475648043358503684023 80529713472065037755526035)
  ·
    refine ⟨120794570208097556633289053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80529713472065037755526035 120794570208097556633289053)
    ·
      refine ⟨45297963828036583737483395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120794570208097556633289053 45297963828036583737483395)
      ·
        refine ⟨67946945742054875606225093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45297963828036583737483395 67946945742054875606225093)
        ·
          refine ⟨12740052326635289176167205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67946945742054875606225093 12740052326635289176167205)
          ·
            refine ⟨2388759811244116720531351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12740052326635289176167205 2388759811244116720531351)
            ·
              refine ⟨3583139716866175080797027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388759811244116720531351 3583139716866175080797027)
              ·
                refine ⟨5374709575299262621195541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3583139716866175080797027 5374709575299262621195541)
                ·
                  refine ⟨251939511342152935368541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5374709575299262621195541 251939511342152935368541)
                  ·
                    rfl

theorem cell22_2207927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 6].length) (baseStart_2207927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207927 prefixEnd_2207927 := by exact prefixLift 2207927
  have htrace : WordTrace (prefixWord ++ tailWord_2207927) baseStart_2207927 baseEnd_2207927 := by
    simpa [prefixWord, tailWord_2207927, baseEnd_2207927] using wordTrace_append hprefix tailTrace_2207927
  have hstable : (prefixWord ++ tailWord_2207927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207927).length < 2 ^ (prefixWord ++ tailWord_2207927).sum := by decide
  have hdescent : baseEnd_2207927 < baseStart_2207927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207985 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_2207985 : Nat := 118140960795 + 2207985 * 2 ^ 59
def prefixEnd_2207985 : Nat := 4983230072969 + 3 ^ 40 * 2207985 * 2
def baseEnd_2207985 : Nat := 755838388611765988155445

theorem tailTrace_2207985 : CollatzResearch.WordTrace tailWord_2207985 prefixEnd_2207985 755838388611765988155445 := by
  unfold tailWord_2207985
  simp only [CollatzResearch.WordTrace]
  refine ⟨80531828905854913661137409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53687885937236609107424939 80531828905854913661137409)
  ·
    refine ⟨60398871679391185245853057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80531828905854913661137409 60398871679391185245853057)
    ·
      refine ⟨45299153759543388934389793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60398871679391185245853057 45299153759543388934389793)
      ·
        refine ⟨33974365319657541700792345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45299153759543388934389793 33974365319657541700792345)
        ·
          refine ⟨25480773989743156275594259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33974365319657541700792345 25480773989743156275594259)
          ·
            refine ⟨38221160984614734413391389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25480773989743156275594259 38221160984614734413391389)
            ·
              refine ⟨14332935369230525405021771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38221160984614734413391389 14332935369230525405021771)
              ·
                refine ⟨21499403053845788107532657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14332935369230525405021771 21499403053845788107532657)
                ·
                  refine ⟨16124552290384341080649493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21499403053845788107532657 16124552290384341080649493)
                  ·
                    refine ⟨755838388611765988155445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16124552290384341080649493 755838388611765988155445)
                    ·
                      rfl

theorem cell22_2207985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_2207985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207985 prefixEnd_2207985 := by exact prefixLift 2207985
  have htrace : WordTrace (prefixWord ++ tailWord_2207985) baseStart_2207985 baseEnd_2207985 := by
    simpa [prefixWord, tailWord_2207985, baseEnd_2207985] using wordTrace_append hprefix tailTrace_2207985
  have hstable : (prefixWord ++ tailWord_2207985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207985).length < 2 ^ (prefixWord ++ tailWord_2207985).sum := by decide
  have hdescent : baseEnd_2207985 < baseStart_2207985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2207987 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 3, 3]
def baseStart_2207987 : Nat := 118140960795 + 2207987 * 2 ^ 59
def prefixEnd_2207987 : Nat := 4983230072969 + 3 ^ 40 * 2207987 * 2
def baseEnd_2207987 : Nat := 755839073252638649605439

theorem tailTrace_2207987 : CollatzResearch.WordTrace tailWord_2207987 prefixEnd_2207987 755839073252638649605439 := by
  unfold tailWord_2207987
  simp only [CollatzResearch.WordTrace]
  refine ⟨80531901851847668002710215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53687934567898445335140143 80531901851847668002710215)
  ·
    refine ⟨120797852777771502004065323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80531901851847668002710215 120797852777771502004065323)
    ·
      refine ⟨181196779166657253006097985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120797852777771502004065323 181196779166657253006097985)
      ·
        refine ⟨135897584374992939754573489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181196779166657253006097985 135897584374992939754573489)
        ·
          refine ⟨101923188281244704815930117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135897584374992939754573489 101923188281244704815930117)
          ·
            refine ⟨19110597802733382152986897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101923188281244704815930117 19110597802733382152986897)
            ·
              refine ⟨14332948352050036614740173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19110597802733382152986897 14332948352050036614740173)
              ·
                refine ⟨5374855632018763730527565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14332948352050036614740173 5374855632018763730527565)
                ·
                  refine ⟨2015570862007036398947837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5374855632018763730527565 2015570862007036398947837)
                  ·
                    refine ⟨755839073252638649605439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2015570862007036398947837 755839073252638649605439)
                    ·
                      rfl

theorem cell22_2207987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 3].length) (baseStart_2207987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2207987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2207987 prefixEnd_2207987 := by exact prefixLift 2207987
  have htrace : WordTrace (prefixWord ++ tailWord_2207987) baseStart_2207987 baseEnd_2207987 := by
    simpa [prefixWord, tailWord_2207987, baseEnd_2207987] using wordTrace_append hprefix tailTrace_2207987
  have hstable : (prefixWord ++ tailWord_2207987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2207987).length < 2 ^ (prefixWord ++ tailWord_2207987).sum := by decide
  have hdescent : baseEnd_2207987 < baseStart_2207987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2207987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208032 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_2208032 : Nat := 118140960795 + 2208032 * 2 ^ 59
def prefixEnd_2208032 : Nat := 4983230072969 + 3 ^ 40 * 2208032 * 2
def baseEnd_2208032 : Nat := 755854477672273532230301

theorem tailTrace_2208032 : CollatzResearch.WordTrace tailWord_2208032 prefixEnd_2208032 755854477672273532230301 := by
  unfold tailWord_2208032
  simp only [CollatzResearch.WordTrace]
  refine ⟨40266771568342320344049175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53689028757789760458732233 40266771568342320344049175)
  ·
    refine ⟨60400157352513480516073763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40266771568342320344049175 60400157352513480516073763)
    ·
      refine ⟨90600236028770220774110645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60400157352513480516073763 90600236028770220774110645)
      ·
        refine ⟨8493772127697208197572873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90600236028770220774110645 8493772127697208197572873)
        ·
          refine ⟨6370329095772906148179655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8493772127697208197572873 6370329095772906148179655)
          ·
            refine ⟨9555493643659359222269483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6370329095772906148179655 9555493643659359222269483)
            ·
              refine ⟨14333240465489038833404225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9555493643659359222269483 14333240465489038833404225)
              ·
                refine ⟨10749930349116779125053169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14333240465489038833404225 10749930349116779125053169)
                ·
                  refine ⟨8062447761837584343789877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10749930349116779125053169 8062447761837584343789877)
                  ·
                    refine ⟨755854477672273532230301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8062447761837584343789877 755854477672273532230301)
                    ·
                      rfl

theorem cell22_2208032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_2208032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208032 prefixEnd_2208032 := by exact prefixLift 2208032
  have htrace : WordTrace (prefixWord ++ tailWord_2208032) baseStart_2208032 baseEnd_2208032 := by
    simpa [prefixWord, tailWord_2208032, baseEnd_2208032] using wordTrace_append hprefix tailTrace_2208032
  have hstable : (prefixWord ++ tailWord_2208032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208032).length < 2 ^ (prefixWord ++ tailWord_2208032).sum := by decide
  have hdescent : baseEnd_2208032 < baseStart_2208032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208034 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_2208034 : Nat := 118140960795 + 2208034 * 2 ^ 59
def prefixEnd_2208034 : Nat := 4983230072969 + 3 ^ 40 * 2208034 * 2
def baseEnd_2208034 : Nat := 251951720771048731226765

theorem tailTrace_2208034 : CollatzResearch.WordTrace tailWord_2208034 prefixEnd_2208034 251951720771048731226765 := by
  unfold tailWord_2208034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20133404020669348757417789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53689077388451596686447437 20133404020669348757417789)
  ·
    refine ⟨7550026507751005784031671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20133404020669348757417789 7550026507751005784031671)
    ·
      refine ⟨11325039761626508676047507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7550026507751005784031671 11325039761626508676047507)
      ·
        refine ⟨16987559642439763014071261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11325039761626508676047507 16987559642439763014071261)
        ·
          refine ⟨6370334865914911130276723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16987559642439763014071261 6370334865914911130276723)
          ·
            refine ⟨9555502298872366695415085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6370334865914911130276723 9555502298872366695415085)
            ·
              refine ⟨3583313362077137510780657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9555502298872366695415085 3583313362077137510780657)
              ·
                refine ⟨2687485021557853133085493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3583313362077137510780657 2687485021557853133085493)
                ·
                  refine ⟨251951720771048731226765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2687485021557853133085493 251951720771048731226765)
                  ·
                    rfl

theorem cell22_2208034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_2208034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208034 prefixEnd_2208034 := by exact prefixLift 2208034
  have htrace : WordTrace (prefixWord ++ tailWord_2208034) baseStart_2208034 baseEnd_2208034 := by
    simpa [prefixWord, tailWord_2208034, baseEnd_2208034] using wordTrace_append hprefix tailTrace_2208034
  have hstable : (prefixWord ++ tailWord_2208034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208034).length < 2 ^ (prefixWord ++ tailWord_2208034).sum := by decide
  have hdescent : baseEnd_2208034 < baseStart_2208034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208096 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 6]
def baseStart_2208096 : Nat := 118140960795 + 2208096 * 2 ^ 59
def prefixEnd_2208096 : Nat := 4983230072969 + 3 ^ 40 * 2208096 * 2
def baseEnd_2208096 : Nat := 251958795393399566210035

theorem tailTrace_2208096 : CollatzResearch.WordTrace tailWord_2208096 prefixEnd_2208096 251958795393399566210035 := by
  unfold tailWord_2208096
  simp only [CollatzResearch.WordTrace]
  refine ⟨40267938704226389809214071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53690584938968519745618761 40267938704226389809214071)
  ·
    refine ⟨60401908056339584713821107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40267938704226389809214071 60401908056339584713821107)
    ·
      refine ⟨90602862084509377070731661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60401908056339584713821107 90602862084509377070731661)
      ·
        refine ⟨33976073281691016401524373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90602862084509377070731661 33976073281691016401524373)
        ·
          refine ⟨1592628435079266393821455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33976073281691016401524373 1592628435079266393821455)
          ·
            refine ⟨2388942652618899590732183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592628435079266393821455 2388942652618899590732183)
            ·
              refine ⟨3583413978928349386098275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388942652618899590732183 3583413978928349386098275)
              ·
                refine ⟨5375120968392524079147413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3583413978928349386098275 5375120968392524079147413)
                ·
                  refine ⟨251958795393399566210035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5375120968392524079147413 251958795393399566210035)
                  ·
                    rfl

theorem cell22_2208096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_2208096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208096 prefixEnd_2208096 := by exact prefixLift 2208096
  have htrace : WordTrace (prefixWord ++ tailWord_2208096) baseStart_2208096 baseEnd_2208096 := by
    simpa [prefixWord, tailWord_2208096, baseEnd_2208096] using wordTrace_append hprefix tailTrace_2208096
  have hstable : (prefixWord ++ tailWord_2208096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208096).length < 2 ^ (prefixWord ++ tailWord_2208096).sum := by decide
  have hdescent : baseEnd_2208096 < baseStart_2208096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208173 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2208173 : Nat := 118140960795 + 2208173 * 2 ^ 59
def prefixEnd_2208173 : Nat := 4983230072969 + 3 ^ 40 * 2208173 * 2
def baseEnd_2208173 : Nat := 755902744853796164454869

theorem tailTrace_2208173 : CollatzResearch.WordTrace tailWord_2208173 prefixEnd_2208173 755902744853796164454869 := by
  unfold tailWord_2208173
  simp only [CollatzResearch.WordTrace]
  refine ⟨80538685829173821768981173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53692457219449214512654115 80538685829173821768981173)
  ·
    refine ⟨7550501796485045790841985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80538685829173821768981173 7550501796485045790841985)
    ·
      refine ⟨5662876347363784343131489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7550501796485045790841985 5662876347363784343131489)
      ·
        refine ⟨4247157260522838257348617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5662876347363784343131489 4247157260522838257348617)
        ·
          refine ⟨3185367945392128693011463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4247157260522838257348617 3185367945392128693011463)
          ·
            refine ⟨4778051918088193039517195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185367945392128693011463 4778051918088193039517195)
            ·
              refine ⟨7167077877132289559275793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778051918088193039517195 7167077877132289559275793)
              ·
                refine ⟨5375308407849217169456845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7167077877132289559275793 5375308407849217169456845)
                ·
                  refine ⟨2015740652943456438546317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5375308407849217169456845 2015740652943456438546317)
                  ·
                    refine ⟨755902744853796164454869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2015740652943456438546317 755902744853796164454869)
                    ·
                      rfl

theorem cell22_2208173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2208173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208173 prefixEnd_2208173 := by exact prefixLift 2208173
  have htrace : WordTrace (prefixWord ++ tailWord_2208173) baseStart_2208173 baseEnd_2208173 := by
    simpa [prefixWord, tailWord_2208173, baseEnd_2208173] using wordTrace_append hprefix tailTrace_2208173
  have hstable : (prefixWord ++ tailWord_2208173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208173).length < 2 ^ (prefixWord ++ tailWord_2208173).sum := by decide
  have hdescent : baseEnd_2208173 < baseStart_2208173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208246 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_2208246 : Nat := 118140960795 + 2208246 * 2 ^ 59
def prefixEnd_2208246 : Nat := 4983230072969 + 3 ^ 40 * 2208246 * 2
def baseEnd_2208246 : Nat := 755927734245648307379645

theorem tailTrace_2208246 : CollatzResearch.WordTrace tailWord_2208246 prefixEnd_2208246 755927734245648307379645 := by
  unfold tailWord_2208246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5033834272369334702274287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53694232238606236824259061 5033834272369334702274287)
  ·
    refine ⟨7550751408554002053411431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5033834272369334702274287 7550751408554002053411431)
    ·
      refine ⟨11326127112831003080117147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7550751408554002053411431 11326127112831003080117147)
      ·
        refine ⟨16989190669246504620175721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11326127112831003080117147 16989190669246504620175721)
        ·
          refine ⟨12741893001934878465131791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16989190669246504620175721 12741893001934878465131791)
          ·
            refine ⟨19112839502902317697697687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12741893001934878465131791 19112839502902317697697687)
            ·
              refine ⟨28669259254353476546546531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19112839502902317697697687 28669259254353476546546531)
              ·
                refine ⟨43003888881530214819819797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28669259254353476546546531 43003888881530214819819797)
                ·
                  refine ⟨2015807291321728819679053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43003888881530214819819797 2015807291321728819679053)
                  ·
                    refine ⟨755927734245648307379645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2015807291321728819679053 755927734245648307379645)
                    ·
                      rfl

theorem cell22_2208246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_2208246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208246 prefixEnd_2208246 := by exact prefixLift 2208246
  have htrace : WordTrace (prefixWord ++ tailWord_2208246) baseStart_2208246 baseEnd_2208246 := by
    simpa [prefixWord, tailWord_2208246, baseEnd_2208246] using wordTrace_append hprefix tailTrace_2208246
  have hstable : (prefixWord ++ tailWord_2208246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208246).length < 2 ^ (prefixWord ++ tailWord_2208246).sum := by decide
  have hdescent : baseEnd_2208246 < baseStart_2208246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208276 : List Nat := [2, 4, 3, 1, 1, 1, 1, 9]
def baseStart_2208276 : Nat := 118140960795 + 2208276 * 2 ^ 59
def prefixEnd_2208276 : Nat := 4983230072969 + 3 ^ 40 * 2208276 * 2
def baseEnd_2208276 : Nat := 83993111539859803236617

theorem tailTrace_2208276 : CollatzResearch.WordTrace tailWord_2208276 prefixEnd_2208276 83993111539859803236617 := by
  unfold tailWord_2208276
  simp only [CollatzResearch.WordTrace]
  refine ⟨40271221273900335179990341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53694961698533780239987121 40271221273900335179990341)
  ·
    refine ⟨7550853988856312846248189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40271221273900335179990341 7550853988856312846248189)
    ·
      refine ⟨2831570245821117317343071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7550853988856312846248189 2831570245821117317343071)
      ·
        refine ⟨4247355368731675976014607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831570245821117317343071 4247355368731675976014607)
        ·
          refine ⟨6371033053097513964021911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4247355368731675976014607 6371033053097513964021911)
          ·
            refine ⟨9556549579646270946032867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6371033053097513964021911 9556549579646270946032867)
            ·
              refine ⟨14334824369469406419049301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9556549579646270946032867 14334824369469406419049301)
              ·
                refine ⟨83993111539859803236617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14334824369469406419049301 83993111539859803236617)
                ·
                  rfl

theorem cell22_2208276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 9].length) (baseStart_2208276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208276 prefixEnd_2208276 := by exact prefixLift 2208276
  have htrace : WordTrace (prefixWord ++ tailWord_2208276) baseStart_2208276 baseEnd_2208276 := by
    simpa [prefixWord, tailWord_2208276, baseEnd_2208276] using wordTrace_append hprefix tailTrace_2208276
  have hstable : (prefixWord ++ tailWord_2208276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208276).length < 2 ^ (prefixWord ++ tailWord_2208276).sum := by decide
  have hdescent : baseEnd_2208276 < baseStart_2208276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208280 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 2, 3]
def baseStart_2208280 : Nat := 118140960795 + 2208280 * 2 ^ 59
def prefixEnd_2208280 : Nat := 4983230072969 + 3 ^ 40 * 2208280 * 2
def baseEnd_2208280 : Nat := 755939373140483552029541

theorem tailTrace_2208280 : CollatzResearch.WordTrace tailWord_2208280 prefixEnd_2208280 755939373140483552029541 := by
  unfold tailWord_2208280
  simp only [CollatzResearch.WordTrace]
  refine ⟨40271294219893089521563147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53695058959857452695417529 40271294219893089521563147)
  ·
    refine ⟨60406941329839634282344721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40271294219893089521563147 60406941329839634282344721)
    ·
      refine ⟨45305205997379725711758541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60406941329839634282344721 45305205997379725711758541)
      ·
        refine ⟨16989452249017397141909453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45305205997379725711758541 16989452249017397141909453)
        ·
          refine ⟨6371044593381523928216045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16989452249017397141909453 6371044593381523928216045)
          ·
            refine ⟨2389141722518071473081017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6371044593381523928216045 2389141722518071473081017)
            ·
              refine ⟨1791856291888553604810763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389141722518071473081017 1791856291888553604810763)
              ·
                refine ⟨2687784437832830407216145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791856291888553604810763 2687784437832830407216145)
                ·
                  refine ⟨2015838328374622805412109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2687784437832830407216145 2015838328374622805412109)
                  ·
                    refine ⟨755939373140483552029541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2015838328374622805412109 755939373140483552029541)
                    ·
                      rfl

theorem cell22_2208280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_2208280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208280 prefixEnd_2208280 := by exact prefixLift 2208280
  have htrace : WordTrace (prefixWord ++ tailWord_2208280) baseStart_2208280 baseEnd_2208280 := by
    simpa [prefixWord, tailWord_2208280, baseEnd_2208280] using wordTrace_append hprefix tailTrace_2208280
  have hstable : (prefixWord ++ tailWord_2208280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208280).length < 2 ^ (prefixWord ++ tailWord_2208280).sum := by decide
  have hdescent : baseEnd_2208280 < baseStart_2208280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208295 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2208295 : Nat := 118140960795 + 2208295 * 2 ^ 59
def prefixEnd_2208295 : Nat := 4983230072969 + 3 ^ 40 * 2208295 * 2
def baseEnd_2208295 : Nat := 755944507947028512904495

theorem tailTrace_2208295 : CollatzResearch.WordTrace tailWord_2208295 prefixEnd_2208295 755944507947028512904495 := by
  unfold tailWord_2208295
  simp only [CollatzResearch.WordTrace]
  refine ⟨80543135534731836604922339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53695423689821224403281559 80543135534731836604922339)
  ·
    refine ⟨120814703302097754907383509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80543135534731836604922339 120814703302097754907383509)
    ·
      refine ⟨2831594608642916130641801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 120814703302097754907383509 2831594608642916130641801)
      ·
        refine ⟨2123695956482187097981351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2831594608642916130641801 2123695956482187097981351)
        ·
          refine ⟨3185543934723280646972027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123695956482187097981351 3185543934723280646972027)
          ·
            refine ⟨4778315902084920970458041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185543934723280646972027 4778315902084920970458041)
            ·
              refine ⟨3583736926563690727843531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4778315902084920970458041 3583736926563690727843531)
              ·
                refine ⟨5375605389845536091765297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3583736926563690727843531 5375605389845536091765297)
                ·
                  refine ⟨4031704042384152068823973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5375605389845536091765297 4031704042384152068823973)
                  ·
                    refine ⟨755944507947028512904495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4031704042384152068823973 755944507947028512904495)
                    ·
                      rfl

theorem cell22_2208295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2208295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208295 prefixEnd_2208295 := by exact prefixLift 2208295
  have htrace : WordTrace (prefixWord ++ tailWord_2208295) baseStart_2208295 baseEnd_2208295 := by
    simpa [prefixWord, tailWord_2208295, baseEnd_2208295] using wordTrace_append hprefix tailTrace_2208295
  have hstable : (prefixWord ++ tailWord_2208295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208295).length < 2 ^ (prefixWord ++ tailWord_2208295).sum := by decide
  have hdescent : baseEnd_2208295 < baseStart_2208295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208319 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 2, 5]
def baseStart_2208319 : Nat := 118140960795 + 2208319 * 2 ^ 59
def prefixEnd_2208319 : Nat := 4983230072969 + 3 ^ 40 * 2208319 * 2
def baseEnd_2208319 : Nat := 755952723637500450304421

theorem tailTrace_2208319 : CollatzResearch.WordTrace tailWord_2208319 prefixEnd_2208319 755952723637500450304421 := by
  unfold tailWord_2208319
  simp only [CollatzResearch.WordTrace]
  refine ⟨80544010886644888703796011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53696007257763259135864007 80544010886644888703796011)
  ·
    refine ⟨120816016329967333055694017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80544010886644888703796011 120816016329967333055694017)
    ·
      refine ⟨90612012247475499791770513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120816016329967333055694017 90612012247475499791770513)
      ·
        refine ⟨67959009185606624843827885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90612012247475499791770513 67959009185606624843827885)
        ·
          refine ⟨25484628444602484316435457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67959009185606624843827885 25484628444602484316435457)
          ·
            refine ⟨19113471333451863237326593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25484628444602484316435457 19113471333451863237326593)
            ·
              refine ⟨14335103500088897427994945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19113471333451863237326593 14335103500088897427994945)
              ·
                refine ⟨10751327625066673070996209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14335103500088897427994945 10751327625066673070996209)
                ·
                  refine ⟨8063495718800004803247157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10751327625066673070996209 8063495718800004803247157)
                  ·
                    refine ⟨755952723637500450304421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8063495718800004803247157 755952723637500450304421)
                    ·
                      rfl

theorem cell22_2208319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_2208319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208319 prefixEnd_2208319 := by exact prefixLift 2208319
  have htrace : WordTrace (prefixWord ++ tailWord_2208319) baseStart_2208319 baseEnd_2208319 := by
    simpa [prefixWord, tailWord_2208319, baseEnd_2208319] using wordTrace_append hprefix tailTrace_2208319
  have hstable : (prefixWord ++ tailWord_2208319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208319).length < 2 ^ (prefixWord ++ tailWord_2208319).sum := by decide
  have hdescent : baseEnd_2208319 < baseStart_2208319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208321 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 5]
def baseStart_2208321 : Nat := 118140960795 + 2208321 * 2 ^ 59
def prefixEnd_2208321 : Nat := 4983230072969 + 3 ^ 40 * 2208321 * 2
def baseEnd_2208321 : Nat := 251984469426124370584805

theorem tailTrace_2208321 : CollatzResearch.WordTrace tailWord_2208321 prefixEnd_2208321 251984469426124370584805 := by
  unfold tailWord_2208321
  simp only [CollatzResearch.WordTrace]
  refine ⟨80544083832637643045368817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53696055888425095363579211 80544083832637643045368817)
  ·
    refine ⟨60408062874478232284026613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80544083832637643045368817 60408062874478232284026613)
    ·
      refine ⟨5663255894482334276627495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60408062874478232284026613 5663255894482334276627495)
      ·
        refine ⟨8494883841723501414941243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5663255894482334276627495 8494883841723501414941243)
        ·
          refine ⟨12742325762585252122411865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8494883841723501414941243 12742325762585252122411865)
          ·
            refine ⟨9556744321938939091808899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12742325762585252122411865 9556744321938939091808899)
            ·
              refine ⟨14335116482908408637713349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9556744321938939091808899 14335116482908408637713349)
              ·
                refine ⟨2687834340545326619571253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14335116482908408637713349 2687834340545326619571253)
                ·
                  refine ⟨251984469426124370584805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2687834340545326619571253 251984469426124370584805)
                  ·
                    rfl

theorem cell22_2208321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_2208321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208321 prefixEnd_2208321 := by exact prefixLift 2208321
  have htrace : WordTrace (prefixWord ++ tailWord_2208321) baseStart_2208321 baseEnd_2208321 := by
    simpa [prefixWord, tailWord_2208321, baseEnd_2208321] using wordTrace_append hprefix tailTrace_2208321
  have hstable : (prefixWord ++ tailWord_2208321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208321).length < 2 ^ (prefixWord ++ tailWord_2208321).sum := by decide
  have hdescent : baseEnd_2208321 < baseStart_2208321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208325 : List Nat := [1, 3, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_2208325 : Nat := 118140960795 + 2208325 * 2 ^ 59
def prefixEnd_2208325 : Nat := 4983230072969 + 3 ^ 40 * 2208325 * 2
def baseEnd_2208325 : Nat := 755954777560118434654403

theorem tailTrace_2208325 : CollatzResearch.WordTrace tailWord_2208325 prefixEnd_2208325 755954777560118434654403 := by
  unfold tailWord_2208325
  simp only [CollatzResearch.WordTrace]
  refine ⟨80544229724623151728514429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53696153149748767819009619 80544229724623151728514429)
  ·
    refine ⟨30204086146733681898192911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80544229724623151728514429 30204086146733681898192911)
    ·
      refine ⟨45306129220100522847289367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30204086146733681898192911 45306129220100522847289367)
      ·
        refine ⟨67959193830150784270934051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45306129220100522847289367 67959193830150784270934051)
        ·
          refine ⟨101938790745226176406401077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67959193830150784270934051 101938790745226176406401077)
          ·
            refine ⟨9556761632364954038100101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101938790745226176406401077 9556761632364954038100101)
            ·
              refine ⟨1791892806068428882143769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9556761632364954038100101 1791892806068428882143769)
              ·
                refine ⟨1343919604551321661607827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791892806068428882143769 1343919604551321661607827)
                ·
                  refine ⟨2015879406826982492411741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343919604551321661607827 2015879406826982492411741)
                  ·
                    refine ⟨755954777560118434654403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2015879406826982492411741 755954777560118434654403)
                    ·
                      rfl

theorem cell22_2208325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_2208325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208325 prefixEnd_2208325 := by exact prefixLift 2208325
  have htrace : WordTrace (prefixWord ++ tailWord_2208325) baseStart_2208325 baseEnd_2208325 := by
    simpa [prefixWord, tailWord_2208325, baseEnd_2208325] using wordTrace_append hprefix tailTrace_2208325
  have hstable : (prefixWord ++ tailWord_2208325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208325).length < 2 ^ (prefixWord ++ tailWord_2208325).sum := by decide
  have hdescent : baseEnd_2208325 < baseStart_2208325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208368 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_2208368 : Nat := 118140960795 + 2208368 * 2 ^ 59
def prefixEnd_2208368 : Nat := 4983230072969 + 3 ^ 40 * 2208368 * 2
def baseEnd_2208368 : Nat := 755969497338880655829271

theorem tailTrace_2208368 : CollatzResearch.WordTrace tailWord_2208368 prefixEnd_2208368 755969497338880655829271 := by
  unfold tailWord_2208368
  simp only [CollatzResearch.WordTrace]
  refine ⟨40272899031733685036164879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53697198708978246714886505 40272899031733685036164879)
  ·
    refine ⟨60409348547600527554247319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40272899031733685036164879 60409348547600527554247319)
    ·
      refine ⟨90614022821400791331370979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60409348547600527554247319 90614022821400791331370979)
      ·
        refine ⟨135921034232101186997056469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90614022821400791331370979 135921034232101186997056469)
        ·
          refine ⟨3185649239814871570243511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 135921034232101186997056469 3185649239814871570243511)
          ·
            refine ⟨4778473859722307355365267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185649239814871570243511 4778473859722307355365267)
            ·
              refine ⟨7167710789583461033047901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778473859722307355365267 7167710789583461033047901)
              ·
                refine ⟨2687891546093797887392963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7167710789583461033047901 2687891546093797887392963)
                ·
                  refine ⟨4031837319140696831089445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2687891546093797887392963 4031837319140696831089445)
                  ·
                    refine ⟨755969497338880655829271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4031837319140696831089445 755969497338880655829271)
                    ·
                      rfl

theorem cell22_2208368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_2208368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208368 prefixEnd_2208368 := by exact prefixLift 2208368
  have htrace : WordTrace (prefixWord ++ tailWord_2208368) baseStart_2208368 baseEnd_2208368 := by
    simpa [prefixWord, tailWord_2208368, baseEnd_2208368] using wordTrace_append hprefix tailTrace_2208368
  have hstable : (prefixWord ++ tailWord_2208368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208368).length < 2 ^ (prefixWord ++ tailWord_2208368).sum := by decide
  have hdescent : baseEnd_2208368 < baseStart_2208368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208409 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_2208409 : Nat := 118140960795 + 2208409 * 2 ^ 59
def prefixEnd_2208409 : Nat := 4983230072969 + 3 ^ 40 * 2208409 * 2
def baseEnd_2208409 : Nat := 755983532476770215554145

theorem tailTrace_2208409 : CollatzResearch.WordTrace tailWord_2208409 prefixEnd_2208409 755983532476770215554145 := by
  unfold tailWord_2208409
  simp only [CollatzResearch.WordTrace]
  refine ⟨80547293456318834074572281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53698195637545889383048187 80547293456318834074572281)
  ·
    refine ⟨60410470092239125555929211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80547293456318834074572281 60410470092239125555929211)
    ·
      refine ⟨90615705138358688333893817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60410470092239125555929211 90615705138358688333893817)
      ·
        refine ⟨67961778853769016250420363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90615705138358688333893817 67961778853769016250420363)
        ·
          refine ⟨101942668280653524375630545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67961778853769016250420363 101942668280653524375630545)
          ·
            refine ⟨76457001210490143281722909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101942668280653524375630545 76457001210490143281722909)
            ·
              refine ⟨28671375453933803730646091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76457001210490143281722909 28671375453933803730646091)
              ·
                refine ⟨43007063180900705595969137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28671375453933803730646091 43007063180900705595969137)
                ·
                  refine ⟨32255297385675529196976853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43007063180900705595969137 32255297385675529196976853)
                  ·
                    refine ⟨755983532476770215554145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32255297385675529196976853 755983532476770215554145)
                    ·
                      rfl

theorem cell22_2208409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_2208409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208409 prefixEnd_2208409 := by exact prefixLift 2208409
  have htrace : WordTrace (prefixWord ++ tailWord_2208409) baseStart_2208409 baseEnd_2208409 := by
    simpa [prefixWord, tailWord_2208409, baseEnd_2208409] using wordTrace_append hprefix tailTrace_2208409
  have hstable : (prefixWord ++ tailWord_2208409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208409).length < 2 ^ (prefixWord ++ tailWord_2208409).sum := by decide
  have hdescent : baseEnd_2208409 < baseStart_2208409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208417 : List Nat := [1, 2, 3, 3, 4, 1, 1, 3, 4]
def baseStart_2208417 : Nat := 118140960795 + 2208417 * 2 ^ 59
def prefixEnd_2208417 : Nat := 4983230072969 + 3 ^ 40 * 2208417 * 2
def baseEnd_2208417 : Nat := 251995423680086953784707

theorem tailTrace_2208417 : CollatzResearch.WordTrace tailWord_2208417 prefixEnd_2208417 251995423680086953784707 := by
  unfold tailWord_2208417
  simp only [CollatzResearch.WordTrace]
  refine ⟨80547585240289851440863505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53698390160193234293909003 80547585240289851440863505)
  ·
    refine ⟨60410688930217388580647629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80547585240289851440863505 60410688930217388580647629)
    ·
      refine ⟨22654008348831520717742861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60410688930217388580647629 22654008348831520717742861)
      ·
        refine ⟨8495253130811820269153573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22654008348831520717742861 8495253130811820269153573)
        ·
          refine ⟨1592859962027216300466295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8495253130811820269153573 1592859962027216300466295)
          ·
            refine ⟨2389289943040824450699443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592859962027216300466295 2389289943040824450699443)
            ·
              refine ⟨3583934914561236676049165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389289943040824450699443 3583934914561236676049165)
              ·
                refine ⟨1343975592960463753518437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3583934914561236676049165 1343975592960463753518437)
                ·
                  refine ⟨251995423680086953784707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1343975592960463753518437 251995423680086953784707)
                  ·
                    rfl

theorem cell22_2208417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 4].length) (baseStart_2208417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208417 prefixEnd_2208417 := by exact prefixLift 2208417
  have htrace : WordTrace (prefixWord ++ tailWord_2208417) baseStart_2208417 baseEnd_2208417 := by
    simpa [prefixWord, tailWord_2208417, baseEnd_2208417] using wordTrace_append hprefix tailTrace_2208417
  have hstable : (prefixWord ++ tailWord_2208417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208417).length < 2 ^ (prefixWord ++ tailWord_2208417).sum := by decide
  have hdescent : baseEnd_2208417 < baseStart_2208417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208430 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2208430 : Nat := 118140960795 + 2208430 * 2 ^ 59
def prefixEnd_2208430 : Nat := 4983230072969 + 3 ^ 40 * 2208430 * 2
def baseEnd_2208430 : Nat := 755990721205933160779081

theorem tailTrace_2208430 : CollatzResearch.WordTrace tailWord_2208430 prefixEnd_2208430 755990721205933160779081 := by
  unfold tailWord_2208430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068507423655344332635843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53698706259495169774057829 10068507423655344332635843)
  ·
    refine ⟨15102761135483016498953765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10068507423655344332635843 15102761135483016498953765)
    ·
      refine ⟨2831767712903065593553831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15102761135483016498953765 2831767712903065593553831)
      ·
        refine ⟨4247651569354598390330747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831767712903065593553831 4247651569354598390330747)
        ·
          refine ⟨6371477354031897585496121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4247651569354598390330747 6371477354031897585496121)
          ·
            refine ⟨4778608015523923189122091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6371477354031897585496121 4778608015523923189122091)
            ·
              refine ⟨7167912023285884783683137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778608015523923189122091 7167912023285884783683137)
              ·
                refine ⟨5375934017464413587762353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7167912023285884783683137 5375934017464413587762353)
                ·
                  refine ⟨4031950513098310190821765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5375934017464413587762353 4031950513098310190821765)
                  ·
                    refine ⟨755990721205933160779081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4031950513098310190821765 755990721205933160779081)
                    ·
                      rfl

theorem cell22_2208430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2208430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208430 prefixEnd_2208430 := by exact prefixLift 2208430
  have htrace : WordTrace (prefixWord ++ tailWord_2208430) baseStart_2208430 baseEnd_2208430 := by
    simpa [prefixWord, tailWord_2208430, baseEnd_2208430] using wordTrace_append hprefix tailTrace_2208430
  have hstable : (prefixWord ++ tailWord_2208430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208430).length < 2 ^ (prefixWord ++ tailWord_2208430).sum := by decide
  have hdescent : baseEnd_2208430 < baseStart_2208430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208494 : List Nat := [4, 1, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2208494 : Nat := 118140960795 + 2208494 * 2 ^ 59
def prefixEnd_2208494 : Nat := 4983230072969 + 3 ^ 40 * 2208494 * 2
def baseEnd_2208494 : Nat := 756012629713858327178885

theorem tailTrace_2208494 : CollatzResearch.WordTrace tailWord_2208494 prefixEnd_2208494 756012629713858327178885 := by
  unfold tailWord_2208494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068799207626361698927067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53700262440673929060944357 10068799207626361698927067)
  ·
    refine ⟨15103198811439542548390601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10068799207626361698927067 15103198811439542548390601)
    ·
      refine ⟨11327399108579656911292951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15103198811439542548390601 11327399108579656911292951)
      ·
        refine ⟨16991098662869485366939427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11327399108579656911292951 16991098662869485366939427)
        ·
          refine ⟨25486647994304228050409141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16991098662869485366939427 25486647994304228050409141)
          ·
            refine ⟨2389373249466021379725857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25486647994304228050409141 2389373249466021379725857)
            ·
              refine ⟨1792029937099516034794393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389373249466021379725857 1792029937099516034794393)
              ·
                refine ⟨1344022452824637026095795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792029937099516034794393 1344022452824637026095795)
                ·
                  refine ⟨2016033679236955539143693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344022452824637026095795 2016033679236955539143693)
                  ·
                    refine ⟨756012629713858327178885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016033679236955539143693 756012629713858327178885)
                    ·
                      rfl

theorem cell22_2208494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2208494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208494 prefixEnd_2208494 := by exact prefixLift 2208494
  have htrace : WordTrace (prefixWord ++ tailWord_2208494) baseStart_2208494 baseEnd_2208494 := by
    simpa [prefixWord, tailWord_2208494, baseEnd_2208494] using wordTrace_append hprefix tailTrace_2208494
  have hstable : (prefixWord ++ tailWord_2208494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208494).length < 2 ^ (prefixWord ++ tailWord_2208494).sum := by decide
  have hdescent : baseEnd_2208494 < baseStart_2208494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208531 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 1, 6]
def baseStart_2208531 : Nat := 118140960795 + 2208531 * 2 ^ 59
def prefixEnd_2208531 : Nat := 4983230072969 + 3 ^ 40 * 2208531 * 2
def baseEnd_2208531 : Nat := 756025295570002564003771

theorem tailTrace_2208531 : CollatzResearch.WordTrace tailWord_2208531 prefixEnd_2208531 756025295570002564003771 := by
  unfold tailWord_2208531
  simp only [CollatzResearch.WordTrace]
  refine ⟨80551743161876848910513447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53701162107917899273675631 80551743161876848910513447)
  ·
    refine ⟨120827614742815273365770171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80551743161876848910513447 120827614742815273365770171)
    ·
      refine ⟨181241422114222910048655257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120827614742815273365770171 181241422114222910048655257)
      ·
        refine ⟨135931066585667182536491443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181241422114222910048655257 135931066585667182536491443)
        ·
          refine ⟨203896599878500773804737165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135931066585667182536491443 203896599878500773804737165)
          ·
            refine ⟨76461224954437790176776437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203896599878500773804737165 76461224954437790176776437)
            ·
              refine ⟨7168239839478542829072791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76461224954437790176776437 7168239839478542829072791)
              ·
                refine ⟨10752359759217814243609187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7168239839478542829072791 10752359759217814243609187)
                ·
                  refine ⟨16128539638826721365413781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10752359759217814243609187 16128539638826721365413781)
                  ·
                    refine ⟨756025295570002564003771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16128539638826721365413781 756025295570002564003771)
                    ·
                      rfl

theorem cell22_2208531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_2208531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208531 prefixEnd_2208531 := by exact prefixLift 2208531
  have htrace : WordTrace (prefixWord ++ tailWord_2208531) baseStart_2208531 baseEnd_2208531 := by
    simpa [prefixWord, tailWord_2208531, baseEnd_2208531] using wordTrace_append hprefix tailTrace_2208531
  have hstable : (prefixWord ++ tailWord_2208531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208531).length < 2 ^ (prefixWord ++ tailWord_2208531).sum := by decide
  have hdescent : baseEnd_2208531 < baseStart_2208531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208533 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_2208533 : Nat := 118140960795 + 2208533 * 2 ^ 59
def prefixEnd_2208533 : Nat := 4983230072969 + 3 ^ 40 * 2208533 * 2
def baseEnd_2208533 : Nat := 756025980210875225453765

theorem tailTrace_2208533 : CollatzResearch.WordTrace tailWord_2208533 prefixEnd_2208533 756025980210875225453765 := by
  unfold tailWord_2208533
  simp only [CollatzResearch.WordTrace]
  refine ⟨80551816107869603252086253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53701210738579735501390835 80551816107869603252086253)
  ·
    refine ⟨30206931040451101219532345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80551816107869603252086253 30206931040451101219532345)
    ·
      refine ⟨22655198280338325914649259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30206931040451101219532345 22655198280338325914649259)
      ·
        refine ⟨33982797420507488871973889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22655198280338325914649259 33982797420507488871973889)
        ·
          refine ⟨25487098065380616653980417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33982797420507488871973889 25487098065380616653980417)
          ·
            refine ⟨19115323549035462490485313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25487098065380616653980417 19115323549035462490485313)
            ·
              refine ⟨14336492661776596867863985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19115323549035462490485313 14336492661776596867863985)
              ·
                refine ⟨10752369496332447650897989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14336492661776596867863985 10752369496332447650897989)
                ·
                  refine ⟨2016069280562333934543373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10752369496332447650897989 2016069280562333934543373)
                  ·
                    refine ⟨756025980210875225453765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016069280562333934543373 756025980210875225453765)
                    ·
                      rfl

theorem cell22_2208533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_2208533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208533 prefixEnd_2208533 := by exact prefixLift 2208533
  have htrace : WordTrace (prefixWord ++ tailWord_2208533) baseStart_2208533 baseEnd_2208533 := by
    simpa [prefixWord, tailWord_2208533, baseEnd_2208533] using wordTrace_append hprefix tailTrace_2208533
  have hstable : (prefixWord ++ tailWord_2208533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208533).length < 2 ^ (prefixWord ++ tailWord_2208533).sum := by decide
  have hdescent : baseEnd_2208533 < baseStart_2208533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208576 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_2208576 : Nat := 118140960795 + 2208576 * 2 ^ 59
def prefixEnd_2208576 : Nat := 4983230072969 + 3 ^ 40 * 2208576 * 2
def baseEnd_2208576 : Nat := 756040699989637446628633

theorem tailTrace_2208576 : CollatzResearch.WordTrace tailWord_2208576 prefixEnd_2208576 756040699989637446628633 := by
  unfold tailWord_2208576
  simp only [CollatzResearch.WordTrace]
  refine ⟨40276692223356910797950791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53702256297809214397267721 40276692223356910797950791)
  ·
    refine ⟨60415038335035366196926187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40276692223356910797950791 60415038335035366196926187)
    ·
      refine ⟨90622557502553049295389281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60415038335035366196926187 90622557502553049295389281)
      ·
        refine ⟨67966918126914786971541961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90622557502553049295389281 67966918126914786971541961)
        ·
          refine ⟨50975188595186090228656471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67966918126914786971541961 50975188595186090228656471)
          ·
            refine ⟨76462782892779135342984707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50975188595186090228656471 76462782892779135342984707)
            ·
              refine ⟨114694174339168703014477061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76462782892779135342984707 114694174339168703014477061)
              ·
                refine ⟨21505157688594131815214449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114694174339168703014477061 21505157688594131815214449)
                ·
                  refine ⟨16128868266445598861410837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21505157688594131815214449 16128868266445598861410837)
                  ·
                    refine ⟨756040699989637446628633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16128868266445598861410837 756040699989637446628633)
                    ·
                      rfl

theorem cell22_2208576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_2208576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208576 prefixEnd_2208576 := by exact prefixLift 2208576
  have htrace : WordTrace (prefixWord ++ tailWord_2208576) baseStart_2208576 baseEnd_2208576 := by
    simpa [prefixWord, tailWord_2208576, baseEnd_2208576] using wordTrace_append hprefix tailTrace_2208576
  have hstable : (prefixWord ++ tailWord_2208576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208576).length < 2 ^ (prefixWord ++ tailWord_2208576).sum := by decide
  have hdescent : baseEnd_2208576 < baseStart_2208576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208608 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 5]
def baseStart_2208608 : Nat := 118140960795 + 2208608 * 2 ^ 59
def prefixEnd_2208608 : Nat := 4983230072969 + 3 ^ 40 * 2208608 * 2
def baseEnd_2208608 : Nat := 252017218081200009942845

theorem tailTrace_2208608 : CollatzResearch.WordTrace tailWord_2208608 prefixEnd_2208608 252017218081200009942845 := by
  unfold tailWord_2208608
  simp only [CollatzResearch.WordTrace]
  refine ⟨40277275791298945530533239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53703034388398594040710985 40277275791298945530533239)
  ·
    refine ⟨60415913686948418295799859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40277275791298945530533239 60415913686948418295799859)
    ·
      refine ⟨90623870530422627443699789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60415913686948418295799859 90623870530422627443699789)
      ·
        refine ⟨33983951448908485291387421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90623870530422627443699789 33983951448908485291387421)
        ·
          refine ⟨12743981793340681984270283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33983951448908485291387421 12743981793340681984270283)
          ·
            refine ⟨19115972690011022976405425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12743981793340681984270283 19115972690011022976405425)
            ·
              refine ⟨14336979517508267232304069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19115972690011022976405425 14336979517508267232304069)
              ·
                refine ⟨2688183659532800106057013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14336979517508267232304069 2688183659532800106057013)
                ·
                  refine ⟨252017218081200009942845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2688183659532800106057013 252017218081200009942845)
                  ·
                    rfl

theorem cell22_2208608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_2208608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208608 prefixEnd_2208608 := by exact prefixLift 2208608
  have htrace : WordTrace (prefixWord ++ tailWord_2208608) baseStart_2208608 baseEnd_2208608 := by
    simpa [prefixWord, tailWord_2208608, baseEnd_2208608] using wordTrace_append hprefix tailTrace_2208608
  have hstable : (prefixWord ++ tailWord_2208608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208608).length < 2 ^ (prefixWord ++ tailWord_2208608).sum := by decide
  have hdescent : baseEnd_2208608 < baseStart_2208608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208612 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_2208612 : Nat := 118140960795 + 2208612 * 2 ^ 59
def prefixEnd_2208612 : Nat := 4983230072969 + 3 ^ 40 * 2208612 * 2
def baseEnd_2208612 : Nat := 756053023525345352728523

theorem tailTrace_2208612 : CollatzResearch.WordTrace tailWord_2208612 prefixEnd_2208612 756053023525345352728523 := by
  unfold tailWord_2208612
  simp only [CollatzResearch.WordTrace]
  refine ⟨40277348737291699872106045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53703131649722266496141393 40277348737291699872106045)
  ·
    refine ⟨15104005776484387452039767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40277348737291699872106045 15104005776484387452039767)
    ·
      refine ⟨22656008664726581178059651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15104005776484387452039767 22656008664726581178059651)
      ·
        refine ⟨33984012997089871767089477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22656008664726581178059651 33984012997089871767089477)
        ·
          refine ⟨6372002436954350956329277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33984012997089871767089477 6372002436954350956329277)
          ·
            refine ⟨2389500913857881608623479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6372002436954350956329277 2389500913857881608623479)
            ·
              refine ⟨3584251370786822412935219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389500913857881608623479 3584251370786822412935219)
              ·
                refine ⟨5376377056180233619402829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584251370786822412935219 5376377056180233619402829)
                ·
                  refine ⟨2016141396067587607276061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5376377056180233619402829 2016141396067587607276061)
                  ·
                    refine ⟨756053023525345352728523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016141396067587607276061 756053023525345352728523)
                    ·
                      rfl

theorem cell22_2208612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_2208612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208612 prefixEnd_2208612 := by exact prefixLift 2208612
  have htrace : WordTrace (prefixWord ++ tailWord_2208612) baseStart_2208612 baseEnd_2208612 := by
    simpa [prefixWord, tailWord_2208612, baseEnd_2208612] using wordTrace_append hprefix tailTrace_2208612
  have hstable : (prefixWord ++ tailWord_2208612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208612).length < 2 ^ (prefixWord ++ tailWord_2208612).sum := by decide
  have hdescent : baseEnd_2208612 < baseStart_2208612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208625 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 5]
def baseStart_2208625 : Nat := 118140960795 + 2208625 * 2 ^ 59
def prefixEnd_2208625 : Nat := 4983230072969 + 3 ^ 40 * 2208625 * 2
def baseEnd_2208625 : Nat := 252019157897005884051161

theorem tailTrace_2208625 : CollatzResearch.WordTrace tailWord_2208625 prefixEnd_2208625 252019157897005884051161 := by
  unfold tailWord_2208625
  simp only [CollatzResearch.WordTrace]
  refine ⟨80555171623536302964435329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53703447749024201976290219 80555171623536302964435329)
  ·
    refine ⟨60416378717652227223326497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80555171623536302964435329 60416378717652227223326497)
    ·
      refine ⟨45312284038239170417494873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60416378717652227223326497 45312284038239170417494873)
      ·
        refine ⟨33984213028679377813121155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45312284038239170417494873 33984213028679377813121155)
        ·
          refine ⟨50976319543019066719681733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33984213028679377813121155 50976319543019066719681733)
          ·
            refine ⟨9558059914316075009940325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50976319543019066719681733 9558059914316075009940325)
            ·
              refine ⟨1792136233934264064363811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9558059914316075009940325 1792136233934264064363811)
              ·
                refine ⟨2688204350901396096545717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792136233934264064363811 2688204350901396096545717)
                ·
                  refine ⟨252019157897005884051161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2688204350901396096545717 252019157897005884051161)
                  ·
                    rfl

theorem cell22_2208625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_2208625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208625 prefixEnd_2208625 := by exact prefixLift 2208625
  have htrace : WordTrace (prefixWord ++ tailWord_2208625) baseStart_2208625 baseEnd_2208625 := by
    simpa [prefixWord, tailWord_2208625, baseEnd_2208625] using wordTrace_append hprefix tailTrace_2208625
  have hstable : (prefixWord ++ tailWord_2208625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208625).length < 2 ^ (prefixWord ++ tailWord_2208625).sum := by decide
  have hdescent : baseEnd_2208625 < baseStart_2208625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208710 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2208710 : Nat := 118140960795 + 2208710 * 2 ^ 59
def prefixEnd_2208710 : Nat := 4983230072969 + 3 ^ 40 * 2208710 * 2
def baseEnd_2208710 : Nat := 252028856976035254592741

theorem tailTrace_2208710 : CollatzResearch.WordTrace tailWord_2208710 prefixEnd_2208710 252028856976035254592741 := by
  unfold tailWord_2208710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517445994632136327539987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53705514552152241654186389 2517445994632136327539987)
  ·
    refine ⟨3776168991948204491309981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2517445994632136327539987 3776168991948204491309981)
    ·
      refine ⟨1416063371980576684241243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3776168991948204491309981 1416063371980576684241243)
      ·
        refine ⟨2124095057970865026361865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416063371980576684241243 2124095057970865026361865)
        ·
          refine ⟨1593071293478148769771399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2124095057970865026361865 1593071293478148769771399)
          ·
            refine ⟨2389606940217223154657099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593071293478148769771399 2389606940217223154657099)
            ·
              refine ⟨3584410410325834731985649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389606940217223154657099 3584410410325834731985649)
              ·
                refine ⟨2688307807744376048989237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3584410410325834731985649 2688307807744376048989237)
                ·
                  refine ⟨252028856976035254592741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2688307807744376048989237 252028856976035254592741)
                  ·
                    rfl

theorem cell22_2208710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2208710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208710 prefixEnd_2208710 := by exact prefixLift 2208710
  have htrace : WordTrace (prefixWord ++ tailWord_2208710) baseStart_2208710 baseEnd_2208710 := by
    simpa [prefixWord, tailWord_2208710, baseEnd_2208710] using wordTrace_append hprefix tailTrace_2208710
  have hstable : (prefixWord ++ tailWord_2208710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208710).length < 2 ^ (prefixWord ++ tailWord_2208710).sum := by decide
  have hdescent : baseEnd_2208710 < baseStart_2208710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208764 : List Nat := [2, 2, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_2208764 : Nat := 118140960795 + 2208764 * 2 ^ 59
def prefixEnd_2208764 : Nat := 4983230072969 + 3 ^ 40 * 2208764 * 2
def baseEnd_2208764 : Nat := 756105056231667622928057

theorem tailTrace_2208764 : CollatzResearch.WordTrace tailWord_2208764 prefixEnd_2208764 756105056231667622928057 := by
  unfold tailWord_2208764
  simp only [CollatzResearch.WordTrace]
  refine ⟨40280120685016364851872673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53706827580021819802496897 40280120685016364851872673)
  ·
    refine ⟨30210090513762273638904505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40280120685016364851872673 30210090513762273638904505)
    ·
      refine ⟨22657567885321705229178379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30210090513762273638904505 22657567885321705229178379)
      ·
        refine ⟨33986351827982557843767569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22657567885321705229178379 33986351827982557843767569)
        ·
          refine ⟨25489763870986918382825677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33986351827982557843767569 25489763870986918382825677)
          ·
            refine ⟨9558661451620094393559629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25489763870986918382825677 9558661451620094393559629)
            ·
              refine ⟨3584498044357535397584861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9558661451620094393559629 3584498044357535397584861)
              ·
                refine ⟨1344186766634075774094323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3584498044357535397584861 1344186766634075774094323)
                ·
                  refine ⟨2016280149951113661141485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344186766634075774094323 2016280149951113661141485)
                  ·
                    refine ⟨756105056231667622928057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016280149951113661141485 756105056231667622928057)
                    ·
                      rfl

theorem cell22_2208764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_2208764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208764 prefixEnd_2208764 := by exact prefixLift 2208764
  have htrace : WordTrace (prefixWord ++ tailWord_2208764) baseStart_2208764 baseEnd_2208764 := by
    simpa [prefixWord, tailWord_2208764, baseEnd_2208764] using wordTrace_append hprefix tailTrace_2208764
  have hstable : (prefixWord ++ tailWord_2208764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208764).length < 2 ^ (prefixWord ++ tailWord_2208764).sum := by decide
  have hdescent : baseEnd_2208764 < baseStart_2208764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208824 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 1, 4]
def baseStart_2208824 : Nat := 118140960795 + 2208824 * 2 ^ 59
def prefixEnd_2208824 : Nat := 4983230072969 + 3 ^ 40 * 2208824 * 2
def baseEnd_2208824 : Nat := 756125595457847466427873

theorem tailTrace_2208824 : CollatzResearch.WordTrace tailWord_2208824 prefixEnd_2208824 756125595457847466427873 := by
  unfold tailWord_2208824
  simp only [CollatzResearch.WordTrace]
  refine ⟨40281214874907679975464763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53708286499876906633953017 40281214874907679975464763)
  ·
    refine ⟨60421822312361519963197145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40281214874907679975464763 60421822312361519963197145)
    ·
      refine ⟨45316366734271139972397859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60421822312361519963197145 45316366734271139972397859)
      ·
        refine ⟨67974550101406709958596789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45316366734271139972397859 67974550101406709958596789)
        ·
          refine ⟨6372614072006879058618449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67974550101406709958596789 6372614072006879058618449)
          ·
            refine ⟨4779460554005159293963837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6372614072006879058618449 4779460554005159293963837)
            ·
              refine ⟨1792297707751934735236439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4779460554005159293963837 1792297707751934735236439)
              ·
                refine ⟨2688446561627902102854659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792297707751934735236439 2688446561627902102854659)
                ·
                  refine ⟨4032669842441853154281989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688446561627902102854659 4032669842441853154281989)
                  ·
                    refine ⟨756125595457847466427873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4032669842441853154281989 756125595457847466427873)
                    ·
                      rfl

theorem cell22_2208824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_2208824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208824 prefixEnd_2208824 := by exact prefixLift 2208824
  have htrace : WordTrace (prefixWord ++ tailWord_2208824) baseStart_2208824 baseEnd_2208824 := by
    simpa [prefixWord, tailWord_2208824, baseEnd_2208824] using wordTrace_append hprefix tailTrace_2208824
  have hstable : (prefixWord ++ tailWord_2208824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208824).length < 2 ^ (prefixWord ++ tailWord_2208824).sum := by decide
  have hdescent : baseEnd_2208824 < baseStart_2208824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208835 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 2, 4]
def baseStart_2208835 : Nat := 118140960795 + 2208835 * 2 ^ 59
def prefixEnd_2208835 : Nat := 4983230072969 + 3 ^ 40 * 2208835 * 2
def baseEnd_2208835 : Nat := 756129360982647104402839

theorem tailTrace_2208835 : CollatzResearch.WordTrace tailWord_2208835 prefixEnd_2208835 756129360982647104402839 := by
  unfold tailWord_2208835
  simp only [CollatzResearch.WordTrace]
  refine ⟨80562830952775508829579959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53708553968517005886386639 80562830952775508829579959)
  ·
    refine ⟨120844246429163263244369939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80562830952775508829579959 120844246429163263244369939)
    ·
      refine ⟨181266369643744894866554909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120844246429163263244369939 181266369643744894866554909)
      ·
        refine ⟨67974888616404335574958091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181266369643744894866554909 67974888616404335574958091)
        ·
          refine ⟨101962332924606503362437137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67974888616404335574958091 101962332924606503362437137)
          ·
            refine ⟨76471749693454877521827853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101962332924606503362437137 76471749693454877521827853)
            ·
              refine ⟨28676906135045579070685445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76471749693454877521827853 28676906135045579070685445)
              ·
                refine ⟨5376919900321046075753521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28676906135045579070685445 5376919900321046075753521)
                ·
                  refine ⟨4032689925240784556815141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5376919900321046075753521 4032689925240784556815141)
                  ·
                    refine ⟨756129360982647104402839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4032689925240784556815141 756129360982647104402839)
                    ·
                      rfl

theorem cell22_2208835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 4].length) (baseStart_2208835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208835 prefixEnd_2208835 := by exact prefixLift 2208835
  have htrace : WordTrace (prefixWord ++ tailWord_2208835) baseStart_2208835 baseEnd_2208835 := by
    simpa [prefixWord, tailWord_2208835, baseEnd_2208835] using wordTrace_append hprefix tailTrace_2208835
  have hstable : (prefixWord ++ tailWord_2208835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208835).length < 2 ^ (prefixWord ++ tailWord_2208835).sum := by decide
  have hdescent : baseEnd_2208835 < baseStart_2208835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208837 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_2208837 : Nat := 118140960795 + 2208837 * 2 ^ 59
def prefixEnd_2208837 : Nat := 4983230072969 + 3 ^ 40 * 2208837 * 2
def baseEnd_2208837 : Nat := 756130045623519765852833

theorem tailTrace_2208837 : CollatzResearch.WordTrace tailWord_2208837 prefixEnd_2208837 756130045623519765852833 := by
  unfold tailWord_2208837
  simp only [CollatzResearch.WordTrace]
  refine ⟨80562903898768263171152765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53708602599178842114101843 80562903898768263171152765)
  ·
    refine ⟨30211088962038098689182287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80562903898768263171152765 30211088962038098689182287)
    ·
      refine ⟨45316633443057148033773431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30211088962038098689182287 45316633443057148033773431)
      ·
        refine ⟨67974950164585722050660147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45316633443057148033773431 67974950164585722050660147)
        ·
          refine ⟨101962425246878583075990221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67974950164585722050660147 101962425246878583075990221)
          ·
            refine ⟨38235909467579468653496333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101962425246878583075990221 38235909467579468653496333)
            ·
              refine ⟨14338466050342300745061125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38235909467579468653496333 14338466050342300745061125)
              ·
                refine ⟨2688462384439181389698961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14338466050342300745061125 2688462384439181389698961)
                ·
                  refine ⟨2016346788329386042274221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2688462384439181389698961 2016346788329386042274221)
                  ·
                    refine ⟨756130045623519765852833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016346788329386042274221 756130045623519765852833)
                    ·
                      rfl

theorem cell22_2208837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_2208837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208837 prefixEnd_2208837 := by exact prefixLift 2208837
  have htrace : WordTrace (prefixWord ++ tailWord_2208837) baseStart_2208837 baseEnd_2208837 := by
    simpa [prefixWord, tailWord_2208837, baseEnd_2208837] using wordTrace_append hprefix tailTrace_2208837
  have hstable : (prefixWord ++ tailWord_2208837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208837).length < 2 ^ (prefixWord ++ tailWord_2208837).sum := by decide
  have hdescent : baseEnd_2208837 < baseStart_2208837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208839 : List Nat := [1, 1, 4, 1, 3, 2, 4, 2, 4]
def baseStart_2208839 : Nat := 118140960795 + 2208839 * 2 ^ 59
def prefixEnd_2208839 : Nat := 4983230072969 + 3 ^ 40 * 2208839 * 2
def baseEnd_2208839 : Nat := 252043576754797475767609

theorem tailTrace_2208839 : CollatzResearch.WordTrace tailWord_2208839 prefixEnd_2208839 252043576754797475767609 := by
  unfold tailWord_2208839
  simp only [CollatzResearch.WordTrace]
  refine ⟨80562976844761017512725571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53708651229840678341817047 80562976844761017512725571)
  ·
    refine ⟨120844465267141526269088357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80562976844761017512725571 120844465267141526269088357)
    ·
      refine ⟨22658337237589036175454067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120844465267141526269088357 22658337237589036175454067)
      ·
        refine ⟨33987505856383554263181101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22658337237589036175454067 33987505856383554263181101)
        ·
          refine ⟨12745314696143832848692913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33987505856383554263181101 12745314696143832848692913)
          ·
            refine ⟨9558986022107874636519685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12745314696143832848692913 9558986022107874636519685)
            ·
              refine ⟨1792309879145226494347441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9558986022107874636519685 1792309879145226494347441)
              ·
                refine ⟨1344232409358919870760581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792309879145226494347441 1344232409358919870760581)
                ·
                  refine ⟨252043576754797475767609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1344232409358919870760581 252043576754797475767609)
                  ·
                    rfl

theorem cell22_2208839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 4].length) (baseStart_2208839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208839 prefixEnd_2208839 := by exact prefixLift 2208839
  have htrace : WordTrace (prefixWord ++ tailWord_2208839) baseStart_2208839 baseEnd_2208839 := by
    simpa [prefixWord, tailWord_2208839, baseEnd_2208839] using wordTrace_append hprefix tailTrace_2208839
  have hstable : (prefixWord ++ tailWord_2208839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208839).length < 2 ^ (prefixWord ++ tailWord_2208839).sum := by decide
  have hdescent : baseEnd_2208839 < baseStart_2208839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208882 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_2208882 : Nat := 118140960795 + 2208882 * 2 ^ 59
def prefixEnd_2208882 : Nat := 4983230072969 + 3 ^ 40 * 2208882 * 2
def baseEnd_2208882 : Nat := 756145450043154648477695

theorem tailTrace_2208882 : CollatzResearch.WordTrace tailWord_2208882 prefixEnd_2208882 756145450043154648477695 := by
  unfold tailWord_2208882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20141136295901308964135225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53709696789070157237693933 20141136295901308964135225)
  ·
    refine ⟨15105852221925981723101419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20141136295901308964135225 15105852221925981723101419)
    ·
      refine ⟨22658778332888972584652129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15105852221925981723101419 22658778332888972584652129)
      ·
        refine ⟨16994083749666729438489097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22658778332888972584652129 16994083749666729438489097)
        ·
          refine ⟨12745562812250047078866823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16994083749666729438489097 12745562812250047078866823)
          ·
            refine ⟨19118344218375070618300235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12745562812250047078866823 19118344218375070618300235)
            ·
              refine ⟨28677516327562605927450353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19118344218375070618300235 28677516327562605927450353)
              ·
                refine ⟨21508137245671954445587765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28677516327562605927450353 21508137245671954445587765)
                ·
                  refine ⟨2016387866781745729273853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21508137245671954445587765 2016387866781745729273853)
                  ·
                    refine ⟨756145450043154648477695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016387866781745729273853 756145450043154648477695)
                    ·
                      rfl

theorem cell22_2208882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_2208882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208882 prefixEnd_2208882 := by exact prefixLift 2208882
  have htrace : WordTrace (prefixWord ++ tailWord_2208882) baseStart_2208882 baseEnd_2208882 := by
    simpa [prefixWord, tailWord_2208882, baseEnd_2208882] using wordTrace_append hprefix tailTrace_2208882
  have hstable : (prefixWord ++ tailWord_2208882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208882).length < 2 ^ (prefixWord ++ tailWord_2208882).sum := by decide
  have hdescent : baseEnd_2208882 < baseStart_2208882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208899 : List Nat := [1, 1, 1, 3, 3, 2, 1, 6, 1, 3]
def baseStart_2208899 : Nat := 118140960795 + 2208899 * 2 ^ 59
def prefixEnd_2208899 : Nat := 4983230072969 + 3 ^ 40 * 2208899 * 2
def baseEnd_2208899 : Nat := 756151269490572270802643

theorem tailTrace_2208899 : CollatzResearch.WordTrace tailWord_2208899 prefixEnd_2208899 756151269490572270802643 := by
  unfold tailWord_2208899
  simp only [CollatzResearch.WordTrace]
  refine ⟨80565165224543647759909751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53710110149695765173273167 80565165224543647759909751)
  ·
    refine ⟨120847747836815471639864627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80565165224543647759909751 120847747836815471639864627)
    ·
      refine ⟨181271621755223207459796941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120847747836815471639864627 181271621755223207459796941)
      ·
        refine ⟨67976858158208702797423853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181271621755223207459796941 67976858158208702797423853)
        ·
          refine ⟨25491321809328263549033945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67976858158208702797423853 25491321809328263549033945)
          ·
            refine ⟨19118491356996197661775459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25491321809328263549033945 19118491356996197661775459)
            ·
              refine ⟨28677737035494296492663189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19118491356996197661775459 28677737035494296492663189)
              ·
                refine ⟨1344268923538795148093587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28677737035494296492663189 1344268923538795148093587)
                ·
                  refine ⟨2016403385308192722140381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344268923538795148093587 2016403385308192722140381)
                  ·
                    refine ⟨756151269490572270802643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016403385308192722140381 756151269490572270802643)
                    ·
                      rfl

theorem cell22_2208899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 3].length) (baseStart_2208899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208899 prefixEnd_2208899 := by exact prefixLift 2208899
  have htrace : WordTrace (prefixWord ++ tailWord_2208899) baseStart_2208899 baseEnd_2208899 := by
    simpa [prefixWord, tailWord_2208899, baseEnd_2208899] using wordTrace_append hprefix tailTrace_2208899
  have hstable : (prefixWord ++ tailWord_2208899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208899).length < 2 ^ (prefixWord ++ tailWord_2208899).sum := by decide
  have hdescent : baseEnd_2208899 < baseStart_2208899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208950 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2208950 : Nat := 118140960795 + 2208950 * 2 ^ 59
def prefixEnd_2208950 : Nat := 4983230072969 + 3 ^ 40 * 2208950 * 2
def baseEnd_2208950 : Nat := 756168727832825137777487

theorem tailTrace_2208950 : CollatzResearch.WordTrace tailWord_2208950 prefixEnd_2208950 756168727832825137777487 := by
  unfold tailWord_2208950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5035439084209930216876019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53711350231572588980010869 5035439084209930216876019)
  ·
    refine ⟨7553158626314895325314029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5035439084209930216876019 7553158626314895325314029)
    ·
      refine ⟨2832434484868085746992761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7553158626314895325314029 2832434484868085746992761)
      ·
        refine ⟨2124325863651064310244571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2832434484868085746992761 2124325863651064310244571)
        ·
          refine ⟨3186488795476596465366857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2124325863651064310244571 3186488795476596465366857)
          ·
            refine ⟨2389866596607447349025143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3186488795476596465366857 2389866596607447349025143)
            ·
              refine ⟨3584799894911171023537715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389866596607447349025143 3584799894911171023537715)
              ·
                refine ⟨5377199842366756535306573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584799894911171023537715 5377199842366756535306573)
                ·
                  refine ⟨2016449940887533700739965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5377199842366756535306573 2016449940887533700739965)
                  ·
                    refine ⟨756168727832825137777487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016449940887533700739965 756168727832825137777487)
                    ·
                      rfl

theorem cell22_2208950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2208950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208950 prefixEnd_2208950 := by exact prefixLift 2208950
  have htrace : WordTrace (prefixWord ++ tailWord_2208950) baseStart_2208950 baseEnd_2208950 := by
    simpa [prefixWord, tailWord_2208950, baseEnd_2208950] using wordTrace_append hprefix tailTrace_2208950
  have hstable : (prefixWord ++ tailWord_2208950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208950).length < 2 ^ (prefixWord ++ tailWord_2208950).sum := by decide
  have hdescent : baseEnd_2208950 < baseStart_2208950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208955 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 5, 5]
def baseStart_2208955 : Nat := 118140960795 + 2208955 * 2 ^ 59
def prefixEnd_2208955 : Nat := 4983230072969 + 3 ^ 40 * 2208955 * 2
def baseEnd_2208955 : Nat := 756170439435006791402471

theorem tailTrace_2208955 : CollatzResearch.WordTrace tailWord_2208955 prefixEnd_2208955 756170439435006791402471 := by
  unfold tailWord_2208955
  simp only [CollatzResearch.WordTrace]
  refine ⟨80567207712340769323948319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53711471808227179549298879 80567207712340769323948319)
  ·
    refine ⟨120850811568511153985922479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80567207712340769323948319 120850811568511153985922479)
    ·
      refine ⟨181276217352766730978883719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120850811568511153985922479 181276217352766730978883719)
      ·
        refine ⟨271914326029150096468325579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181276217352766730978883719 271914326029150096468325579)
        ·
          refine ⟨407871489043725144702488369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271914326029150096468325579 407871489043725144702488369)
          ·
            refine ⟨305903616782793858526866277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407871489043725144702488369 305903616782793858526866277)
            ·
              refine ⟨57356928146773848473787427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 305903616782793858526866277 57356928146773848473787427)
              ·
                refine ⟨86035392220160772710681141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57356928146773848473787427 86035392220160772710681141)
                ·
                  refine ⟨8065818020640072441626357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86035392220160772710681141 8065818020640072441626357)
                  ·
                    refine ⟨756170439435006791402471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8065818020640072441626357 756170439435006791402471)
                    ·
                      rfl

theorem cell22_2208955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_2208955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208955 prefixEnd_2208955 := by exact prefixLift 2208955
  have htrace : WordTrace (prefixWord ++ tailWord_2208955) baseStart_2208955 baseEnd_2208955 := by
    simpa [prefixWord, tailWord_2208955, baseEnd_2208955] using wordTrace_append hprefix tailTrace_2208955
  have hstable : (prefixWord ++ tailWord_2208955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208955).length < 2 ^ (prefixWord ++ tailWord_2208955).sum := by decide
  have hdescent : baseEnd_2208955 < baseStart_2208955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2208957 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 6]
def baseStart_2208957 : Nat := 118140960795 + 2208957 * 2 ^ 59
def prefixEnd_2208957 : Nat := 4983230072969 + 3 ^ 40 * 2208957 * 2
def baseEnd_2208957 : Nat := 252057041358626484284155

theorem tailTrace_2208957 : CollatzResearch.WordTrace tailWord_2208957 prefixEnd_2208957 252057041358626484284155 := by
  unfold tailWord_2208957
  simp only [CollatzResearch.WordTrace]
  refine ⟨80567280658333523665521125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53711520438889015777014083 80567280658333523665521125)
  ·
    refine ⟨15106365123437535687285211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80567280658333523665521125 15106365123437535687285211)
    ·
      refine ⟨22659547685156303530927817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15106365123437535687285211 22659547685156303530927817)
      ·
        refine ⟨16994660763867227648195863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22659547685156303530927817 16994660763867227648195863)
        ·
          refine ⟨25491991145800841472293795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16994660763867227648195863 25491991145800841472293795)
          ·
            refine ⟨38237986718701262208440693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25491991145800841472293795 38237986718701262208440693)
            ·
              refine ⟨3584811254878243332041315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38237986718701262208440693 3584811254878243332041315)
              ·
                refine ⟨5377216882317364998061973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584811254878243332041315 5377216882317364998061973)
                ·
                  refine ⟨252057041358626484284155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5377216882317364998061973 252057041358626484284155)
                  ·
                    rfl

theorem cell22_2208957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_2208957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2208957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2208957 prefixEnd_2208957 := by exact prefixLift 2208957
  have htrace : WordTrace (prefixWord ++ tailWord_2208957) baseStart_2208957 baseEnd_2208957 := by
    simpa [prefixWord, tailWord_2208957, baseEnd_2208957] using wordTrace_append hprefix tailTrace_2208957
  have hstable : (prefixWord ++ tailWord_2208957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2208957).length < 2 ^ (prefixWord ++ tailWord_2208957).sum := by decide
  have hdescent : baseEnd_2208957 < baseStart_2208957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2208957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209047 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 7]
def baseStart_2209047 : Nat := 118140960795 + 2209047 * 2 ^ 59
def prefixEnd_2209047 : Nat := 4983230072969 + 3 ^ 40 * 2209047 * 2
def baseEnd_2209047 : Nat := 252067310971716406034063

theorem tailTrace_2209047 : CollatzResearch.WordTrace tailWord_2209047 prefixEnd_2209047 252067310971716406034063 := by
  unfold tailWord_2209047
  simp only [CollatzResearch.WordTrace]
  refine ⟨80570563228007469036297395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53713708818671646024198263 80570563228007469036297395)
  ·
    refine ⟨120855844842011203554446093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80570563228007469036297395 120855844842011203554446093)
    ·
      refine ⟨45320941815754201332917285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120855844842011203554446093 45320941815754201332917285)
      ·
        refine ⟨8497676590453912749921991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45320941815754201332917285 8497676590453912749921991)
        ·
          refine ⟨12746514885680869124882987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8497676590453912749921991 12746514885680869124882987)
          ·
            refine ⟨19119772328521303687324481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12746514885680869124882987 19119772328521303687324481)
            ·
              refine ⟨14339829246390977765493361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19119772328521303687324481 14339829246390977765493361)
              ·
                refine ⟨10754871934793233324120021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14339829246390977765493361 10754871934793233324120021)
                ·
                  refine ⟨252067310971716406034063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10754871934793233324120021 252067310971716406034063)
                  ·
                    rfl

theorem cell22_2209047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 7].length) (baseStart_2209047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209047 prefixEnd_2209047 := by exact prefixLift 2209047
  have htrace : WordTrace (prefixWord ++ tailWord_2209047) baseStart_2209047 baseEnd_2209047 := by
    simpa [prefixWord, tailWord_2209047, baseEnd_2209047] using wordTrace_append hprefix tailTrace_2209047
  have hstable : (prefixWord ++ tailWord_2209047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209047).length < 2 ^ (prefixWord ++ tailWord_2209047).sum := by decide
  have hdescent : baseEnd_2209047 < baseStart_2209047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209064 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 7]
def baseStart_2209064 : Nat := 118140960795 + 2209064 * 2 ^ 59
def prefixEnd_2209064 : Nat := 4983230072969 + 3 ^ 40 * 2209064 * 2
def baseEnd_2209064 : Nat := 252069250787522280142379

theorem tailTrace_2209064 : CollatzResearch.WordTrace tailWord_2209064 prefixEnd_2209064 252069250787522280142379 := by
  unfold tailWord_2209064
  simp only [CollatzResearch.WordTrace]
  refine ⟨40285591634472940469833123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53714122179297253959777497 40285591634472940469833123)
  ·
    refine ⟨60428387451709410704749685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40285591634472940469833123 60428387451709410704749685)
    ·
      refine ⟨5665161323597757253570283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60428387451709410704749685 5665161323597757253570283)
      ·
        refine ⟨8497741985396635880355425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5665161323597757253570283 8497741985396635880355425)
        ·
          refine ⟨6373306489047476910266569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8497741985396635880355425 6373306489047476910266569)
          ·
            refine ⟨4779979866785607682699927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6373306489047476910266569 4779979866785607682699927)
            ·
              refine ⟨7169969800178411524049891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4779979866785607682699927 7169969800178411524049891)
              ·
                refine ⟨10754954700267617286074837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7169969800178411524049891 10754954700267617286074837)
                ·
                  refine ⟨252069250787522280142379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10754954700267617286074837 252069250787522280142379)
                  ·
                    rfl

theorem cell22_2209064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_2209064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209064 prefixEnd_2209064 := by exact prefixLift 2209064
  have htrace : WordTrace (prefixWord ++ tailWord_2209064) baseStart_2209064 baseEnd_2209064 := by
    simpa [prefixWord, tailWord_2209064, baseEnd_2209064] using wordTrace_append hprefix tailTrace_2209064
  have hstable : (prefixWord ++ tailWord_2209064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209064).length < 2 ^ (prefixWord ++ tailWord_2209064).sum := by decide
  have hdescent : baseEnd_2209064 < baseStart_2209064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209107 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 3, 5]
def baseStart_2209107 : Nat := 118140960795 + 2209107 * 2 ^ 59
def prefixEnd_2209107 : Nat := 4983230072969 + 3 ^ 40 * 2209107 * 2
def baseEnd_2209107 : Nat := 756222472141329061602005

theorem tailTrace_2209107 : CollatzResearch.WordTrace tailWord_2209107 prefixEnd_2209107 756222472141329061602005 := by
  unfold tailWord_2209107
  simp only [CollatzResearch.WordTrace]
  refine ⟨80572751607790099283481575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53715167738526732855654383 80572751607790099283481575)
  ·
    refine ⟨120859127411685148925222363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80572751607790099283481575 120859127411685148925222363)
    ·
      refine ⟨181288691117527723387833545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120859127411685148925222363 181288691117527723387833545)
      ·
        refine ⟨135966518338145792540875159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181288691117527723387833545 135966518338145792540875159)
        ·
          refine ⟨203949777507218688811312739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135966518338145792540875159 203949777507218688811312739)
          ·
            refine ⟨305924666260828033216969109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203949777507218688811312739 305924666260828033216969109)
            ·
              refine ⟨14340218730976314057045427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 305924666260828033216969109 14340218730976314057045427)
              ·
                refine ⟨21510328096464471085568141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14340218730976314057045427 21510328096464471085568141)
                ·
                  refine ⟨8066373036174176657088053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21510328096464471085568141 8066373036174176657088053)
                  ·
                    refine ⟨756222472141329061602005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8066373036174176657088053 756222472141329061602005)
                    ·
                      rfl

theorem cell22_2209107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_2209107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209107 prefixEnd_2209107 := by exact prefixLift 2209107
  have htrace : WordTrace (prefixWord ++ tailWord_2209107) baseStart_2209107 baseEnd_2209107 := by
    simpa [prefixWord, tailWord_2209107, baseEnd_2209107] using wordTrace_append hprefix tailTrace_2209107
  have hstable : (prefixWord ++ tailWord_2209107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209107).length < 2 ^ (prefixWord ++ tailWord_2209107).sum := by decide
  have hdescent : baseEnd_2209107 < baseStart_2209107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209137 : List Nat := [1, 2, 2, 2, 1, 2, 3, 9]
def baseStart_2209137 : Nat := 118140960795 + 2209137 * 2 ^ 59
def prefixEnd_2209137 : Nat := 4983230072969 + 3 ^ 40 * 2209137 * 2
def baseEnd_2209137 : Nat := 84025860194935442594657

theorem tailTrace_2209137 : CollatzResearch.WordTrace tailWord_2209137 prefixEnd_2209137 84025860194935442594657 := by
  unfold tailWord_2209137
  simp only [CollatzResearch.WordTrace]
  refine ⟨80573845797681414407073665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53715897198454276271382443 80573845797681414407073665)
  ·
    refine ⟨60430384348261060805305249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80573845797681414407073665 60430384348261060805305249)
    ·
      refine ⟨45322788261195795603978937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60430384348261060805305249 45322788261195795603978937)
      ·
        refine ⟨33992091195896846702984203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45322788261195795603978937 33992091195896846702984203)
        ·
          refine ⟨50988136793845270054476305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33992091195896846702984203 50988136793845270054476305)
          ·
            refine ⟨38241102595383952540857229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50988136793845270054476305 38241102595383952540857229)
            ·
              refine ⟨14340413473268982202821461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38241102595383952540857229 14340413473268982202821461)
              ·
                refine ⟨84025860194935442594657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14340413473268982202821461 84025860194935442594657)
                ·
                  rfl

theorem cell22_2209137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 9].length) (baseStart_2209137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209137 prefixEnd_2209137 := by exact prefixLift 2209137
  have htrace : WordTrace (prefixWord ++ tailWord_2209137) baseStart_2209137 baseEnd_2209137 := by
    simpa [prefixWord, tailWord_2209137, baseEnd_2209137] using wordTrace_append hprefix tailTrace_2209137
  have hstable : (prefixWord ++ tailWord_2209137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209137).length < 2 ^ (prefixWord ++ tailWord_2209137).sum := by decide
  have hdescent : baseEnd_2209137 < baseStart_2209137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209152 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_2209152 : Nat := 118140960795 + 2209152 * 2 ^ 59
def prefixEnd_2209152 : Nat := 4983230072969 + 3 ^ 40 * 2209152 * 2
def baseEnd_2209152 : Nat := 756237876560963944226867

theorem tailTrace_2209152 : CollatzResearch.WordTrace tailWord_2209152 prefixEnd_2209152 756237876560963944226867 := by
  unfold tailWord_2209152
  simp only [CollatzResearch.WordTrace]
  refine ⟨40287196446313535984434855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53716261928418047979246473 40287196446313535984434855)
  ·
    refine ⟨60430794669470303976652283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40287196446313535984434855 60430794669470303976652283)
    ·
      refine ⟨90646192004205455964978425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60430794669470303976652283 90646192004205455964978425)
      ·
        refine ⟨67984644003154091973733819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90646192004205455964978425 67984644003154091973733819)
        ·
          refine ⟨101976966004731137960600729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67984644003154091973733819 101976966004731137960600729)
          ·
            refine ⟨76482724503548353470450547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101976966004731137960600729 76482724503548353470450547)
            ·
              refine ⟨114724086755322530205675821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76482724503548353470450547 114724086755322530205675821)
              ·
                refine ⟨43021532533245948827128433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114724086755322530205675821 43021532533245948827128433)
                ·
                  refine ⟨32266149399934461620346325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43021532533245948827128433 32266149399934461620346325)
                  ·
                    refine ⟨756237876560963944226867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32266149399934461620346325 756237876560963944226867)
                    ·
                      rfl

theorem cell22_2209152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_2209152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209152 prefixEnd_2209152 := by exact prefixLift 2209152
  have htrace : WordTrace (prefixWord ++ tailWord_2209152) baseStart_2209152 baseEnd_2209152 := by
    simpa [prefixWord, tailWord_2209152, baseEnd_2209152] using wordTrace_append hprefix tailTrace_2209152
  have hstable : (prefixWord ++ tailWord_2209152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209152).length < 2 ^ (prefixWord ++ tailWord_2209152).sum := by decide
  have hdescent : baseEnd_2209152 < baseStart_2209152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209156 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_2209156 : Nat := 118140960795 + 2209156 * 2 ^ 59
def prefixEnd_2209156 : Nat := 4983230072969 + 3 ^ 40 * 2209156 * 2
def baseEnd_2209156 : Nat := 756239245842709267126855

theorem tailTrace_2209156 : CollatzResearch.WordTrace tailWord_2209156 prefixEnd_2209156 756239245842709267126855 := by
  unfold tailWord_2209156
  simp only [CollatzResearch.WordTrace]
  refine ⟨40287269392306290326007661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53716359189741720434676881 40287269392306290326007661)
  ·
    refine ⟨15107726022114858872252873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40287269392306290326007661 15107726022114858872252873)
    ·
      refine ⟨11330794516586144154189655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15107726022114858872252873 11330794516586144154189655)
      ·
        refine ⟨16996191774879216231284483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11330794516586144154189655 16996191774879216231284483)
        ·
          refine ⟨25494287662318824346926725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16996191774879216231284483 25494287662318824346926725)
          ·
            refine ⟨4780178936684779565048761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25494287662318824346926725 4780178936684779565048761)
            ·
              refine ⟨3585134202513584673786571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4780178936684779565048761 3585134202513584673786571)
              ·
                refine ⟨5377701303770377010679857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3585134202513584673786571 5377701303770377010679857)
                ·
                  refine ⟨4033275977827782758009893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5377701303770377010679857 4033275977827782758009893)
                  ·
                    refine ⟨756239245842709267126855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4033275977827782758009893 756239245842709267126855)
                    ·
                      rfl

theorem cell22_2209156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_2209156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209156 prefixEnd_2209156 := by exact prefixLift 2209156
  have htrace : WordTrace (prefixWord ++ tailWord_2209156) baseStart_2209156 baseEnd_2209156 := by
    simpa [prefixWord, tailWord_2209156, baseEnd_2209156] using wordTrace_append hprefix tailTrace_2209156
  have hstable : (prefixWord ++ tailWord_2209156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209156).length < 2 ^ (prefixWord ++ tailWord_2209156).sum := by decide
  have hdescent : baseEnd_2209156 < baseStart_2209156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209169 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 5, 3]
def baseStart_2209169 : Nat := 118140960795 + 2209169 * 2 ^ 59
def prefixEnd_2209169 : Nat := 4983230072969 + 3 ^ 40 * 2209169 * 2
def baseEnd_2209169 : Nat := 756243696008381566551815

theorem tailTrace_2209169 : CollatzResearch.WordTrace tailWord_2209169 prefixEnd_2209169 756243696008381566551815 := by
  unfold tailWord_2209169
  simp only [CollatzResearch.WordTrace]
  refine ⟨80575012933565483872238561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53716675289043655914825707 80575012933565483872238561)
  ·
    refine ⟨60431259700174112904178921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80575012933565483872238561 60431259700174112904178921)
    ·
      refine ⟨45323444775130584678134191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60431259700174112904178921 45323444775130584678134191)
      ·
        refine ⟨67985167162695877017201287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45323444775130584678134191 67985167162695877017201287)
        ·
          refine ⟨101977750744043815525801931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67985167162695877017201287 101977750744043815525801931)
          ·
            refine ⟨152966626116065723288702897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101977750744043815525801931 152966626116065723288702897)
            ·
              refine ⟨114724969587049292466527173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152966626116065723288702897 114724969587049292466527173)
              ·
                refine ⟨21510931797571742337473845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114724969587049292466527173 21510931797571742337473845)
                ·
                  refine ⟨2016649856022350844138173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21510931797571742337473845 2016649856022350844138173)
                  ·
                    refine ⟨756243696008381566551815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016649856022350844138173 756243696008381566551815)
                    ·
                      rfl

theorem cell22_2209169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_2209169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209169 prefixEnd_2209169 := by exact prefixLift 2209169
  have htrace : WordTrace (prefixWord ++ tailWord_2209169) baseStart_2209169 baseEnd_2209169 := by
    simpa [prefixWord, tailWord_2209169, baseEnd_2209169] using wordTrace_append hprefix tailTrace_2209169
  have hstable : (prefixWord ++ tailWord_2209169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209169).length < 2 ^ (prefixWord ++ tailWord_2209169).sum := by decide
  have hdescent : baseEnd_2209169 < baseStart_2209169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209214 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2209214 : Nat := 118140960795 + 2209214 * 2 ^ 59
def prefixEnd_2209214 : Nat := 4983230072969 + 3 ^ 40 * 2209214 * 2
def baseEnd_2209214 : Nat := 756259100428016449176677

theorem tailTrace_2209214 : CollatzResearch.WordTrace tailWord_2209214 prefixEnd_2209214 756259100428016449176677 := by
  unfold tailWord_2209214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10072081777300307069703337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53717769478934971038417797 10072081777300307069703337)
  ·
    refine ⟨7554061332975230302277503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10072081777300307069703337 7554061332975230302277503)
    ·
      refine ⟨11331091999462845453416255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7554061332975230302277503 11331091999462845453416255)
      ·
        refine ⟨16996637999194268180124383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11331091999462845453416255 16996637999194268180124383)
        ·
          refine ⟨25494956998791402270186575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16996637999194268180124383 25494956998791402270186575)
          ·
            refine ⟨38242435498187103405279863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25494956998791402270186575 38242435498187103405279863)
            ·
              refine ⟨57363653247280655107919795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38242435498187103405279863 57363653247280655107919795)
              ·
                refine ⟨86045479870920982661879693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57363653247280655107919795 86045479870920982661879693)
                ·
                  refine ⟨32267054951595368498204885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86045479870920982661879693 32267054951595368498204885)
                  ·
                    refine ⟨756259100428016449176677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32267054951595368498204885 756259100428016449176677)
                    ·
                      rfl

theorem cell22_2209214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2209214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209214 prefixEnd_2209214 := by exact prefixLift 2209214
  have htrace : WordTrace (prefixWord ++ tailWord_2209214) baseStart_2209214 baseEnd_2209214 := by
    simpa [prefixWord, tailWord_2209214, baseEnd_2209214] using wordTrace_append hprefix tailTrace_2209214
  have hstable : (prefixWord ++ tailWord_2209214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209214).length < 2 ^ (prefixWord ++ tailWord_2209214).sum := by decide
  have hdescent : baseEnd_2209214 < baseStart_2209214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209220 : List Nat := [2, 3, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2209220 : Nat := 118140960795 + 2209220 * 2 ^ 59
def prefixEnd_2209220 : Nat := 4983230072969 + 3 ^ 40 * 2209220 * 2
def baseEnd_2209220 : Nat := 756261154350634433526659

theorem tailTrace_2209220 : CollatzResearch.WordTrace tailWord_2209220 prefixEnd_2209220 756261154350634433526659 := by
  unfold tailWord_2209220
  simp only [CollatzResearch.WordTrace]
  refine ⟨40288436528190359791172557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53717915370920479721563409 40288436528190359791172557)
  ·
    refine ⟨15108163698071384921689709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40288436528190359791172557 15108163698071384921689709)
    ·
      refine ⟨5665561386776769345633641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15108163698071384921689709 5665561386776769345633641)
      ·
        refine ⟨4249171040082577009225231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5665561386776769345633641 4249171040082577009225231)
        ·
          refine ⟨6373756560123865513837847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249171040082577009225231 6373756560123865513837847)
          ·
            refine ⟨9560634840185798270756771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6373756560123865513837847 9560634840185798270756771)
            ·
              refine ⟨14340952260278697406135157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9560634840185798270756771 14340952260278697406135157)
              ·
                refine ⟨1344464274401127881825171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14340952260278697406135157 1344464274401127881825171)
                ·
                  refine ⟨2016696411601691822737757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344464274401127881825171 2016696411601691822737757)
                  ·
                    refine ⟨756261154350634433526659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016696411601691822737757 756261154350634433526659)
                    ·
                      rfl

theorem cell22_2209220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2209220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209220 prefixEnd_2209220 := by exact prefixLift 2209220
  have htrace : WordTrace (prefixWord ++ tailWord_2209220) baseStart_2209220 baseEnd_2209220 := by
    simpa [prefixWord, tailWord_2209220, baseEnd_2209220] using wordTrace_append hprefix tailTrace_2209220
  have hstable : (prefixWord ++ tailWord_2209220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209220).length < 2 ^ (prefixWord ++ tailWord_2209220).sum := by decide
  have hdescent : baseEnd_2209220 < baseStart_2209220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209259 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 1, 5]
def baseStart_2209259 : Nat := 118140960795 + 2209259 * 2 ^ 59
def prefixEnd_2209259 : Nat := 4983230072969 + 3 ^ 40 * 2209259 * 2
def baseEnd_2209259 : Nat := 756274504847651331801539

theorem tailTrace_2209259 : CollatzResearch.WordTrace tailWord_2209259 prefixEnd_2209259 756274504847651331801539 := by
  unfold tailWord_2209259
  simp only [CollatzResearch.WordTrace]
  refine ⟨80578295503239429243014831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53718863668826286162009887 80578295503239429243014831)
  ·
    refine ⟨120867443254859143864522247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80578295503239429243014831 120867443254859143864522247)
    ·
      refine ⟨181301164882288715796783371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120867443254859143864522247 181301164882288715796783371)
      ·
        refine ⟨271951747323433073695175057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181301164882288715796783371 271951747323433073695175057)
        ·
          refine ⟨203963810492574805271381293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271951747323433073695175057 203963810492574805271381293)
          ·
            refine ⟨76486428934715551976767985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203963810492574805271381293 76486428934715551976767985)
            ·
              refine ⟨57364821701036663982575989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76486428934715551976767985 57364821701036663982575989)
              ·
                refine ⟨5377952034472187248366499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57364821701036663982575989 5377952034472187248366499)
                ·
                  refine ⟨8066928051708280872549749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5377952034472187248366499 8066928051708280872549749)
                  ·
                    refine ⟨756274504847651331801539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8066928051708280872549749 756274504847651331801539)
                    ·
                      rfl

theorem cell22_2209259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_2209259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209259 prefixEnd_2209259 := by exact prefixLift 2209259
  have htrace : WordTrace (prefixWord ++ tailWord_2209259) baseStart_2209259 baseEnd_2209259 := by
    simpa [prefixWord, tailWord_2209259, baseEnd_2209259] using wordTrace_append hprefix tailTrace_2209259
  have hstable : (prefixWord ++ tailWord_2209259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209259).length < 2 ^ (prefixWord ++ tailWord_2209259).sum := by decide
  have hdescent : baseEnd_2209259 < baseStart_2209259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209274 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_2209274 : Nat := 118140960795 + 2209274 * 2 ^ 59
def prefixEnd_2209274 : Nat := 4983230072969 + 3 ^ 40 * 2209274 * 2
def baseEnd_2209274 : Nat := 756279639654196292676493

theorem tailTrace_2209274 : CollatzResearch.WordTrace tailWord_2209274 prefixEnd_2209274 756279639654196292676493 := by
  unfold tailWord_2209274
  simp only [CollatzResearch.WordTrace]
  refine ⟨20144710649546271701202719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53719228398790057869873917 20144710649546271701202719)
  ·
    refine ⟨30217065974319407551804079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20144710649546271701202719 30217065974319407551804079)
    ·
      refine ⟨45325598961479111327706119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30217065974319407551804079 45325598961479111327706119)
      ·
        refine ⟨67988398442218666991559179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45325598961479111327706119 67988398442218666991559179)
        ·
          refine ⟨101982597663328000487338769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67988398442218666991559179 101982597663328000487338769)
          ·
            refine ⟨76486948247496000365504077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101982597663328000487338769 76486948247496000365504077)
            ·
              refine ⟨28682605592811000137064029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76486948247496000365504077 28682605592811000137064029)
              ·
                refine ⟨10755977097304125051399011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28682605592811000137064029 10755977097304125051399011)
                ·
                  refine ⟨16133965645956187577098517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10755977097304125051399011 16133965645956187577098517)
                  ·
                    refine ⟨756279639654196292676493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16133965645956187577098517 756279639654196292676493)
                    ·
                      rfl

theorem cell22_2209274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_2209274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209274 prefixEnd_2209274 := by exact prefixLift 2209274
  have htrace : WordTrace (prefixWord ++ tailWord_2209274) baseStart_2209274 baseEnd_2209274 := by
    simpa [prefixWord, tailWord_2209274, baseEnd_2209274] using wordTrace_append hprefix tailTrace_2209274
  have hstable : (prefixWord ++ tailWord_2209274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209274).length < 2 ^ (prefixWord ++ tailWord_2209274).sum := by decide
  have hdescent : baseEnd_2209274 < baseStart_2209274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209276 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_2209276 : Nat := 118140960795 + 2209276 * 2 ^ 59
def prefixEnd_2209276 : Nat := 4983230072969 + 3 ^ 40 * 2209276 * 2
def baseEnd_2209276 : Nat := 756280324295068954126487

theorem tailTrace_2209276 : CollatzResearch.WordTrace tailWord_2209276 prefixEnd_2209276 756280324295068954126487 := by
  unfold tailWord_2209276
  simp only [CollatzResearch.WordTrace]
  refine ⟨40289457772088920573191841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53719277029451894097589121 40289457772088920573191841)
  ·
    refine ⟨30217093329066690429893881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40289457772088920573191841 30217093329066690429893881)
    ·
      refine ⟨22662819996800017822420411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30217093329066690429893881 22662819996800017822420411)
      ·
        refine ⟨33994229995200026733630617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22662819996800017822420411 33994229995200026733630617)
        ·
          refine ⟨25495672496400020050222963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33994229995200026733630617 25495672496400020050222963)
          ·
            refine ⟨38243508744600030075334445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25495672496400020050222963 38243508744600030075334445)
            ·
              refine ⟨14341315779225011278250417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38243508744600030075334445 14341315779225011278250417)
              ·
                refine ⟨10755986834418758458687813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14341315779225011278250417 10755986834418758458687813)
                ·
                  refine ⟨2016747531453517211003965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10755986834418758458687813 2016747531453517211003965)
                  ·
                    refine ⟨756280324295068954126487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016747531453517211003965 756280324295068954126487)
                    ·
                      rfl

theorem cell22_2209276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_2209276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209276 prefixEnd_2209276 := by exact prefixLift 2209276
  have htrace : WordTrace (prefixWord ++ tailWord_2209276) baseStart_2209276 baseEnd_2209276 := by
    simpa [prefixWord, tailWord_2209276, baseEnd_2209276] using wordTrace_append hprefix tailTrace_2209276
  have hstable : (prefixWord ++ tailWord_2209276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209276).length < 2 ^ (prefixWord ++ tailWord_2209276).sum := by decide
  have hdescent : baseEnd_2209276 < baseStart_2209276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209413 : List Nat := [1, 3, 1, 1, 4, 1, 1, 6, 4]
def baseStart_2209413 : Nat := 118140960795 + 2209413 * 2 ^ 59
def prefixEnd_2209413 : Nat := 4983230072969 + 3 ^ 40 * 2209413 * 2
def baseEnd_2209413 : Nat := 252109074064948754483689

theorem tailTrace_2209413 : CollatzResearch.WordTrace tailWord_2209413 prefixEnd_2209413 252109074064948754483689 := by
  unfold tailWord_2209413
  simp only [CollatzResearch.WordTrace]
  refine ⟨80583912344681513544120893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53722608229787675696080595 80583912344681513544120893)
  ·
    refine ⟨30218967129255567579045335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80583912344681513544120893 30218967129255567579045335)
    ·
      refine ⟨45328450693883351368568003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30218967129255567579045335 45328450693883351368568003)
      ·
        refine ⟨67992676040825027052852005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45328450693883351368568003 67992676040825027052852005)
        ·
          refine ⟨12748626757654692572409751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67992676040825027052852005 12748626757654692572409751)
          ·
            refine ⟨19122940136482038858614627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12748626757654692572409751 19122940136482038858614627)
            ·
              refine ⟨28684410204723058287921941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19122940136482038858614627 28684410204723058287921941)
              ·
                refine ⟨1344581728346393357246341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28684410204723058287921941 1344581728346393357246341)
                ·
                  refine ⟨252109074064948754483689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1344581728346393357246341 252109074064948754483689)
                  ·
                    rfl

theorem cell22_2209413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_2209413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209413 prefixEnd_2209413 := by exact prefixLift 2209413
  have htrace : WordTrace (prefixWord ++ tailWord_2209413) baseStart_2209413 baseEnd_2209413 := by
    simpa [prefixWord, tailWord_2209413, baseEnd_2209413] using wordTrace_append hprefix tailTrace_2209413
  have hstable : (prefixWord ++ tailWord_2209413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209413).length < 2 ^ (prefixWord ++ tailWord_2209413).sum := by decide
  have hdescent : baseEnd_2209413 < baseStart_2209413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209462 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2209462 : Nat := 118140960795 + 2209462 * 2 ^ 59
def prefixEnd_2209462 : Nat := 4983230072969 + 3 ^ 40 * 2209462 * 2
def baseEnd_2209462 : Nat := 756343995896226468975917

theorem tailTrace_2209462 : CollatzResearch.WordTrace tailWord_2209462 prefixEnd_2209462 756343995896226468975917 := by
  unfold tailWord_2209462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036606220093999682040915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53723799681002663275103093 5036606220093999682040915)
  ·
    refine ⟨7554909330140999523061373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5036606220093999682040915 7554909330140999523061373)
    ·
      refine ⟨2833090998802874821148015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7554909330140999523061373 2833090998802874821148015)
      ·
        refine ⟨4249636498204312231722023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2833090998802874821148015 4249636498204312231722023)
        ·
          refine ⟨6374454747306468347583035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249636498204312231722023 6374454747306468347583035)
          ·
            refine ⟨9561682120959702521374553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6374454747306468347583035 9561682120959702521374553)
            ·
              refine ⟨7171261590719776891030915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9561682120959702521374553 7171261590719776891030915)
              ·
                refine ⟨10756892386079665336546373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171261590719776891030915 10756892386079665336546373)
                ·
                  refine ⟨2016917322389937250602445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10756892386079665336546373 2016917322389937250602445)
                  ·
                    refine ⟨756343995896226468975917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016917322389937250602445 756343995896226468975917)
                    ·
                      rfl

theorem cell22_2209462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2209462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209462 prefixEnd_2209462 := by exact prefixLift 2209462
  have htrace : WordTrace (prefixWord ++ tailWord_2209462) baseStart_2209462 baseEnd_2209462 := by
    simpa [prefixWord, tailWord_2209462, baseEnd_2209462] using wordTrace_append hprefix tailTrace_2209462
  have hstable : (prefixWord ++ tailWord_2209462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209462).length < 2 ^ (prefixWord ++ tailWord_2209462).sum := by decide
  have hdescent : baseEnd_2209462 < baseStart_2209462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209471 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 2, 6]
def baseStart_2209471 : Nat := 118140960795 + 2209471 * 2 ^ 59
def prefixEnd_2209471 : Nat := 4983230072969 + 3 ^ 40 * 2209471 * 2
def baseEnd_2209471 : Nat := 756347076780153445500889

theorem tailTrace_2209471 : CollatzResearch.WordTrace tailWord_2209471 prefixEnd_2209471 756347076780153445500889 := by
  unfold tailWord_2209471
  simp only [CollatzResearch.WordTrace]
  refine ⟨80586027778471389449732267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53724018518980926299821511 80586027778471389449732267)
  ·
    refine ⟨120879041667707084174598401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80586027778471389449732267 120879041667707084174598401)
    ·
      refine ⟨90659281250780313130948801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120879041667707084174598401 90659281250780313130948801)
      ·
        refine ⟨67994460938085234848211601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90659281250780313130948801 67994460938085234848211601)
        ·
          refine ⟨50995845703563926136158701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67994460938085234848211601 50995845703563926136158701)
          ·
            refine ⟨19123442138836472301059513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50995845703563926136158701 19123442138836472301059513)
            ·
              refine ⟨14342581604127354225794635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19123442138836472301059513 14342581604127354225794635)
              ·
                refine ⟨21513872406191031338691953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14342581604127354225794635 21513872406191031338691953)
                ·
                  refine ⟨16135404304643273504018965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21513872406191031338691953 16135404304643273504018965)
                  ·
                    refine ⟨756347076780153445500889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16135404304643273504018965 756347076780153445500889)
                    ·
                      rfl

theorem cell22_2209471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_2209471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209471 prefixEnd_2209471 := by exact prefixLift 2209471
  have htrace : WordTrace (prefixWord ++ tailWord_2209471) baseStart_2209471 baseEnd_2209471 := by
    simpa [prefixWord, tailWord_2209471, baseEnd_2209471] using wordTrace_append hprefix tailTrace_2209471
  have hstable : (prefixWord ++ tailWord_2209471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209471).length < 2 ^ (prefixWord ++ tailWord_2209471).sum := by decide
  have hdescent : baseEnd_2209471 < baseStart_2209471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209494 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2209494 : Nat := 118140960795 + 2209494 * 2 ^ 59
def prefixEnd_2209494 : Nat := 4983230072969 + 3 ^ 40 * 2209494 * 2
def baseEnd_2209494 : Nat := 756354950150189052175819

theorem tailTrace_2209494 : CollatzResearch.WordTrace tailWord_2209494 prefixEnd_2209494 756354950150189052175819 := by
  unfold tailWord_2209494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036679166086754023613721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53724577771592042918546357 5036679166086754023613721)
  ·
    refine ⟨3777509374565065517710291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5036679166086754023613721 3777509374565065517710291)
    ·
      refine ⟨5666264061847598276565437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3777509374565065517710291 5666264061847598276565437)
      ·
        refine ⟨2124849023192849353712039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5666264061847598276565437 2124849023192849353712039)
        ·
          refine ⟨3187273534789274030568059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2124849023192849353712039 3187273534789274030568059)
          ·
            refine ⟨4780910302183911045852089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187273534789274030568059 4780910302183911045852089)
            ·
              refine ⟨3585682726637933284389067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4780910302183911045852089 3585682726637933284389067)
              ·
                refine ⟨5378524089956899926583601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3585682726637933284389067 5378524089956899926583601)
                ·
                  refine ⟨4033893067467674944937701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5378524089956899926583601 4033893067467674944937701)
                  ·
                    refine ⟨756354950150189052175819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4033893067467674944937701 756354950150189052175819)
                    ·
                      rfl

theorem cell22_2209494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2209494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209494 prefixEnd_2209494 := by exact prefixLift 2209494
  have htrace : WordTrace (prefixWord ++ tailWord_2209494) baseStart_2209494 baseEnd_2209494 := by
    simpa [prefixWord, tailWord_2209494, baseEnd_2209494] using wordTrace_append hprefix tailTrace_2209494
  have hstable : (prefixWord ++ tailWord_2209494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209494).length < 2 ^ (prefixWord ++ tailWord_2209494).sum := by decide
  have hdescent : baseEnd_2209494 < baseStart_2209494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209518 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2209518 : Nat := 118140960795 + 2209518 * 2 ^ 59
def prefixEnd_2209518 : Nat := 4983230072969 + 3 ^ 40 * 2209518 * 2
def baseEnd_2209518 : Nat := 756363165840660989575745

theorem tailTrace_2209518 : CollatzResearch.WordTrace tailWord_2209518 prefixEnd_2209518 756363165840660989575745 := by
  unfold tailWord_2209518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10073467751162639559586651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53725161339534077651128805 10073467751162639559586651)
  ·
    refine ⟨15110201626743959339379977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10073467751162639559586651 15110201626743959339379977)
    ·
      refine ⟨11332651220057969504534983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15110201626743959339379977 11332651220057969504534983)
      ·
        refine ⟨16998976830086954256802475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11332651220057969504534983 16998976830086954256802475)
        ·
          refine ⟨25498465245130431385203713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16998976830086954256802475 25498465245130431385203713)
          ·
            refine ⟨19123848933847823538902785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25498465245130431385203713 19123848933847823538902785)
            ·
              refine ⟨14342886700385867654177089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19123848933847823538902785 14342886700385867654177089)
              ·
                refine ⟨10757165025289400740632817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14342886700385867654177089 10757165025289400740632817)
                ·
                  refine ⟨8067873768967050555474613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10757165025289400740632817 8067873768967050555474613)
                  ·
                    refine ⟨756363165840660989575745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8067873768967050555474613 756363165840660989575745)
                    ·
                      rfl

theorem cell22_2209518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2209518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209518 prefixEnd_2209518 := by exact prefixLift 2209518
  have htrace : WordTrace (prefixWord ++ tailWord_2209518) baseStart_2209518 baseEnd_2209518 := by
    simpa [prefixWord, tailWord_2209518, baseEnd_2209518] using wordTrace_append hprefix tailTrace_2209518
  have hstable : (prefixWord ++ tailWord_2209518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209518).length < 2 ^ (prefixWord ++ tailWord_2209518).sum := by decide
  have hdescent : baseEnd_2209518 < baseStart_2209518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209563 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 6, 3]
def baseStart_2209563 : Nat := 118140960795 + 2209563 * 2 ^ 59
def prefixEnd_2209563 : Nat := 4983230072969 + 3 ^ 40 * 2209563 * 2
def baseEnd_2209563 : Nat := 756378570260295872200607

theorem tailTrace_2209563 : CollatzResearch.WordTrace tailWord_2209563 prefixEnd_2209563 756378570260295872200607 := by
  unfold tailWord_2209563
  simp only [CollatzResearch.WordTrace]
  refine ⟨80589383294138089162081343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53726255529425392774720895 80589383294138089162081343)
  ·
    refine ⟨120884074941207133743122015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80589383294138089162081343 120884074941207133743122015)
    ·
      refine ⟨181326112411810700614683023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120884074941207133743122015 181326112411810700614683023)
      ·
        refine ⟨271989168617716050922024535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181326112411810700614683023 271989168617716050922024535)
        ·
          refine ⟨407983752926574076383036803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271989168617716050922024535 407983752926574076383036803)
          ·
            refine ⟨611975629389861114574555205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407983752926574076383036803 611975629389861114574555205)
            ·
              refine ⟨114745430510598958982729101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 611975629389861114574555205 114745430510598958982729101)
              ·
                refine ⟨43029536441474609618523413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114745430510598958982729101 43029536441474609618523413)
                ·
                  refine ⟨2017009520694122325868285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43029536441474609618523413 2017009520694122325868285)
                  ·
                    refine ⟨756378570260295872200607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017009520694122325868285 756378570260295872200607)
                    ·
                      rfl

theorem cell22_2209563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 3].length) (baseStart_2209563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209563 prefixEnd_2209563 := by exact prefixLift 2209563
  have htrace : WordTrace (prefixWord ++ tailWord_2209563) baseStart_2209563 baseEnd_2209563 := by
    simpa [prefixWord, tailWord_2209563, baseEnd_2209563] using wordTrace_append hprefix tailTrace_2209563
  have hstable : (prefixWord ++ tailWord_2209563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209563).length < 2 ^ (prefixWord ++ tailWord_2209563).sum := by decide
  have hdescent : baseEnd_2209563 < baseStart_2209563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209580 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_2209580 : Nat := 118140960795 + 2209580 * 2 ^ 59
def prefixEnd_2209580 : Nat := 4983230072969 + 3 ^ 40 * 2209580 * 2
def baseEnd_2209580 : Nat := 756384389707713494525555

theorem tailTrace_2209580 : CollatzResearch.WordTrace tailWord_2209580 prefixEnd_2209580 756384389707713494525555 := by
  unfold tailWord_2209580
  simp only [CollatzResearch.WordTrace]
  refine ⟨40295001667538250532725097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53726668890051000710300129 40295001667538250532725097)
  ·
    refine ⟨30221251250653687899543823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40295001667538250532725097 30221251250653687899543823)
    ·
      refine ⟨45331876875980531849315735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30221251250653687899543823 45331876875980531849315735)
      ·
        refine ⟨67997815313970797773973603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45331876875980531849315735 67997815313970797773973603)
        ·
          refine ⟨101996722970956196660960405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67997815313970797773973603 101996722970956196660960405)
          ·
            refine ⟨4781096389263571718482519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101996722970956196660960405 4781096389263571718482519)
            ·
              refine ⟨7171644583895357577723779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4781096389263571718482519 7171644583895357577723779)
              ·
                refine ⟨10757466875843036366585669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171644583895357577723779 10757466875843036366585669)
                ·
                  refine ⟨2017025039220569318734813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10757466875843036366585669 2017025039220569318734813)
                  ·
                    refine ⟨756384389707713494525555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017025039220569318734813 756384389707713494525555)
                    ·
                      rfl

theorem cell22_2209580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_2209580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209580 prefixEnd_2209580 := by exact prefixLift 2209580
  have htrace : WordTrace (prefixWord ++ tailWord_2209580) baseStart_2209580 baseEnd_2209580 := by
    simpa [prefixWord, tailWord_2209580, baseEnd_2209580] using wordTrace_append hprefix tailTrace_2209580
  have hstable : (prefixWord ++ tailWord_2209580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209580).length < 2 ^ (prefixWord ++ tailWord_2209580).sum := by decide
  have hdescent : baseEnd_2209580 < baseStart_2209580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209582 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_2209582 : Nat := 118140960795 + 2209582 * 2 ^ 59
def prefixEnd_2209582 : Nat := 4983230072969 + 3 ^ 40 * 2209582 * 2
def baseEnd_2209582 : Nat := 252128358116195385325183

theorem tailTrace_2209582 : CollatzResearch.WordTrace tailWord_2209582 prefixEnd_2209582 252128358116195385325183 := by
  unfold tailWord_2209582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10073759535133656925877875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53726717520712836938015333 10073759535133656925877875)
  ·
    refine ⟨15110639302700485388816813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10073759535133656925877875 15110639302700485388816813)
    ·
      refine ⟨5666489738512682020806305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15110639302700485388816813 5666489738512682020806305)
      ·
        refine ⟨4249867303884511515604729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5666489738512682020806305 4249867303884511515604729)
        ·
          refine ⟨3187400477913383636703547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4249867303884511515604729 3187400477913383636703547)
          ·
            refine ⟨4781100716870075455055321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187400477913383636703547 4781100716870075455055321)
            ·
              refine ⟨3585825537652556591291491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4781100716870075455055321 3585825537652556591291491)
              ·
                refine ⟨5378738306478834886937237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3585825537652556591291491 5378738306478834886937237)
                ·
                  refine ⟨252128358116195385325183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5378738306478834886937237 252128358116195385325183)
                  ·
                    rfl

theorem cell22_2209582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_2209582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209582 prefixEnd_2209582 := by exact prefixLift 2209582
  have htrace : WordTrace (prefixWord ++ tailWord_2209582) baseStart_2209582 baseEnd_2209582 := by
    simpa [prefixWord, tailWord_2209582, baseEnd_2209582] using wordTrace_append hprefix tailTrace_2209582
  have hstable : (prefixWord ++ tailWord_2209582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209582).length < 2 ^ (prefixWord ++ tailWord_2209582).sum := by decide
  have hdescent : baseEnd_2209582 < baseStart_2209582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209597 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_2209597 : Nat := 118140960795 + 2209597 * 2 ^ 59
def prefixEnd_2209597 : Nat := 4983230072969 + 3 ^ 40 * 2209597 * 2
def baseEnd_2209597 : Nat := 756390209155131116850503

theorem tailTrace_2209597 : CollatzResearch.WordTrace tailWord_2209597 prefixEnd_2209597 756390209155131116850503 := by
  unfold tailWord_2209597
  simp only [CollatzResearch.WordTrace]
  refine ⟨80590623376014912968819045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53727082250676608645879363 80590623376014912968819045)
  ·
    refine ⟨15110741883002796181653571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80590623376014912968819045 15110741883002796181653571)
    ·
      refine ⟨22666112824504194272480357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15110741883002796181653571 22666112824504194272480357)
      ·
        refine ⟨4249896154594536426090067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22666112824504194272480357 4249896154594536426090067)
        ·
          refine ⟨6374844231891804639135101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249896154594536426090067 6374844231891804639135101)
          ·
            refine ⟨2390566586959426739675663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6374844231891804639135101 2390566586959426739675663)
            ·
              refine ⟨3585849880439140109513495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2390566586959426739675663 3585849880439140109513495)
              ·
                refine ⟨5378774820658710164270243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3585849880439140109513495 5378774820658710164270243)
                ·
                  refine ⟨8068162230988065246405365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5378774820658710164270243 8068162230988065246405365)
                  ·
                    refine ⟨756390209155131116850503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8068162230988065246405365 756390209155131116850503)
                    ·
                      rfl

theorem cell22_2209597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_2209597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209597 prefixEnd_2209597 := by exact prefixLift 2209597
  have htrace : WordTrace (prefixWord ++ tailWord_2209597) baseStart_2209597 baseEnd_2209597 := by
    simpa [prefixWord, tailWord_2209597, baseEnd_2209597] using wordTrace_append hprefix tailTrace_2209597
  have hstable : (prefixWord ++ tailWord_2209597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209597).length < 2 ^ (prefixWord ++ tailWord_2209597).sum := by decide
  have hdescent : baseEnd_2209597 < baseStart_2209597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209704 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2209704 : Nat := 118140960795 + 2209704 * 2 ^ 59
def prefixEnd_2209704 : Nat := 4983230072969 + 3 ^ 40 * 2209704 * 2
def baseEnd_2209704 : Nat := 756426837441818504425175

theorem tailTrace_2209704 : CollatzResearch.WordTrace tailWord_2209704 prefixEnd_2209704 756426837441818504425175 := by
  unfold tailWord_2209704
  simp only [CollatzResearch.WordTrace]
  refine ⟨40297262993313635121482083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53729683991084846828642777 40297262993313635121482083)
  ·
    refine ⟨60445894489970452682223125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40297262993313635121482083 60445894489970452682223125)
    ·
      refine ⟨2833401304217364969479209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60445894489970452682223125 2833401304217364969479209)
      ·
        refine ⟨2125050978163023727109407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2833401304217364969479209 2125050978163023727109407)
        ·
          refine ⟨3187576467244535590664111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125050978163023727109407 3187576467244535590664111)
          ·
            refine ⟨4781364700866803385996167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187576467244535590664111 4781364700866803385996167)
            ·
              refine ⟨7172047051300205078994251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4781364700866803385996167 7172047051300205078994251)
              ·
                refine ⟨10758070576950307618491377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7172047051300205078994251 10758070576950307618491377)
                ·
                  refine ⟨8068552932712730713868533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10758070576950307618491377 8068552932712730713868533)
                  ·
                    refine ⟨756426837441818504425175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8068552932712730713868533 756426837441818504425175)
                    ·
                      rfl

theorem cell22_2209704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2209704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209704 prefixEnd_2209704 := by exact prefixLift 2209704
  have htrace : WordTrace (prefixWord ++ tailWord_2209704) baseStart_2209704 baseEnd_2209704 := by
    simpa [prefixWord, tailWord_2209704, baseEnd_2209704] using wordTrace_append hprefix tailTrace_2209704
  have hstable : (prefixWord ++ tailWord_2209704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209704).length < 2 ^ (prefixWord ++ tailWord_2209704).sum := by decide
  have hdescent : baseEnd_2209704 < baseStart_2209704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209715 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 1, 5]
def baseStart_2209715 : Nat := 118140960795 + 2209715 * 2 ^ 59
def prefixEnd_2209715 : Nat := 4983230072969 + 3 ^ 40 * 2209715 * 2
def baseEnd_2209715 : Nat := 756430602966618142400141

theorem tailTrace_2209715 : CollatzResearch.WordTrace tailWord_2209715 prefixEnd_2209715 756430602966618142400141 := by
  unfold tailWord_2209715
  simp only [CollatzResearch.WordTrace]
  refine ⟨80594927189587419121614599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53729951459724946081076399 80594927189587419121614599)
  ·
    refine ⟨120892390784381128682421899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80594927189587419121614599 120892390784381128682421899)
    ·
      refine ⟨181338586176571693023632849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120892390784381128682421899 181338586176571693023632849)
      ·
        refine ⟨136003939632428769767724637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181338586176571693023632849 136003939632428769767724637)
        ·
          refine ⟨51001477362160788662896739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136003939632428769767724637 51001477362160788662896739)
          ·
            refine ⟨76502216043241182994345109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51001477362160788662896739 76502216043241182994345109)
            ·
              refine ⟨3586041377026930452859927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76502216043241182994345109 3586041377026930452859927)
              ·
                refine ⟨5379062065540395679289891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586041377026930452859927 5379062065540395679289891)
                ·
                  refine ⟨8068593098310593518934837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5379062065540395679289891 8068593098310593518934837)
                  ·
                    refine ⟨756430602966618142400141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8068593098310593518934837 756430602966618142400141)
                    ·
                      rfl

theorem cell22_2209715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 5].length) (baseStart_2209715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209715 prefixEnd_2209715 := by exact prefixLift 2209715
  have htrace : WordTrace (prefixWord ++ tailWord_2209715) baseStart_2209715 baseEnd_2209715 := by
    simpa [prefixWord, tailWord_2209715, baseEnd_2209715] using wordTrace_append hprefix tailTrace_2209715
  have hstable : (prefixWord ++ tailWord_2209715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209715).length < 2 ^ (prefixWord ++ tailWord_2209715).sum := by decide
  have hdescent : baseEnd_2209715 < baseStart_2209715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209749 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_2209749 : Nat := 118140960795 + 2209749 * 2 ^ 59
def prefixEnd_2209749 : Nat := 4983230072969 + 3 ^ 40 * 2209749 * 2
def baseEnd_2209749 : Nat := 756442241861453387050037

theorem tailTrace_2209749 : CollatzResearch.WordTrace tailWord_2209749 prefixEnd_2209749 756442241861453387050037 := by
  unfold tailWord_2209749
  simp only [CollatzResearch.WordTrace]
  refine ⟨80596167271464242928352301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53730778180976161952234867 80596167271464242928352301)
  ·
    refine ⟨30223562726799091098132113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80596167271464242928352301 30223562726799091098132113)
    ·
      refine ⟨22667672045099318323599085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30223562726799091098132113 22667672045099318323599085)
      ·
        refine ⟨8500377016912244371349657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22667672045099318323599085 8500377016912244371349657)
        ·
          refine ⟨6375282762684183278512243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8500377016912244371349657 6375282762684183278512243)
          ·
            refine ⟨9562924144026274917768365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6375282762684183278512243 9562924144026274917768365)
            ·
              refine ⟨3586096554009853094163137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9562924144026274917768365 3586096554009853094163137)
              ·
                refine ⟨2689572415507389820622353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3586096554009853094163137 2689572415507389820622353)
                ·
                  refine ⟨2017179311630542365466765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2689572415507389820622353 2017179311630542365466765)
                  ·
                    refine ⟨756442241861453387050037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017179311630542365466765 756442241861453387050037)
                    ·
                      rfl

theorem cell22_2209749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_2209749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209749 prefixEnd_2209749 := by exact prefixLift 2209749
  have htrace : WordTrace (prefixWord ++ tailWord_2209749) baseStart_2209749 baseEnd_2209749 := by
    simpa [prefixWord, tailWord_2209749, baseEnd_2209749] using wordTrace_append hprefix tailTrace_2209749
  have hstable : (prefixWord ++ tailWord_2209749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209749).length < 2 ^ (prefixWord ++ tailWord_2209749).sum := by decide
  have hdescent : baseEnd_2209749 < baseStart_2209749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209884 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2209884 : Nat := 118140960795 + 2209884 * 2 ^ 59
def prefixEnd_2209884 : Nat := 4983230072969 + 3 ^ 40 * 2209884 * 2
def baseEnd_2209884 : Nat := 756488455120358034924623

theorem tailTrace_2209884 : CollatzResearch.WordTrace tailWord_2209884 prefixEnd_2209884 756488455120358034924623 := by
  unfold tailWord_2209884
  simp only [CollatzResearch.WordTrace]
  refine ⟨40300545562987580492258353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53734060750650107323011137 40300545562987580492258353)
  ·
    refine ⟨30225409172240685369193765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40300545562987580492258353 30225409172240685369193765)
    ·
      refine ⟨5667264219795128506723831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30225409172240685369193765 5667264219795128506723831)
      ·
        refine ⟨8500896329692692760085747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5667264219795128506723831 8500896329692692760085747)
        ·
          refine ⟨12751344494539039140128621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8500896329692692760085747 12751344494539039140128621)
          ·
            refine ⟨4781754185452139677548233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12751344494539039140128621 4781754185452139677548233)
            ·
              refine ⟨3586315639089104758161175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4781754185452139677548233 3586315639089104758161175)
              ·
                refine ⟨5379473458633657137241763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586315639089104758161175 5379473458633657137241763)
                ·
                  refine ⟨8069210187950485705862645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5379473458633657137241763 8069210187950485705862645)
                  ·
                    refine ⟨756488455120358034924623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8069210187950485705862645 756488455120358034924623)
                    ·
                      rfl

theorem cell22_2209884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2209884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209884 prefixEnd_2209884 := by exact prefixLift 2209884
  have htrace : WordTrace (prefixWord ++ tailWord_2209884) baseStart_2209884 baseEnd_2209884 := by
    simpa [prefixWord, tailWord_2209884, baseEnd_2209884] using wordTrace_append hprefix tailTrace_2209884
  have hstable : (prefixWord ++ tailWord_2209884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209884).length < 2 ^ (prefixWord ++ tailWord_2209884).sum := by decide
  have hdescent : baseEnd_2209884 < baseStart_2209884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209897 : List Nat := [1, 2, 1, 1, 1, 5, 5, 6]
def baseStart_2209897 : Nat := 118140960795 + 2209897 * 2 ^ 59
def prefixEnd_2209897 : Nat := 4983230072969 + 3 ^ 40 * 2209897 * 2
def baseEnd_2209897 : Nat := 84054767254003370483287

theorem tailTrace_2209897 : CollatzResearch.WordTrace tailWord_2209897 prefixEnd_2209897 84054767254003370483287 := by
  unfold tailWord_2209897
  simp only [CollatzResearch.WordTrace]
  refine ⟨80601565274928064204739945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53734376849952042803159963 80601565274928064204739945)
  ·
    refine ⟨60451173956196048153554959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80601565274928064204739945 60451173956196048153554959)
    ·
      refine ⟨90676760934294072230332439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60451173956196048153554959 90676760934294072230332439)
      ·
        refine ⟨136015141401441108345498659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90676760934294072230332439 136015141401441108345498659)
        ·
          refine ⟨204022712102161662518247989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136015141401441108345498659 204022712102161662518247989)
          ·
            refine ⟨19127129259577655861085749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 204022712102161662518247989 19127129259577655861085749)
            ·
              refine ⟨1793168368085405236976789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19127129259577655861085749 1793168368085405236976789)
              ·
                refine ⟨84054767254003370483287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1793168368085405236976789 84054767254003370483287)
                ·
                  rfl

theorem cell22_2209897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 6].length) (baseStart_2209897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209897 prefixEnd_2209897 := by exact prefixLift 2209897
  have htrace : WordTrace (prefixWord ++ tailWord_2209897) baseStart_2209897 baseEnd_2209897 := by
    simpa [prefixWord, tailWord_2209897, baseEnd_2209897] using wordTrace_append hprefix tailTrace_2209897
  have hstable : (prefixWord ++ tailWord_2209897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209897).length < 2 ^ (prefixWord ++ tailWord_2209897).sum := by decide
  have hdescent : baseEnd_2209897 < baseStart_2209897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209912 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 7, 3]
def baseStart_2209912 : Nat := 118140960795 + 2209912 * 2 ^ 59
def prefixEnd_2209912 : Nat := 4983230072969 + 3 ^ 40 * 2209912 * 2
def baseEnd_2209912 : Nat := 756498040092575295224537

theorem tailTrace_2209912 : CollatzResearch.WordTrace tailWord_2209912 prefixEnd_2209912 756498040092575295224537 := by
  unfold tailWord_2209912
  simp only [CollatzResearch.WordTrace]
  refine ⟨40301056184936860883267995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53734741579915814511023993 40301056184936860883267995)
  ·
    refine ⟨60451584277405291324901993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40301056184936860883267995 60451584277405291324901993)
    ·
      refine ⟨45338688208053968493676495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60451584277405291324901993 45338688208053968493676495)
      ·
        refine ⟨68008032312080952740514743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45338688208053968493676495 68008032312080952740514743)
        ·
          refine ⟨102012048468121429110772115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68008032312080952740514743 102012048468121429110772115)
          ·
            refine ⟨153018072702182143666158173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102012048468121429110772115 153018072702182143666158173)
            ·
              refine ⟨57381777263318303874809315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153018072702182143666158173 57381777263318303874809315)
              ·
                refine ⟨86072665894977455812213973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57381777263318303874809315 86072665894977455812213973)
                ·
                  refine ⟨2017328106913534120598765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 86072665894977455812213973 2017328106913534120598765)
                  ·
                    refine ⟨756498040092575295224537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017328106913534120598765 756498040092575295224537)
                    ·
                      rfl

theorem cell22_2209912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_2209912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209912 prefixEnd_2209912 := by exact prefixLift 2209912
  have htrace : WordTrace (prefixWord ++ tailWord_2209912) baseStart_2209912 baseEnd_2209912 := by
    simpa [prefixWord, tailWord_2209912, baseEnd_2209912] using wordTrace_append hprefix tailTrace_2209912
  have hstable : (prefixWord ++ tailWord_2209912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209912).length < 2 ^ (prefixWord ++ tailWord_2209912).sum := by decide
  have hdescent : baseEnd_2209912 < baseStart_2209912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209929 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 3, 3]
def baseStart_2209929 : Nat := 118140960795 + 2209929 * 2 ^ 59
def prefixEnd_2209929 : Nat := 4983230072969 + 3 ^ 40 * 2209929 * 2
def baseEnd_2209929 : Nat := 756503859539992917549485

theorem tailTrace_2209929 : CollatzResearch.WordTrace tailWord_2209929 prefixEnd_2209929 756503859539992917549485 := by
  unfold tailWord_2209929
  simp only [CollatzResearch.WordTrace]
  refine ⟨80602732410812133669904841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53735154940541422446603227 80602732410812133669904841)
  ·
    refine ⟨60452049308109100252428631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80602732410812133669904841 60452049308109100252428631)
    ·
      refine ⟨90678073962163650378642947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60452049308109100252428631 90678073962163650378642947)
      ·
        refine ⟨136017110943245475567964421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90678073962163650378642947 136017110943245475567964421)
        ·
          refine ⟨25503208301858526668993329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136017110943245475567964421 25503208301858526668993329)
          ·
            refine ⟨19127406226393895001744997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25503208301858526668993329 19127406226393895001744997)
            ·
              refine ⟨3586388667448855312827187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19127406226393895001744997 3586388667448855312827187)
              ·
                refine ⟨5379583001173282969240781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586388667448855312827187 5379583001173282969240781)
                ·
                  refine ⟨2017343625439981113465293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5379583001173282969240781 2017343625439981113465293)
                  ·
                    refine ⟨756503859539992917549485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017343625439981113465293 756503859539992917549485)
                    ·
                      rfl

theorem cell22_2209929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_2209929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209929 prefixEnd_2209929 := by exact prefixLift 2209929
  have htrace : WordTrace (prefixWord ++ tailWord_2209929) baseStart_2209929 baseEnd_2209929 := by
    simpa [prefixWord, tailWord_2209929, baseEnd_2209929] using wordTrace_append hprefix tailTrace_2209929
  have hstable : (prefixWord ++ tailWord_2209929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209929).length < 2 ^ (prefixWord ++ tailWord_2209929).sum := by decide
  have hdescent : baseEnd_2209929 < baseStart_2209929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2209980 : List Nat := [2, 2, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_2209980 : Nat := 118140960795 + 2209980 * 2 ^ 59
def prefixEnd_2209980 : Nat := 4983230072969 + 3 ^ 40 * 2209980 * 2
def baseEnd_2209980 : Nat := 756521317882245784524329

theorem tailTrace_2209980 : CollatzResearch.WordTrace tailWord_2209980 prefixEnd_2209980 756521317882245784524329 := by
  unfold tailWord_2209980
  simp only [CollatzResearch.WordTrace]
  refine ⟨40302296266813684690005697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53736395022418246253340929 40302296266813684690005697)
  ·
    refine ⟨30226722200110263517504273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40302296266813684690005697 30226722200110263517504273)
    ·
      refine ⟨22670041650082697638128205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30226722200110263517504273 22670041650082697638128205)
      ·
        refine ⟨8501265618781011614298077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22670041650082697638128205 8501265618781011614298077)
        ·
          refine ⟨3187974607042879355361779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8501265618781011614298077 3187974607042879355361779)
          ·
            refine ⟨4781961910564319033042669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187974607042879355361779 4781961910564319033042669)
            ·
              refine ⟨1793235716461619637391001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4781961910564319033042669 1793235716461619637391001)
              ·
                refine ⟨1344926787346214728043251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793235716461619637391001 1344926787346214728043251)
                ·
                  refine ⟨2017390181019322092064877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344926787346214728043251 2017390181019322092064877)
                  ·
                    refine ⟨756521317882245784524329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017390181019322092064877 756521317882245784524329)
                    ·
                      rfl

theorem cell22_2209980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_2209980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2209980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2209980 prefixEnd_2209980 := by exact prefixLift 2209980
  have htrace : WordTrace (prefixWord ++ tailWord_2209980) baseStart_2209980 baseEnd_2209980 := by
    simpa [prefixWord, tailWord_2209980, baseEnd_2209980] using wordTrace_append hprefix tailTrace_2209980
  have hstable : (prefixWord ++ tailWord_2209980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2209980).length < 2 ^ (prefixWord ++ tailWord_2209980).sum := by decide
  have hdescent : baseEnd_2209980 < baseStart_2209980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2209980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210023 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2210023 : Nat := 118140960795 + 2210023 * 2 ^ 59
def prefixEnd_2210023 : Nat := 4983230072969 + 3 ^ 40 * 2210023 * 2
def baseEnd_2210023 : Nat := 756536037661008005699197

theorem tailTrace_2210023 : CollatzResearch.WordTrace tailWord_2210023 prefixEnd_2210023 756536037661008005699197 := by
  unfold tailWord_2210023
  simp only [CollatzResearch.WordTrace]
  refine ⟨80606160872471587723826723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53737440581647725149217815 80606160872471587723826723)
  ·
    refine ⟨120909241308707381585740085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80606160872471587723826723 120909241308707381585740085)
    ·
      refine ⟨11335241372691317023663133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120909241308707381585740085 11335241372691317023663133)
      ·
        refine ⟨4250715514759243883873675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11335241372691317023663133 4250715514759243883873675)
        ·
          refine ⟨6376073272138865825810513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250715514759243883873675 6376073272138865825810513)
          ·
            refine ⟨4782054954104149369357885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6376073272138865825810513 4782054954104149369357885)
            ·
              refine ⟨1793270607789056013509207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4782054954104149369357885 1793270607789056013509207)
              ·
                refine ⟨2689905911683584020263811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793270607789056013509207 2689905911683584020263811)
                ·
                  refine ⟨4034858867525376030395717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689905911683584020263811 4034858867525376030395717)
                  ·
                    refine ⟨756536037661008005699197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4034858867525376030395717 756536037661008005699197)
                    ·
                      rfl

theorem cell22_2210023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2210023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210023 prefixEnd_2210023 := by exact prefixLift 2210023
  have htrace : WordTrace (prefixWord ++ tailWord_2210023) baseStart_2210023 baseEnd_2210023 := by
    simpa [prefixWord, tailWord_2210023, baseEnd_2210023] using wordTrace_append hprefix tailTrace_2210023
  have hstable : (prefixWord ++ tailWord_2210023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210023).length < 2 ^ (prefixWord ++ tailWord_2210023).sum := by decide
  have hdescent : baseEnd_2210023 < baseStart_2210023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210038 : List Nat := [5, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2210038 : Nat := 118140960795 + 2210038 * 2 ^ 59
def prefixEnd_2210038 : Nat := 4983230072969 + 3 ^ 40 * 2210038 * 2
def baseEnd_2210038 : Nat := 252180390822517655524717

theorem tailTrace_2210038 : CollatzResearch.WordTrace tailWord_2210038 prefixEnd_2210038 252180390822517655524717 := by
  unfold tailWord_2210038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5037919247963577830351423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53737805311611496857081845 5037919247963577830351423)
  ·
    refine ⟨7556878871945366745527135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5037919247963577830351423 7556878871945366745527135)
    ·
      refine ⟨11335318307918050118290703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7556878871945366745527135 11335318307918050118290703)
      ·
        refine ⟨17002977461877075177436055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11335318307918050118290703 17002977461877075177436055)
        ·
          refine ⟨25504466192815612766154083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17002977461877075177436055 25504466192815612766154083)
          ·
            refine ⟨38256699289223419149231125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25504466192815612766154083 38256699289223419149231125)
            ·
              refine ⟨1793282779182347772620209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38256699289223419149231125 1793282779182347772620209)
              ·
                refine ⟨1344962084386760829465157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793282779182347772620209 1344962084386760829465157)
                ·
                  refine ⟨252180390822517655524717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1344962084386760829465157 252180390822517655524717)
                  ·
                    rfl

theorem cell22_2210038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2210038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210038 prefixEnd_2210038 := by exact prefixLift 2210038
  have htrace : WordTrace (prefixWord ++ tailWord_2210038) baseStart_2210038 baseEnd_2210038 := by
    simpa [prefixWord, tailWord_2210038, baseEnd_2210038] using wordTrace_append hprefix tailTrace_2210038
  have hstable : (prefixWord ++ tailWord_2210038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210038).length < 2 ^ (prefixWord ++ tailWord_2210038).sum := by decide
  have hdescent : baseEnd_2210038 < baseStart_2210038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210098 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_2210098 : Nat := 118140960795 + 2210098 * 2 ^ 59
def prefixEnd_2210098 : Nat := 4983230072969 + 3 ^ 40 * 2210098 * 2
def baseEnd_2210098 : Nat := 756561711693732810073967

theorem tailTrace_2210098 : CollatzResearch.WordTrace tailWord_2210098 prefixEnd_2210098 756561711693732810073967 := by
  unfold tailWord_2210098
  simp only [CollatzResearch.WordTrace]
  refine ⟨20152224086799968883201737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53739264231466583688537965 20152224086799968883201737)
  ·
    refine ⟨15114168065099976662401303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20152224086799968883201737 15114168065099976662401303)
    ·
      refine ⟨22671252097649964993601955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15114168065099976662401303 22671252097649964993601955)
      ·
        refine ⟨34006878146474947490402933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22671252097649964993601955 34006878146474947490402933)
        ·
          refine ⟨3188144826232026327225275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34006878146474947490402933 3188144826232026327225275)
          ·
            refine ⟨4782217239348039490837913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3188144826232026327225275 4782217239348039490837913)
            ·
              refine ⟨3586662929511029618128435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782217239348039490837913 3586662929511029618128435)
              ·
                refine ⟨5379994394266544427192653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586662929511029618128435 5379994394266544427192653)
                ·
                  refine ⟨2017497897849954160197245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5379994394266544427192653 2017497897849954160197245)
                  ·
                    refine ⟨756561711693732810073967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017497897849954160197245 756561711693732810073967)
                    ·
                      rfl

theorem cell22_2210098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_2210098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210098 prefixEnd_2210098 := by exact prefixLift 2210098
  have htrace : WordTrace (prefixWord ++ tailWord_2210098) baseStart_2210098 baseEnd_2210098 := by
    simpa [prefixWord, tailWord_2210098, baseEnd_2210098] using wordTrace_append hprefix tailTrace_2210098
  have hstable : (prefixWord ++ tailWord_2210098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210098).length < 2 ^ (prefixWord ++ tailWord_2210098).sum := by decide
  have hdescent : baseEnd_2210098 < baseStart_2210098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210111 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 5]
def baseStart_2210111 : Nat := 118140960795 + 2210111 * 2 ^ 59
def prefixEnd_2210111 : Nat := 4983230072969 + 3 ^ 40 * 2210111 * 2
def baseEnd_2210111 : Nat := 252188720619801703166309

theorem tailTrace_2210111 : CollatzResearch.WordTrace tailWord_2210111 prefixEnd_2210111 252188720619801703166309 := by
  unfold tailWord_2210111
  simp only [CollatzResearch.WordTrace]
  refine ⟨80609370496152778753030187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53739580330768519168686791 80609370496152778753030187)
  ·
    refine ⟨120914055744229168129545281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80609370496152778753030187 120914055744229168129545281)
    ·
      refine ⟨90685541808171876097158961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120914055744229168129545281 90685541808171876097158961)
      ·
        refine ⟨68014156356128907072869221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90685541808171876097158961 68014156356128907072869221)
        ·
          refine ⟨12752654316774170076162979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68014156356128907072869221 12752654316774170076162979)
          ·
            refine ⟨19128981475161255114244469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12752654316774170076162979 19128981475161255114244469)
            ·
              refine ⟨1793342013296367666960419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19128981475161255114244469 1793342013296367666960419)
              ·
                refine ⟨2690013019944551500440629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793342013296367666960419 2690013019944551500440629)
                ·
                  refine ⟨252188720619801703166309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2690013019944551500440629 252188720619801703166309)
                  ·
                    rfl

theorem cell22_2210111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 5].length) (baseStart_2210111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210111 prefixEnd_2210111 := by exact prefixLift 2210111
  have htrace : WordTrace (prefixWord ++ tailWord_2210111) baseStart_2210111 baseEnd_2210111 := by
    simpa [prefixWord, tailWord_2210111, baseEnd_2210111] using wordTrace_append hprefix tailTrace_2210111
  have hstable : (prefixWord ++ tailWord_2210111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210111).length < 2 ^ (prefixWord ++ tailWord_2210111).sum := by decide
  have hdescent : baseEnd_2210111 < baseStart_2210111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210169 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_2210169 : Nat := 118140960795 + 2210169 * 2 ^ 59
def prefixEnd_2210169 : Nat := 4983230072969 + 3 ^ 40 * 2210169 * 2
def baseEnd_2210169 : Nat := 756586016444712291548749

theorem tailTrace_2210169 : CollatzResearch.WordTrace tailWord_2210169 prefixEnd_2210169 756586016444712291548749 := by
  unfold tailWord_2210169
  simp only [CollatzResearch.WordTrace]
  refine ⟨80611485929942654658641561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53740990619961769772427707 80611485929942654658641561)
  ·
    refine ⟨60458614447456990993981171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80611485929942654658641561 60458614447456990993981171)
    ·
      refine ⟨90687921671185486490971757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60458614447456990993981171 90687921671185486490971757)
      ·
        refine ⟨34007970626694557434114409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90687921671185486490971757 34007970626694557434114409)
        ·
          refine ⟨25505977970020918075585807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34007970626694557434114409 25505977970020918075585807)
          ·
            refine ⟨38258966955031377113378711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25505977970020918075585807 38258966955031377113378711)
            ·
              refine ⟨57388450432547065670068067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38258966955031377113378711 57388450432547065670068067)
              ·
                refine ⟨86082675648820598505102101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57388450432547065670068067 86082675648820598505102101)
                ·
                  refine ⟨4035125421038465554926661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86082675648820598505102101 4035125421038465554926661)
                  ·
                    refine ⟨756586016444712291548749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4035125421038465554926661 756586016444712291548749)
                    ·
                      rfl

theorem cell22_2210169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_2210169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210169 prefixEnd_2210169 := by exact prefixLift 2210169
  have htrace : WordTrace (prefixWord ++ tailWord_2210169) baseStart_2210169 baseEnd_2210169 := by
    simpa [prefixWord, tailWord_2210169, baseEnd_2210169] using wordTrace_append hprefix tailTrace_2210169
  have hstable : (prefixWord ++ tailWord_2210169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210169).length < 2 ^ (prefixWord ++ tailWord_2210169).sum := by decide
  have hdescent : baseEnd_2210169 < baseStart_2210169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210184 : List Nat := [2, 1, 3, 3, 1, 1, 1, 10]
def baseStart_2210184 : Nat := 118140960795 + 2210184 * 2 ^ 59
def prefixEnd_2210184 : Nat := 4983230072969 + 3 ^ 40 * 2210184 * 2
def baseEnd_2210184 : Nat := 84065683472361916935967

theorem tailTrace_2210184 : CollatzResearch.WordTrace tailWord_2210184 prefixEnd_2210184 84065683472361916935967 := by
  unfold tailWord_2210184
  simp only [CollatzResearch.WordTrace]
  refine ⟨40306016512444156110218803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53741355349925541480291737 40306016512444156110218803)
  ·
    refine ⟨60459024768666234165328205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40306016512444156110218803 60459024768666234165328205)
    ·
      refine ⟨22672134288249837811998077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60459024768666234165328205 22672134288249837811998077)
      ·
        refine ⟨8502050358093689179499279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22672134288249837811998077 8502050358093689179499279)
        ·
          refine ⟨12753075537140533769248919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8502050358093689179499279 12753075537140533769248919)
          ·
            refine ⟨19129613305710800653873379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12753075537140533769248919 19129613305710800653873379)
            ·
              refine ⟨28694419958566200980810069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19129613305710800653873379 28694419958566200980810069)
              ·
                refine ⟨84065683472361916935967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28694419958566200980810069 84065683472361916935967)
                ·
                  rfl

theorem cell22_2210184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 10].length) (baseStart_2210184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210184 prefixEnd_2210184 := by exact prefixLift 2210184
  have htrace : WordTrace (prefixWord ++ tailWord_2210184) baseStart_2210184 baseEnd_2210184 := by
    simpa [prefixWord, tailWord_2210184, baseEnd_2210184] using wordTrace_append hprefix tailTrace_2210184
  have hstable : (prefixWord ++ tailWord_2210184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210184).length < 2 ^ (prefixWord ++ tailWord_2210184).sum := by decide
  have hdescent : baseEnd_2210184 < baseStart_2210184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210205 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_2210205 : Nat := 118140960795 + 2210205 * 2 ^ 59
def prefixEnd_2210205 : Nat := 4983230072969 + 3 ^ 40 * 2210205 * 2
def baseEnd_2210205 : Nat := 756598339980420197648639

theorem tailTrace_2210205 : CollatzResearch.WordTrace tailWord_2210205 prefixEnd_2210205 756598339980420197648639 := by
  unfold tailWord_2210205
  simp only [CollatzResearch.WordTrace]
  refine ⟨80612798957812232806952069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53741865971874821871301379 80612798957812232806952069)
  ·
    refine ⟨15114899804589793651303513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80612798957812232806952069 15114899804589793651303513)
    ·
      refine ⟨11336174853442345238477635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15114899804589793651303513 11336174853442345238477635)
      ·
        refine ⟨17004262280163517857716453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11336174853442345238477635 17004262280163517857716453)
        ·
          refine ⟨3188299177530659598321835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17004262280163517857716453 3188299177530659598321835)
          ·
            refine ⟨4782448766295989397482753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3188299177530659598321835 4782448766295989397482753)
            ·
              refine ⟨3586836574721992048112065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782448766295989397482753 3586836574721992048112065)
              ·
                refine ⟨2690127431041494036084049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3586836574721992048112065 2690127431041494036084049)
                ·
                  refine ⟨2017595573281120527063037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690127431041494036084049 2017595573281120527063037)
                  ·
                    refine ⟨756598339980420197648639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017595573281120527063037 756598339980420197648639)
                    ·
                      rfl

theorem cell22_2210205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_2210205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210205 prefixEnd_2210205 := by exact prefixLift 2210205
  have htrace : WordTrace (prefixWord ++ tailWord_2210205) baseStart_2210205 baseEnd_2210205 := by
    simpa [prefixWord, tailWord_2210205, baseEnd_2210205] using wordTrace_append hprefix tailTrace_2210205
  have hstable : (prefixWord ++ tailWord_2210205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210205).length < 2 ^ (prefixWord ++ tailWord_2210205).sum := by decide
  have hdescent : baseEnd_2210205 < baseStart_2210205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210233 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 3, 3]
def baseStart_2210233 : Nat := 118140960795 + 2210233 * 2 ^ 59
def prefixEnd_2210233 : Nat := 4983230072969 + 3 ^ 40 * 2210233 * 2
def baseEnd_2210233 : Nat := 756607924952637457948553

theorem tailTrace_2210233 : CollatzResearch.WordTrace tailWord_2210233 prefixEnd_2210233 756607924952637457948553 := by
  unfold tailWord_2210233
  simp only [CollatzResearch.WordTrace]
  refine ⟨80613820201710793588971353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53742546801140529059314235 80613820201710793588971353)
  ·
    refine ⟨60460365151283095191728515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80613820201710793588971353 60460365151283095191728515)
    ·
      refine ⟨90690547726924642787592773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60460365151283095191728515 90690547726924642787592773)
      ·
        refine ⟨17004477698798370522673645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90690547726924642787592773 17004477698798370522673645)
        ·
          refine ⟨6376679137049388946002617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17004477698798370522673645 6376679137049388946002617)
          ·
            refine ⟨4782509352787041709501963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6376679137049388946002617 4782509352787041709501963)
            ·
              refine ⟨7173764029180562564252945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4782509352787041709501963 7173764029180562564252945)
              ·
                refine ⟨5380323021885421923189709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7173764029180562564252945 5380323021885421923189709)
                ·
                  refine ⟨2017621133207033221196141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5380323021885421923189709 2017621133207033221196141)
                  ·
                    refine ⟨756607924952637457948553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017621133207033221196141 756607924952637457948553)
                    ·
                      rfl

theorem cell22_2210233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_2210233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210233 prefixEnd_2210233 := by exact prefixLift 2210233
  have htrace : WordTrace (prefixWord ++ tailWord_2210233) baseStart_2210233 baseEnd_2210233 := by
    simpa [prefixWord, tailWord_2210233, baseEnd_2210233] using wordTrace_append hprefix tailTrace_2210233
  have hstable : (prefixWord ++ tailWord_2210233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210233).length < 2 ^ (prefixWord ++ tailWord_2210233).sum := by decide
  have hdescent : baseEnd_2210233 < baseStart_2210233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210250 : List Nat := [3, 1, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_2210250 : Nat := 118140960795 + 2210250 * 2 ^ 59
def prefixEnd_2210250 : Nat := 4983230072969 + 3 ^ 40 * 2210250 * 2
def baseEnd_2210250 : Nat := 756613744400055080273501

theorem tailTrace_2210250 : CollatzResearch.WordTrace tailWord_2210250 prefixEnd_2210250 756613744400055080273501 := by
  unfold tailWord_2210250
  simp only [CollatzResearch.WordTrace]
  refine ⟨20153610060662301373085051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53742960161766136994893469 20153610060662301373085051)
  ·
    refine ⟨30230415090993452059627577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20153610060662301373085051 30230415090993452059627577)
    ·
      refine ⟨22672811318245089044720683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30230415090993452059627577 22672811318245089044720683)
      ·
        refine ⟨34009216977367633567081025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22672811318245089044720683 34009216977367633567081025)
        ·
          refine ⟨25506912733025725175310769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34009216977367633567081025 25506912733025725175310769)
          ·
            refine ⟨19130184549769293881483077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25506912733025725175310769 19130184549769293881483077)
            ·
              refine ⟨3586909603081742602778077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19130184549769293881483077 3586909603081742602778077)
              ·
                refine ⟨1345091101155653476041779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3586909603081742602778077 1345091101155653476041779)
                ·
                  refine ⟨2017636651733480214062669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345091101155653476041779 2017636651733480214062669)
                  ·
                    refine ⟨756613744400055080273501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017636651733480214062669 756613744400055080273501)
                    ·
                      rfl

theorem cell22_2210250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_2210250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210250 prefixEnd_2210250 := by exact prefixLift 2210250
  have htrace : WordTrace (prefixWord ++ tailWord_2210250) baseStart_2210250 baseEnd_2210250 := by
    simpa [prefixWord, tailWord_2210250, baseEnd_2210250] using wordTrace_append hprefix tailTrace_2210250
  have hstable : (prefixWord ++ tailWord_2210250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210250).length < 2 ^ (prefixWord ++ tailWord_2210250).sum := by decide
  have hdescent : baseEnd_2210250 < baseStart_2210250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210261 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_2210261 : Nat := 118140960795 + 2210261 * 2 ^ 59
def prefixEnd_2210261 : Nat := 4983230072969 + 3 ^ 40 * 2210261 * 2
def baseEnd_2210261 : Nat := 756617509924854718248467

theorem tailTrace_2210261 : CollatzResearch.WordTrace tailWord_2210261 prefixEnd_2210261 756617509924854718248467 := by
  unfold tailWord_2210261
  simp only [CollatzResearch.WordTrace]
  refine ⟨80614841445609354370990637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53743227630406236247327091 80614841445609354370990637)
  ·
    refine ⟨30230565542103507889121489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80614841445609354370990637 30230565542103507889121489)
    ·
      refine ⟨22672924156577630916841117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30230565542103507889121489 22672924156577630916841117)
      ·
        refine ⟨8502346558716611593815419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22672924156577630916841117 8502346558716611593815419)
        ·
          refine ⟨12753519838074917390723129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8502346558716611593815419 12753519838074917390723129)
          ·
            refine ⟨9565139878556188043042347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12753519838074917390723129 9565139878556188043042347)
            ·
              refine ⟨14347709817834282064563521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9565139878556188043042347 14347709817834282064563521)
              ·
                refine ⟨10760782363375711548422641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14347709817834282064563521 10760782363375711548422641)
                ·
                  refine ⟨8070586772531783661316981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10760782363375711548422641 8070586772531783661316981)
                  ·
                    refine ⟨756617509924854718248467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8070586772531783661316981 756617509924854718248467)
                    ·
                      rfl

theorem cell22_2210261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_2210261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210261 prefixEnd_2210261 := by exact prefixLift 2210261
  have htrace : WordTrace (prefixWord ++ tailWord_2210261) baseStart_2210261 baseEnd_2210261 := by
    simpa [prefixWord, tailWord_2210261, baseEnd_2210261] using wordTrace_append hprefix tailTrace_2210261
  have hstable : (prefixWord ++ tailWord_2210261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210261).length < 2 ^ (prefixWord ++ tailWord_2210261).sum := by decide
  have hdescent : baseEnd_2210261 < baseStart_2210261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210323 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 2, 3]
def baseStart_2210323 : Nat := 118140960795 + 2210323 * 2 ^ 59
def prefixEnd_2210323 : Nat := 4983230072969 + 3 ^ 40 * 2210323 * 2
def baseEnd_2210323 : Nat := 756638733791907223198277

theorem tailTrace_2210323 : CollatzResearch.WordTrace tailWord_2210323 prefixEnd_2210323 756638733791907223198277 := by
  unfold tailWord_2210323
  simp only [CollatzResearch.WordTrace]
  refine ⟨80617102771384738959747623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53744735180923159306498415 80617102771384738959747623)
  ·
    refine ⟨120925654157077108439621435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80617102771384738959747623 120925654157077108439621435)
    ·
      refine ⟨181388481235615662659432153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120925654157077108439621435 181388481235615662659432153)
      ·
        refine ⟨136041360926711746994574115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181388481235615662659432153 136041360926711746994574115)
        ·
          refine ⟨204062041390067620491861173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136041360926711746994574115 204062041390067620491861173)
          ·
            refine ⟨19130816380318839421111985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 204062041390067620491861173 19130816380318839421111985)
            ·
              refine ⟨14348112285239129565833989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19130816380318839421111985 14348112285239129565833989)
              ·
                refine ⟨2690271053482336793593873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14348112285239129565833989 2690271053482336793593873)
                ·
                  refine ⟨2017703290111752595195405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690271053482336793593873 2017703290111752595195405)
                  ·
                    refine ⟨756638733791907223198277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017703290111752595195405 756638733791907223198277)
                    ·
                      rfl

theorem cell22_2210323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 3].length) (baseStart_2210323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210323 prefixEnd_2210323 := by exact prefixLift 2210323
  have htrace : WordTrace (prefixWord ++ tailWord_2210323) baseStart_2210323 baseEnd_2210323 := by
    simpa [prefixWord, tailWord_2210323, baseEnd_2210323] using wordTrace_append hprefix tailTrace_2210323
  have hstable : (prefixWord ++ tailWord_2210323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210323).length < 2 ^ (prefixWord ++ tailWord_2210323).sum := by decide
  have hdescent : baseEnd_2210323 < baseStart_2210323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210325 : List Nat := [1, 3, 2, 1, 3, 1, 5, 2, 4]
def baseStart_2210325 : Nat := 118140960795 + 2210325 * 2 ^ 59
def prefixEnd_2210325 : Nat := 4983230072969 + 3 ^ 40 * 2210325 * 2
def baseEnd_2210325 : Nat := 252213139477593294882757

theorem tailTrace_2210325 : CollatzResearch.WordTrace tailWord_2210325 prefixEnd_2210325 252213139477593294882757 := by
  unfold tailWord_2210325
  simp only [CollatzResearch.WordTrace]
  refine ⟨80617175717377493301320429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53744783811584995534213619 80617175717377493301320429)
  ·
    refine ⟨30231440894016559987995161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80617175717377493301320429 30231440894016559987995161)
    ·
      refine ⟨22673580670512419990996371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30231440894016559987995161 22673580670512419990996371)
      ·
        refine ⟨34010371005768629986494557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22673580670512419990996371 34010371005768629986494557)
        ·
          refine ⟨12753889127163236244935459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34010371005768629986494557 12753889127163236244935459)
          ·
            refine ⟨19130833690744854367403189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12753889127163236244935459 19130833690744854367403189)
            ·
              refine ⟨1793515658507330096944049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19130833690744854367403189 1793515658507330096944049)
              ·
                refine ⟨1345136743880497572708037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793515658507330096944049 1345136743880497572708037)
                ·
                  refine ⟨252213139477593294882757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345136743880497572708037 252213139477593294882757)
                  ·
                    rfl

theorem cell22_2210325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_2210325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210325 prefixEnd_2210325 := by exact prefixLift 2210325
  have htrace : WordTrace (prefixWord ++ tailWord_2210325) baseStart_2210325 baseEnd_2210325 := by
    simpa [prefixWord, tailWord_2210325, baseEnd_2210325] using wordTrace_append hprefix tailTrace_2210325
  have hstable : (prefixWord ++ tailWord_2210325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210325).length < 2 ^ (prefixWord ++ tailWord_2210325).sum := by decide
  have hdescent : baseEnd_2210325 < baseStart_2210325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210374 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2210374 : Nat := 118140960795 + 2210374 * 2 ^ 59
def prefixEnd_2210374 : Nat := 4983230072969 + 3 ^ 40 * 2210374 * 2
def baseEnd_2210374 : Nat := 756656192134160090173121

theorem tailTrace_2210374 : CollatzResearch.WordTrace tailWord_2210374 prefixEnd_2210374 756656192134160090173121 := by
  unfold tailWord_2210374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519342590443749208432943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53745975262799983113236117 2519342590443749208432943)
  ·
    refine ⟨3779013885665623812649415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2519342590443749208432943 3779013885665623812649415)
    ·
      refine ⟨5668520828498435718974123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779013885665623812649415 5668520828498435718974123)
      ·
        refine ⟨8502781242747653578461185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5668520828498435718974123 8502781242747653578461185)
        ·
          refine ⟨6377085932060740183845889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8502781242747653578461185 6377085932060740183845889)
          ·
            refine ⟨4782814449045555137884417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6377085932060740183845889 4782814449045555137884417)
            ·
              refine ⟨3587110836784166353413313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782814449045555137884417 3587110836784166353413313)
              ·
                refine ⟨2690333127588124765059985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587110836784166353413313 2690333127588124765059985)
                ·
                  refine ⟨2017749845691093573794989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690333127588124765059985 2017749845691093573794989)
                  ·
                    refine ⟨756656192134160090173121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017749845691093573794989 756656192134160090173121)
                    ·
                      rfl

theorem cell22_2210374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2210374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210374 prefixEnd_2210374 := by exact prefixLift 2210374
  have htrace : WordTrace (prefixWord ++ tailWord_2210374) baseStart_2210374 baseEnd_2210374 := by
    simpa [prefixWord, tailWord_2210374, baseEnd_2210374] using wordTrace_append hprefix tailTrace_2210374
  have hstable : (prefixWord ++ tailWord_2210374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210374).length < 2 ^ (prefixWord ++ tailWord_2210374).sum := by decide
  have hdescent : baseEnd_2210374 < baseStart_2210374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210462 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2210462 : Nat := 118140960795 + 2210462 * 2 ^ 59
def prefixEnd_2210462 : Nat := 4983230072969 + 3 ^ 40 * 2210462 * 2
def baseEnd_2210462 : Nat := 756686316332557193972851

theorem tailTrace_2210462 : CollatzResearch.WordTrace tailWord_2210462 prefixEnd_2210462 756686316332557193972851 := by
  unfold tailWord_2210462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10077771564735145712382205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53748115011920777132705093 10077771564735145712382205)
  ·
    refine ⟨3779164336775679642143327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10077771564735145712382205 3779164336775679642143327)
    ·
      refine ⟨5668746505163519463214991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779164336775679642143327 5668746505163519463214991)
      ·
        refine ⟨8503119757745279194822487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5668746505163519463214991 8503119757745279194822487)
        ·
          refine ⟨12754679636617918792233731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8503119757745279194822487 12754679636617918792233731)
          ·
            refine ⟨19132019454926878188350597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12754679636617918792233731 19132019454926878188350597)
            ·
              refine ⟨3587253647798789660315737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19132019454926878188350597 3587253647798789660315737)
              ·
                refine ⟨2690440235849092245236803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587253647798789660315737 2690440235849092245236803)
                ·
                  refine ⟨4035660353773638367855205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690440235849092245236803 4035660353773638367855205)
                  ·
                    refine ⟨756686316332557193972851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4035660353773638367855205 756686316332557193972851)
                    ·
                      rfl

theorem cell22_2210462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2210462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210462 prefixEnd_2210462 := by exact prefixLift 2210462
  have htrace : WordTrace (prefixWord ++ tailWord_2210462) baseStart_2210462 baseEnd_2210462 := by
    simpa [prefixWord, tailWord_2210462, baseEnd_2210462] using wordTrace_append hprefix tailTrace_2210462
  have hstable : (prefixWord ++ tailWord_2210462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210462).length < 2 ^ (prefixWord ++ tailWord_2210462).sum := by decide
  have hdescent : baseEnd_2210462 < baseStart_2210462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210477 : List Nat := [1, 5, 2, 1, 1, 2, 3, 3, 4]
def baseStart_2210477 : Nat := 118140960795 + 2210477 * 2 ^ 59
def prefixEnd_2210477 : Nat := 4983230072969 + 3 ^ 40 * 2210477 * 2
def baseEnd_2210477 : Nat := 252230483713034051615935

theorem tailTrace_2210477 : CollatzResearch.WordTrace tailWord_2210477 prefixEnd_2210477 252230483713034051615935 := by
  unfold tailWord_2210477
  simp only [CollatzResearch.WordTrace]
  refine ⟨80622719612826823260853685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53748479741884548840569123 80622719612826823260853685)
  ·
    refine ⟨7558379963702514680705033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80622719612826823260853685 7558379963702514680705033)
    ·
      refine ⟨5668784972776886010528775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7558379963702514680705033 5668784972776886010528775)
      ·
        refine ⟨8503177459165329015793163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5668784972776886010528775 8503177459165329015793163)
        ·
          refine ⟨12754766188747993523689745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8503177459165329015793163 12754766188747993523689745)
          ·
            refine ⟨9566074641560995142767309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12754766188747993523689745 9566074641560995142767309)
            ·
              refine ⟨3587277990585373178537741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9566074641560995142767309 3587277990585373178537741)
              ·
                refine ⟨1345229246469514941951653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3587277990585373178537741 1345229246469514941951653)
                ·
                  refine ⟨252230483713034051615935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345229246469514941951653 252230483713034051615935)
                  ·
                    rfl

theorem cell22_2210477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_2210477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210477 prefixEnd_2210477 := by exact prefixLift 2210477
  have htrace : WordTrace (prefixWord ++ tailWord_2210477) baseStart_2210477 baseEnd_2210477 := by
    simpa [prefixWord, tailWord_2210477, baseEnd_2210477] using wordTrace_append hprefix tailTrace_2210477
  have hstable : (prefixWord ++ tailWord_2210477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210477).length < 2 ^ (prefixWord ++ tailWord_2210477).sum := by decide
  have hdescent : baseEnd_2210477 < baseStart_2210477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210554 : List Nat := [3, 1, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_2210554 : Nat := 118140960795 + 2210554 * 2 ^ 59
def prefixEnd_2210554 : Nat := 4983230072969 + 3 ^ 40 * 2210554 * 2
def baseEnd_2210554 : Nat := 756717809812699620672569

theorem tailTrace_2210554 : CollatzResearch.WordTrace tailWord_2210554 prefixEnd_2210554 756717809812699620672569 := by
  unfold tailWord_2210554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20156382008386966352851679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53750352022365243607604477 20156382008386966352851679)
  ·
    refine ⟨30234573012580449529277519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20156382008386966352851679 30234573012580449529277519)
    ·
      refine ⟨45351859518870674293916279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30234573012580449529277519 45351859518870674293916279)
      ·
        refine ⟨68027789278306011440874419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45351859518870674293916279 68027789278306011440874419)
        ·
          refine ⟨102041683917459017161311629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68027789278306011440874419 102041683917459017161311629)
          ·
            refine ⟨38265631469047131435491861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102041683917459017161311629 38265631469047131435491861)
            ·
              refine ⟨1793701475111584286038681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38265631469047131435491861 1793701475111584286038681)
              ·
                refine ⟨1345276106333688214529011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793701475111584286038681 1345276106333688214529011)
                ·
                  refine ⟨2017914159500532321793517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345276106333688214529011 2017914159500532321793517)
                  ·
                    refine ⟨756717809812699620672569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017914159500532321793517 756717809812699620672569)
                    ·
                      rfl

theorem cell22_2210554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_2210554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210554 prefixEnd_2210554 := by exact prefixLift 2210554
  have htrace : WordTrace (prefixWord ++ tailWord_2210554) baseStart_2210554 baseEnd_2210554 := by
    simpa [prefixWord, tailWord_2210554, baseEnd_2210554] using wordTrace_append hprefix tailTrace_2210554
  have hstable : (prefixWord ++ tailWord_2210554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210554).length < 2 ^ (prefixWord ++ tailWord_2210554).sum := by decide
  have hdescent : baseEnd_2210554 < baseStart_2210554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210640 : List Nat := [2, 1, 1, 1, 1, 4, 6, 6]
def baseStart_2210640 : Nat := 118140960795 + 2210640 * 2 ^ 59
def prefixEnd_2210640 : Nat := 4983230072969 + 3 ^ 40 * 2210640 * 2
def baseEnd_2210640 : Nat := 84083027707802673669145

theorem tailTrace_2210640 : CollatzResearch.WordTrace tailWord_2210640 prefixEnd_2210640 84083027707802673669145 := by
  unfold tailWord_2210640
  simp only [CollatzResearch.WordTrace]
  refine ⟨40314332355618151049518687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53752443140824201399358249 40314332355618151049518687)
  ·
    refine ⟨60471498533427226574278031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40314332355618151049518687 60471498533427226574278031)
    ·
      refine ⟨90707247800140839861417047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60471498533427226574278031 90707247800140839861417047)
      ·
        refine ⟨136060871700211259792125571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90707247800140839861417047 136060871700211259792125571)
        ·
          refine ⟨204091307550316889688188357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136060871700211259792125571 204091307550316889688188357)
          ·
            refine ⟨38267120165684416816535317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204091307550316889688188357 38267120165684416816535317)
            ·
              refine ⟨1793771257766457038275093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38267120165684416816535317 1793771257766457038275093)
              ·
                refine ⟨84083027707802673669145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1793771257766457038275093 84083027707802673669145)
                ·
                  rfl

theorem cell22_2210640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 6].length) (baseStart_2210640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210640 prefixEnd_2210640 := by exact prefixLift 2210640
  have htrace : WordTrace (prefixWord ++ tailWord_2210640) baseStart_2210640 baseEnd_2210640 := by
    simpa [prefixWord, tailWord_2210640, baseEnd_2210640] using wordTrace_append hprefix tailTrace_2210640
  have hstable : (prefixWord ++ tailWord_2210640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210640).length < 2 ^ (prefixWord ++ tailWord_2210640).sum := by decide
  have hdescent : baseEnd_2210640 < baseStart_2210640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210672 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 3, 3]
def baseStart_2210672 : Nat := 118140960795 + 2210672 * 2 ^ 59
def prefixEnd_2210672 : Nat := 4983230072969 + 3 ^ 40 * 2210672 * 2
def baseEnd_2210672 : Nat := 756758203624186646222207

theorem tailTrace_2210672 : CollatzResearch.WordTrace tailWord_2210672 prefixEnd_2210672 756758203624186646222207 := by
  unfold tailWord_2210672
  simp only [CollatzResearch.WordTrace]
  refine ⟨40314915923560185782101135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53753221231413581042801513 40314915923560185782101135)
  ·
    refine ⟨60472373885340278673151703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40314915923560185782101135 60472373885340278673151703)
    ·
      refine ⟨90708560828010418009727555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60472373885340278673151703 90708560828010418009727555)
      ·
        refine ⟨136062841242015627014591333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90708560828010418009727555 136062841242015627014591333)
        ·
          refine ⟨25511782732877930065235875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136062841242015627014591333 25511782732877930065235875)
          ·
            refine ⟨38267674099316895097853813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25511782732877930065235875 38267674099316895097853813)
            ·
              refine ⟨3587594446810958915423795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38267674099316895097853813 3587594446810958915423795)
              ·
                refine ⟨5381391670216438373135693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3587594446810958915423795 5381391670216438373135693)
                ·
                  refine ⟨2018021876331164389925885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5381391670216438373135693 2018021876331164389925885)
                  ·
                    refine ⟨756758203624186646222207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2018021876331164389925885 756758203624186646222207)
                    ·
                      rfl

theorem cell22_2210672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_2210672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210672 prefixEnd_2210672 := by exact prefixLift 2210672
  have htrace : WordTrace (prefixWord ++ tailWord_2210672) baseStart_2210672 baseEnd_2210672 := by
    simpa [prefixWord, tailWord_2210672, baseEnd_2210672] using wordTrace_append hprefix tailTrace_2210672
  have hstable : (prefixWord ++ tailWord_2210672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210672).length < 2 ^ (prefixWord ++ tailWord_2210672).sum := by decide
  have hdescent : baseEnd_2210672 < baseStart_2210672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210678 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_2210678 : Nat := 118140960795 + 2210678 * 2 ^ 59
def prefixEnd_2210678 : Nat := 4983230072969 + 3 ^ 40 * 2210678 * 2
def baseEnd_2210678 : Nat := 756760257546804630572189

theorem tailTrace_2210678 : CollatzResearch.WordTrace tailWord_2210678 prefixEnd_2210678 756760257546804630572189 := by
  unfold tailWord_2210678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5039378167818664661807543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53753367123399089725947125 5039378167818664661807543)
  ·
    refine ⟨7559067251727996992711315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5039378167818664661807543 7559067251727996992711315)
    ·
      refine ⟨11338600877591995489066973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7559067251727996992711315 11338600877591995489066973)
      ·
        refine ⟨4251975329096998308400115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11338600877591995489066973 4251975329096998308400115)
        ·
          refine ⟨6377962993645497462600173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4251975329096998308400115 6377962993645497462600173)
          ·
            refine ⟨2391736122617061548475065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6377962993645497462600173 2391736122617061548475065)
            ·
              refine ⟨1793802091962796161356299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2391736122617061548475065 1793802091962796161356299)
              ·
                refine ⟨2690703137944194242034449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793802091962796161356299 2690703137944194242034449)
                ·
                  refine ⟨2018027353458145681525837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690703137944194242034449 2018027353458145681525837)
                  ·
                    refine ⟨756760257546804630572189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2018027353458145681525837 756760257546804630572189)
                    ·
                      rfl

theorem cell22_2210678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_2210678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210678 prefixEnd_2210678 := by exact prefixLift 2210678
  have htrace : WordTrace (prefixWord ++ tailWord_2210678) baseStart_2210678 baseEnd_2210678 := by
    simpa [prefixWord, tailWord_2210678, baseEnd_2210678] using wordTrace_append hprefix tailTrace_2210678
  have hstable : (prefixWord ++ tailWord_2210678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210678).length < 2 ^ (prefixWord ++ tailWord_2210678).sum := by decide
  have hdescent : baseEnd_2210678 < baseStart_2210678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210762 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_2210762 : Nat := 118140960795 + 2210762 * 2 ^ 59
def prefixEnd_2210762 : Nat := 4983230072969 + 3 ^ 40 * 2210762 * 2
def baseEnd_2210762 : Nat := 756789012463456411471931

theorem tailTrace_2210762 : CollatzResearch.WordTrace tailWord_2210762 prefixEnd_2210762 756789012463456411471931 := by
  unfold tailWord_2210762
  simp only [CollatzResearch.WordTrace]
  refine ⟨20158278604198579233744635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53755409611196211289985693 20158278604198579233744635)
  ·
    refine ⟨30237417906297868850616953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20158278604198579233744635 30237417906297868850616953)
    ·
      refine ⟨22678063429723401637962715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30237417906297868850616953 22678063429723401637962715)
      ·
        refine ⟨34017095144585102456944073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22678063429723401637962715 34017095144585102456944073)
        ·
          refine ⟨25512821358438826842708055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34017095144585102456944073 25512821358438826842708055)
          ·
            refine ⟨38269232037658240264062083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25512821358438826842708055 38269232037658240264062083)
            ·
              refine ⟨57403848056487360396093125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38269232037658240264062083 57403848056487360396093125)
              ·
                refine ⟨10763221510591380074267461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57403848056487360396093125 10763221510591380074267461)
                ·
                  refine ⟨2018104033235883763925149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10763221510591380074267461 2018104033235883763925149)
                  ·
                    refine ⟨756789012463456411471931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2018104033235883763925149 756789012463456411471931)
                    ·
                      rfl

theorem cell22_2210762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_2210762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210762 prefixEnd_2210762 := by exact prefixLift 2210762
  have htrace : WordTrace (prefixWord ++ tailWord_2210762) baseStart_2210762 baseEnd_2210762 := by
    simpa [prefixWord, tailWord_2210762, baseEnd_2210762] using wordTrace_append hprefix tailTrace_2210762
  have hstable : (prefixWord ++ tailWord_2210762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210762).length < 2 ^ (prefixWord ++ tailWord_2210762).sum := by decide
  have hdescent : baseEnd_2210762 < baseStart_2210762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210764 : List Nat := [2, 2, 1, 4, 1, 1, 4, 3, 4]
def baseStart_2210764 : Nat := 118140960795 + 2210764 * 2 ^ 59
def prefixEnd_2210764 : Nat := 4983230072969 + 3 ^ 40 * 2210764 * 2
def baseEnd_2210764 : Nat := 252263232368109690973975

theorem tailTrace_2210764 : CollatzResearch.WordTrace tailWord_2210764 prefixEnd_2210764 252263232368109690973975 := by
  unfold tailWord_2210764
  simp only [CollatzResearch.WordTrace]
  refine ⟨40316593681393535638275673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53755458241858047517700897 40316593681393535638275673)
  ·
    refine ⟨30237445261045151728706755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40316593681393535638275673 30237445261045151728706755)
    ·
      refine ⟨45356167891567727593060133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30237445261045151728706755 45356167891567727593060133)
      ·
        refine ⟨8504281479668948923698775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45356167891567727593060133 8504281479668948923698775)
        ·
          refine ⟨12756422219503423385548163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8504281479668948923698775 12756422219503423385548163)
          ·
            refine ⟨19134633329255135078322245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12756422219503423385548163 19134633329255135078322245)
            ·
              refine ⟨3587743749235337827185421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19134633329255135078322245 3587743749235337827185421)
              ·
                refine ⟨1345403905963251685194533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3587743749235337827185421 1345403905963251685194533)
                ·
                  refine ⟨252263232368109690973975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345403905963251685194533 252263232368109690973975)
                  ·
                    rfl

theorem cell22_2210764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_2210764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210764 prefixEnd_2210764 := by exact prefixLift 2210764
  have htrace : WordTrace (prefixWord ++ tailWord_2210764) baseStart_2210764 baseEnd_2210764 := by
    simpa [prefixWord, tailWord_2210764, baseEnd_2210764] using wordTrace_append hprefix tailTrace_2210764
  have hstable : (prefixWord ++ tailWord_2210764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210764).length < 2 ^ (prefixWord ++ tailWord_2210764).sum := by decide
  have hdescent : baseEnd_2210764 < baseStart_2210764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210766 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_2210766 : Nat := 118140960795 + 2210766 * 2 ^ 59
def prefixEnd_2210766 : Nat := 4983230072969 + 3 ^ 40 * 2210766 * 2
def baseEnd_2210766 : Nat := 756790381745201734371919

theorem tailTrace_2210766 : CollatzResearch.WordTrace tailWord_2210766 prefixEnd_2210766 756790381745201734371919 := by
  unfold tailWord_2210766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10079157538597478202265519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53755506872519883745416101 10079157538597478202265519)
  ·
    refine ⟨15118736307896217303398279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10079157538597478202265519 15118736307896217303398279)
    ·
      refine ⟨22678104461844325955097419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15118736307896217303398279 22678104461844325955097419)
      ·
        refine ⟨34017156692766488932646129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22678104461844325955097419 34017156692766488932646129)
        ·
          refine ⟨25512867519574866699484597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34017156692766488932646129 25512867519574866699484597)
          ·
            refine ⟨2391831329960143753076681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25512867519574866699484597 2391831329960143753076681)
            ·
              refine ⟨1793873497470107814807511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2391831329960143753076681 1793873497470107814807511)
              ·
                refine ⟨2690810246205161722211267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793873497470107814807511 2690810246205161722211267)
                ·
                  refine ⟨4036215369307742583316901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690810246205161722211267 4036215369307742583316901)
                  ·
                    refine ⟨756790381745201734371919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4036215369307742583316901 756790381745201734371919)
                    ·
                      rfl

theorem cell22_2210766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_2210766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210766 prefixEnd_2210766 := by exact prefixLift 2210766
  have htrace : WordTrace (prefixWord ++ tailWord_2210766) baseStart_2210766 baseEnd_2210766 := by
    simpa [prefixWord, tailWord_2210766, baseEnd_2210766] using wordTrace_append hprefix tailTrace_2210766
  have hstable : (prefixWord ++ tailWord_2210766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210766).length < 2 ^ (prefixWord ++ tailWord_2210766).sum := by decide
  have hdescent : baseEnd_2210766 < baseStart_2210766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210837 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 7]
def baseStart_2210837 : Nat := 118140960795 + 2210837 * 2 ^ 59
def prefixEnd_2210837 : Nat := 4983230072969 + 3 ^ 40 * 2210837 * 2
def baseEnd_2210837 : Nat := 252271562165393738615567

theorem tailTrace_2210837 : CollatzResearch.WordTrace tailWord_2210837 prefixEnd_2210837 252271562165393738615567 := by
  unfold tailWord_2210837
  simp only [CollatzResearch.WordTrace]
  refine ⟨80635849891522604743958765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53757233261015069829305843 80635849891522604743958765)
  ·
    refine ⟨30238443709320976778984537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80635849891522604743958765 30238443709320976778984537)
    ·
      refine ⟨22678832781990732584238403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30238443709320976778984537 22678832781990732584238403)
      ·
        refine ⟨34018249172986098876357605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22678832781990732584238403 34018249172986098876357605)
        ·
          refine ⟨6378421719934893539317051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34018249172986098876357605 6378421719934893539317051)
          ·
            refine ⟨9567632579902340308975577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6378421719934893539317051 9567632579902340308975577)
            ·
              refine ⟨7175724434926755231731683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9567632579902340308975577 7175724434926755231731683)
              ·
                refine ⟨10763586652390132847597525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7175724434926755231731683 10763586652390132847597525)
                ·
                  refine ⟨252271562165393738615567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10763586652390132847597525 252271562165393738615567)
                  ·
                    rfl

theorem cell22_2210837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_2210837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210837 prefixEnd_2210837 := by exact prefixLift 2210837
  have htrace : WordTrace (prefixWord ++ tailWord_2210837) baseStart_2210837 baseEnd_2210837 := by
    simpa [prefixWord, tailWord_2210837, baseEnd_2210837] using wordTrace_append hprefix tailTrace_2210837
  have hstable : (prefixWord ++ tailWord_2210837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210837).length < 2 ^ (prefixWord ++ tailWord_2210837).sum := by decide
  have hdescent : baseEnd_2210837 < baseStart_2210837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210912 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_2210912 : Nat := 118140960795 + 2210912 * 2 ^ 59
def prefixEnd_2210912 : Nat := 4983230072969 + 3 ^ 40 * 2210912 * 2
def baseEnd_2210912 : Nat := 756840360528906020221471

theorem tailTrace_2210912 : CollatzResearch.WordTrace tailWord_2210912 prefixEnd_2210912 756840360528906020221471 := by
  unfold tailWord_2210912
  simp only [CollatzResearch.WordTrace]
  refine ⟨40319292683125446276469495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53759056910833928368625993 40319292683125446276469495)
  ·
    refine ⟨60478939024688169414704243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40319292683125446276469495 60478939024688169414704243)
    ·
      refine ⟨90718408537032254122056365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60478939024688169414704243 90718408537032254122056365)
      ·
        refine ⟨34019403201387095295771137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90718408537032254122056365 34019403201387095295771137)
        ·
          refine ⟨25514552401040321471828353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34019403201387095295771137 25514552401040321471828353)
          ·
            refine ⟨19135914300780241103871265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25514552401040321471828353 19135914300780241103871265)
            ·
              refine ⟨14351935725585180827903449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19135914300780241103871265 14351935725585180827903449)
              ·
                refine ⟨10763951794188885620927587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14351935725585180827903449 10763951794188885620927587)
                ·
                  refine ⟨16145927691283328431391381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10763951794188885620927587 16145927691283328431391381)
                  ·
                    refine ⟨756840360528906020221471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16145927691283328431391381 756840360528906020221471)
                    ·
                      rfl

theorem cell22_2210912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_2210912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210912 prefixEnd_2210912 := by exact prefixLift 2210912
  have htrace : WordTrace (prefixWord ++ tailWord_2210912) baseStart_2210912 baseEnd_2210912 := by
    simpa [prefixWord, tailWord_2210912, baseEnd_2210912] using wordTrace_append hprefix tailTrace_2210912
  have hstable : (prefixWord ++ tailWord_2210912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210912).length < 2 ^ (prefixWord ++ tailWord_2210912).sum := by decide
  have hdescent : baseEnd_2210912 < baseStart_2210912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210948 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_2210948 : Nat := 118140960795 + 2210948 * 2 ^ 59
def prefixEnd_2210948 : Nat := 4983230072969 + 3 ^ 40 * 2210948 * 2
def baseEnd_2210948 : Nat := 756852684064613926321361

theorem tailTrace_2210948 : CollatzResearch.WordTrace tailWord_2210948 prefixEnd_2210948 756852684064613926321361 := by
  unfold tailWord_2210948
  simp only [CollatzResearch.WordTrace]
  refine ⟨40319949197060235350624749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53759932262746980467499665 40319949197060235350624749)
  ·
    refine ⟨15119980948897588256484281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40319949197060235350624749 15119980948897588256484281)
    ·
      refine ⟨11339985711673191192363211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15119980948897588256484281 11339985711673191192363211)
      ·
        refine ⟨17009978567509786788544817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11339985711673191192363211 17009978567509786788544817)
        ·
          refine ⟨12757483925632340091408613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17009978567509786788544817 12757483925632340091408613)
          ·
            refine ⟨2392028236056063767139115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12757483925632340091408613 2392028236056063767139115)
            ·
              refine ⟨3588042354084095650708673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392028236056063767139115 3588042354084095650708673)
              ·
                refine ⟨2691031765563071738031505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588042354084095650708673 2691031765563071738031505)
                ·
                  refine ⟨2018273824172303803523629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2691031765563071738031505 2018273824172303803523629)
                  ·
                    refine ⟨756852684064613926321361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2018273824172303803523629 756852684064613926321361)
                    ·
                      rfl

theorem cell22_2210948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_2210948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210948 prefixEnd_2210948 := by exact prefixLift 2210948
  have htrace : WordTrace (prefixWord ++ tailWord_2210948) baseStart_2210948 baseEnd_2210948 := by
    simpa [prefixWord, tailWord_2210948, baseEnd_2210948] using wordTrace_append hprefix tailTrace_2210948
  have hstable : (prefixWord ++ tailWord_2210948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210948).length < 2 ^ (prefixWord ++ tailWord_2210948).sum := by decide
  have hdescent : baseEnd_2210948 < baseStart_2210948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2210978 : List Nat := [3, 3, 1, 3, 2, 2, 2, 6]
def baseStart_2210978 : Nat := 118140960795 + 2210978 * 2 ^ 59
def prefixEnd_2210978 : Nat := 4983230072969 + 3 ^ 40 * 2210978 * 2
def baseEnd_2210978 : Nat := 84095883741967094230141

theorem tailTrace_2210978 : CollatzResearch.WordTrace tailWord_2210978 prefixEnd_2210978 84095883741967094230141 := by
  unfold tailWord_2210978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20160248146002946456210397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53760661722674523883227725 20160248146002946456210397)
  ·
    refine ⟨7560093054751104921078899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20160248146002946456210397 7560093054751104921078899)
    ·
      refine ⟨11340139582126657381618349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7560093054751104921078899 11340139582126657381618349)
      ·
        refine ⟨4252552343297496518106881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11340139582126657381618349 4252552343297496518106881)
        ·
          refine ⟨3189414257473122388580161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4252552343297496518106881 3189414257473122388580161)
          ·
            refine ⟨2392060693104841791435121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3189414257473122388580161 2392060693104841791435121)
            ·
              refine ⟨1794045519828631343576341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392060693104841791435121 1794045519828631343576341)
              ·
                refine ⟨84095883741967094230141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1794045519828631343576341 84095883741967094230141)
                ·
                  rfl

theorem cell22_2210978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_2210978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2210978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2210978 prefixEnd_2210978 := by exact prefixLift 2210978
  have htrace : WordTrace (prefixWord ++ tailWord_2210978) baseStart_2210978 baseEnd_2210978 := by
    simpa [prefixWord, tailWord_2210978, baseEnd_2210978] using wordTrace_append hprefix tailTrace_2210978
  have hstable : (prefixWord ++ tailWord_2210978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2210978).length < 2 ^ (prefixWord ++ tailWord_2210978).sum := by decide
  have hdescent : baseEnd_2210978 < baseStart_2210978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2210978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211068 : List Nat := [2, 2, 2, 1, 5, 1, 1, 4, 4]
def baseStart_2211068 : Nat := 118140960795 + 2211068 * 2 ^ 59
def prefixEnd_2211068 : Nat := 4983230072969 + 3 ^ 40 * 2211068 * 2
def baseEnd_2211068 : Nat := 252297920838991204440331

theorem tailTrace_2211068 : CollatzResearch.WordTrace tailWord_2211068 prefixEnd_2211068 252297920838991204440331 := by
  unfold tailWord_2211068
  simp only [CollatzResearch.WordTrace]
  refine ⟨40322137576842865597808929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53762850102457154130411905 40322137576842865597808929)
  ·
    refine ⟨30241603182632149198356697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40322137576842865597808929 30241603182632149198356697)
    ·
      refine ⟨22681202386974111898767523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30241603182632149198356697 22681202386974111898767523)
      ·
        refine ⟨34021803580461167848151285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22681202386974111898767523 34021803580461167848151285)
        ·
          refine ⟨3189544085668234485764183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34021803580461167848151285 3189544085668234485764183)
          ·
            refine ⟨4784316128502351728646275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3189544085668234485764183 4784316128502351728646275)
            ·
              refine ⟨7176474192753527592969413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4784316128502351728646275 7176474192753527592969413)
              ·
                refine ⟨1345588911141286423681765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7176474192753527592969413 1345588911141286423681765)
                ·
                  refine ⟨252297920838991204440331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345588911141286423681765 252297920838991204440331)
                  ·
                    rfl

theorem cell22_2211068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_2211068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211068 prefixEnd_2211068 := by exact prefixLift 2211068
  have htrace : WordTrace (prefixWord ++ tailWord_2211068) baseStart_2211068 baseEnd_2211068 := by
    simpa [prefixWord, tailWord_2211068, baseEnd_2211068] using wordTrace_append hprefix tailTrace_2211068
  have hstable : (prefixWord ++ tailWord_2211068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211068).length < 2 ^ (prefixWord ++ tailWord_2211068).sum := by decide
  have hdescent : baseEnd_2211068 < baseStart_2211068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211096 : List Nat := [2, 1, 2, 3, 1, 4, 3, 6]
def baseStart_2211096 : Nat := 118140960795 + 2211096 * 2 ^ 59
def prefixEnd_2211096 : Nat := 4983230072969 + 3 ^ 40 * 2211096 * 2
def baseEnd_2211096 : Nat := 84100371943243430402323

theorem tailTrace_2211096 : CollatzResearch.WordTrace tailWord_2211096 prefixEnd_2211096 84100371943243430402323 := by
  unfold tailWord_2211096
  simp only [CollatzResearch.WordTrace]
  refine ⟨40322648198792145988818571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53763530931722861318424761 40322648198792145988818571)
  ·
    refine ⟨60483972298188218983227857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40322648198792145988818571 60483972298188218983227857)
    ·
      refine ⟨45362979223641164237420893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60483972298188218983227857 45362979223641164237420893)
      ·
        refine ⟨17011117208865436589032835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45362979223641164237420893 17011117208865436589032835)
        ·
          refine ⟨25516675813298154883549253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17011117208865436589032835 25516675813298154883549253)
          ·
            refine ⟨4784376714993404040665485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25516675813298154883549253 4784376714993404040665485)
            ·
              refine ⟨1794141268122526515249557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4784376714993404040665485 1794141268122526515249557)
              ·
                refine ⟨84100371943243430402323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1794141268122526515249557 84100371943243430402323)
                ·
                  rfl

theorem cell22_2211096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 6].length) (baseStart_2211096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211096 prefixEnd_2211096 := by exact prefixLift 2211096
  have htrace : WordTrace (prefixWord ++ tailWord_2211096) baseStart_2211096 baseEnd_2211096 := by
    simpa [prefixWord, tailWord_2211096, baseEnd_2211096] using wordTrace_append hprefix tailTrace_2211096
  have hstable : (prefixWord ++ tailWord_2211096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211096).length < 2 ^ (prefixWord ++ tailWord_2211096).sum := by decide
  have hdescent : baseEnd_2211096 < baseStart_2211096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211098 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_2211098 : Nat := 118140960795 + 2211098 * 2 ^ 59
def prefixEnd_2211098 : Nat := 4983230072969 + 3 ^ 40 * 2211098 * 2
def baseEnd_2211098 : Nat := 756904032130063535070901

theorem tailTrace_2211098 : CollatzResearch.WordTrace tailWord_2211098 prefixEnd_2211098 756904032130063535070901 := by
  unfold tailWord_2211098
  simp only [CollatzResearch.WordTrace]
  refine ⟨20161342335894261579802487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53763579562384697546139965 20161342335894261579802487)
  ·
    refine ⟨30242013503841392369703731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20161342335894261579802487 30242013503841392369703731)
    ·
      refine ⟨45363020255762088554555597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30242013503841392369703731 45363020255762088554555597)
      ·
        refine ⟨17011132595910783207958349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45363020255762088554555597 17011132595910783207958349)
        ·
          refine ⟨6379174723466543702984381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17011132595910783207958349 6379174723466543702984381)
          ·
            refine ⟨2392190521299953888619143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6379174723466543702984381 2392190521299953888619143)
            ·
              refine ⟨3588285781949930832928715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392190521299953888619143 3588285781949930832928715)
              ·
                refine ⟨5382428672924896249393073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3588285781949930832928715 5382428672924896249393073)
                ·
                  refine ⟨4036821504693672187044805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5382428672924896249393073 4036821504693672187044805)
                  ·
                    refine ⟨756904032130063535070901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4036821504693672187044805 756904032130063535070901)
                    ·
                      rfl

theorem cell22_2211098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_2211098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211098 prefixEnd_2211098 := by exact prefixLift 2211098
  have htrace : WordTrace (prefixWord ++ tailWord_2211098) baseStart_2211098 baseEnd_2211098 := by
    simpa [prefixWord, tailWord_2211098, baseEnd_2211098] using wordTrace_append hprefix tailTrace_2211098
  have hstable : (prefixWord ++ tailWord_2211098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211098).length < 2 ^ (prefixWord ++ tailWord_2211098).sum := by decide
  have hdescent : baseEnd_2211098 < baseStart_2211098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211102 : List Nat := [4, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_2211102 : Nat := 118140960795 + 2211102 * 2 ^ 59
def prefixEnd_2211102 : Nat := 4983230072969 + 3 ^ 40 * 2211102 * 2
def baseEnd_2211102 : Nat := 252301800470602952656963

theorem tailTrace_2211102 : CollatzResearch.WordTrace tailWord_2211102 prefixEnd_2211102 252301800470602952656963 := by
  unfold tailWord_2211102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10080689404445319375294445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53763676823708370001570373 10080689404445319375294445)
  ·
    refine ⟨3780258526666994765735417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10080689404445319375294445 3780258526666994765735417)
    ·
      refine ⟨2835193895000246074301563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3780258526666994765735417 2835193895000246074301563)
      ·
        refine ⟨4252790842500369111452345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835193895000246074301563 4252790842500369111452345)
        ·
          refine ⟨3189593131875276833589259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4252790842500369111452345 3189593131875276833589259)
          ·
            refine ⟨4784389697812915250383889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3189593131875276833589259 4784389697812915250383889)
            ·
              refine ⟨3588292273359686437787917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4784389697812915250383889 3588292273359686437787917)
              ·
                refine ⟨1345609602509882414170469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3588292273359686437787917 1345609602509882414170469)
                ·
                  refine ⟨252301800470602952656963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345609602509882414170469 252301800470602952656963)
                  ·
                    rfl

theorem cell22_2211102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_2211102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211102 prefixEnd_2211102 := by exact prefixLift 2211102
  have htrace : WordTrace (prefixWord ++ tailWord_2211102) baseStart_2211102 baseEnd_2211102 := by
    simpa [prefixWord, tailWord_2211102, baseEnd_2211102] using wordTrace_append hprefix tailTrace_2211102
  have hstable : (prefixWord ++ tailWord_2211102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211102).length < 2 ^ (prefixWord ++ tailWord_2211102).sum := by decide
  have hdescent : baseEnd_2211102 < baseStart_2211102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211117 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2211117 : Nat := 118140960795 + 2211117 * 2 ^ 59
def prefixEnd_2211117 : Nat := 4983230072969 + 3 ^ 40 * 2211117 * 2
def baseEnd_2211117 : Nat := 756910536218353818845843

theorem tailTrace_2211117 : CollatzResearch.WordTrace tailWord_2211117 prefixEnd_2211117 756910536218353818845843 := by
  unfold tailWord_2211117
  simp only [CollatzResearch.WordTrace]
  refine ⟨80646062330508212564151605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53764041553672141709434403 80646062330508212564151605)
  ·
    refine ⟨7560568343485144927889213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80646062330508212564151605 7560568343485144927889213)
    ·
      refine ⟨2835213128806929347958455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7560568343485144927889213 2835213128806929347958455)
      ·
        refine ⟨4252819693210394021937683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835213128806929347958455 4252819693210394021937683)
        ·
          refine ⟨6379229539815591032906525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4252819693210394021937683 6379229539815591032906525)
          ·
            refine ⟨2392211077430846637339947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6379229539815591032906525 2392211077430846637339947)
            ·
              refine ⟨3588316616146269956009921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392211077430846637339947 3588316616146269956009921)
              ·
                refine ⟨2691237462109702467007441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588316616146269956009921 2691237462109702467007441)
                ·
                  refine ⟨2018428096582276850255581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2691237462109702467007441 2018428096582276850255581)
                  ·
                    refine ⟨756910536218353818845843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2018428096582276850255581 756910536218353818845843)
                    ·
                      rfl

theorem cell22_2211117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2211117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211117 prefixEnd_2211117 := by exact prefixLift 2211117
  have htrace : WordTrace (prefixWord ++ tailWord_2211117) baseStart_2211117 baseEnd_2211117 := by
    simpa [prefixWord, tailWord_2211117, baseEnd_2211117] using wordTrace_append hprefix tailTrace_2211117
  have hstable : (prefixWord ++ tailWord_2211117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211117).length < 2 ^ (prefixWord ++ tailWord_2211117).sum := by decide
  have hdescent : baseEnd_2211117 < baseStart_2211117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211169 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 8]
def baseStart_2211169 : Nat := 118140960795 + 2211169 * 2 ^ 59
def prefixEnd_2211169 : Nat := 4983230072969 + 3 ^ 40 * 2211169 * 2
def baseEnd_2211169 : Nat := 252309445627014338848561

theorem tailTrace_2211169 : CollatzResearch.WordTrace tailWord_2211169 prefixEnd_2211169 252309445627014338848561 := by
  unfold tailWord_2211169
  simp only [CollatzResearch.WordTrace]
  refine ⟨80647958926319825445044561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53765305950879883630029707 80647958926319825445044561)
  ·
    refine ⟨60485969194739869083783421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80647958926319825445044561 60485969194739869083783421)
    ·
      refine ⟨22682238448027450906418783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60485969194739869083783421 22682238448027450906418783)
      ·
        refine ⟨34023357672041176359628175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22682238448027450906418783 34023357672041176359628175)
        ·
          refine ⟨51035036508061764539442263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34023357672041176359628175 51035036508061764539442263)
          ·
            refine ⟨76552554762092646809163395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51035036508061764539442263 76552554762092646809163395)
            ·
              refine ⟨114828832143138970213745093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76552554762092646809163395 114828832143138970213745093)
              ·
                refine ⟨21530406026838556915077205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114828832143138970213745093 21530406026838556915077205)
                ·
                  refine ⟨252309445627014338848561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21530406026838556915077205 252309445627014338848561)
                  ·
                    rfl

theorem cell22_2211169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_2211169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211169 prefixEnd_2211169 := by exact prefixLift 2211169
  have htrace : WordTrace (prefixWord ++ tailWord_2211169) baseStart_2211169 baseEnd_2211169 := by
    simpa [prefixWord, tailWord_2211169, baseEnd_2211169] using wordTrace_append hprefix tailTrace_2211169
  have hstable : (prefixWord ++ tailWord_2211169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211169).length < 2 ^ (prefixWord ++ tailWord_2211169).sum := by decide
  have hdescent : baseEnd_2211169 < baseStart_2211169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211261 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2211261 : Nat := 118140960795 + 2211261 * 2 ^ 59
def prefixEnd_2211261 : Nat := 4983230072969 + 3 ^ 40 * 2211261 * 2
def baseEnd_2211261 : Nat := 756959830361185443245401

theorem tailTrace_2211261 : CollatzResearch.WordTrace tailWord_2211261 prefixEnd_2211261 756959830361185443245401 := by
  unfold tailWord_2211261
  simp only [CollatzResearch.WordTrace]
  refine ⟨80651314441986525157393637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53767542961324350104929091 80651314441986525157393637)
  ·
    refine ⟨15122121457872473467011307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80651314441986525157393637 15122121457872473467011307)
    ·
      refine ⟨22683182186808710200516961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15122121457872473467011307 22683182186808710200516961)
      ·
        refine ⟨17012386640106532650387721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22683182186808710200516961 17012386640106532650387721)
        ·
          refine ⟨12759289980079899487790791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17012386640106532650387721 12759289980079899487790791)
          ·
            refine ⟨19138934970119849231686187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12759289980079899487790791 19138934970119849231686187)
            ·
              refine ⟨28708402455179773847529281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19138934970119849231686187 28708402455179773847529281)
              ·
                refine ⟨21531301841384830385646961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28708402455179773847529281 21531301841384830385646961)
                ·
                  refine ⟨16148476381038622789235221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21531301841384830385646961 16148476381038622789235221)
                  ·
                    refine ⟨756959830361185443245401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16148476381038622789235221 756959830361185443245401)
                    ·
                      rfl

theorem cell22_2211261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2211261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211261 prefixEnd_2211261 := by exact prefixLift 2211261
  have htrace : WordTrace (prefixWord ++ tailWord_2211261) baseStart_2211261 baseEnd_2211261 := by
    simpa [prefixWord, tailWord_2211261, baseEnd_2211261] using wordTrace_append hprefix tailTrace_2211261
  have hstable : (prefixWord ++ tailWord_2211261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211261).length < 2 ^ (prefixWord ++ tailWord_2211261).sum := by decide
  have hdescent : baseEnd_2211261 < baseStart_2211261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211293 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 7]
def baseStart_2211293 : Nat := 118140960795 + 2211293 * 2 ^ 59
def prefixEnd_2211293 : Nat := 4983230072969 + 3 ^ 40 * 2211293 * 2
def baseEnd_2211293 : Nat := 252323594871716008815101

theorem tailTrace_2211293 : CollatzResearch.WordTrace tailWord_2211293 prefixEnd_2211293 252323594871716008815101 := by
  unfold tailWord_2211293
  simp only [CollatzResearch.WordTrace]
  refine ⟨80652481577870594622558533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53768321051913729748372355 80652481577870594622558533)
  ·
    refine ⟨15122340295850736491729725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80652481577870594622558533 15122340295850736491729725)
    ·
      refine ⟨5670877610944026184398647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15122340295850736491729725 5670877610944026184398647)
      ·
        refine ⟨8506316416416039276597971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5670877610944026184398647 8506316416416039276597971)
        ·
          refine ⟨12759474624624058914896957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8506316416416039276597971 12759474624624058914896957)
          ·
            refine ⟨4784802984234022093086359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12759474624624058914896957 4784802984234022093086359)
            ·
              refine ⟨7177204476351033139629539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4784802984234022093086359 7177204476351033139629539)
              ·
                refine ⟨10765806714526549709444309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7177204476351033139629539 10765806714526549709444309)
                ·
                  refine ⟨252323594871716008815101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10765806714526549709444309 252323594871716008815101)
                  ·
                    rfl

theorem cell22_2211293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_2211293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211293 prefixEnd_2211293 := by exact prefixLift 2211293
  have htrace : WordTrace (prefixWord ++ tailWord_2211293) baseStart_2211293 baseEnd_2211293 := by
    simpa [prefixWord, tailWord_2211293, baseEnd_2211293] using wordTrace_append hprefix tailTrace_2211293
  have hstable : (prefixWord ++ tailWord_2211293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211293).length < 2 ^ (prefixWord ++ tailWord_2211293).sum := by decide
  have hdescent : baseEnd_2211293 < baseStart_2211293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211310 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_2211310 : Nat := 118140960795 + 2211310 * 2 ^ 59
def prefixEnd_2211310 : Nat := 4983230072969 + 3 ^ 40 * 2211310 * 2
def baseEnd_2211310 : Nat := 252325534687521882923417

theorem tailTrace_2211310 : CollatzResearch.WordTrace tailWord_2211310 prefixEnd_2211310 252325534687521882923417 := by
  unfold tailWord_2211310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10081637702351125815740923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53768734412539337683951589 10081637702351125815740923)
  ·
    refine ⟨15122456553526688723611385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10081637702351125815740923 15122456553526688723611385)
    ·
      refine ⟨11341842415145016542708539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15122456553526688723611385 11341842415145016542708539)
      ·
        refine ⟨17012763622717524814062809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11341842415145016542708539 17012763622717524814062809)
        ·
          refine ⟨12759572717038143610547107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17012763622717524814062809 12759572717038143610547107)
          ·
            refine ⟨19139359075557215415820661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12759572717038143610547107 19139359075557215415820661)
            ·
              refine ⟨1794314913333488945233187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19139359075557215415820661 1794314913333488945233187)
              ·
                refine ⟨2691472370000233417849781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794314913333488945233187 2691472370000233417849781)
                ·
                  refine ⟨252325534687521882923417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2691472370000233417849781 252325534687521882923417)
                  ·
                    rfl

theorem cell22_2211310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_2211310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211310 prefixEnd_2211310 := by exact prefixLift 2211310
  have htrace : WordTrace (prefixWord ++ tailWord_2211310) baseStart_2211310 baseEnd_2211310 := by
    simpa [prefixWord, tailWord_2211310, baseEnd_2211310] using wordTrace_append hprefix tailTrace_2211310
  have hstable : (prefixWord ++ tailWord_2211310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211310).length < 2 ^ (prefixWord ++ tailWord_2211310).sum := by decide
  have hdescent : baseEnd_2211310 < baseStart_2211310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211385 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_2211385 : Nat := 118140960795 + 2211385 * 2 ^ 59
def prefixEnd_2211385 : Nat := 4983230072969 + 3 ^ 40 * 2211385 * 2
def baseEnd_2211385 : Nat := 757002278095290453145021

theorem tailTrace_2211385 : CollatzResearch.WordTrace tailWord_2211385 prefixEnd_2211385 757002278095290453145021 := by
  unfold tailWord_2211385
  simp only [CollatzResearch.WordTrace]
  refine ⟨80655837093537294334907609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53770558062358196223271739 80655837093537294334907609)
  ·
    refine ⟨60491877820152970751180707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80655837093537294334907609 60491877820152970751180707)
    ·
      refine ⟨90737816730229456126771061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60491877820152970751180707 90737816730229456126771061)
      ·
        refine ⟨8506670318459011511884787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90737816730229456126771061 8506670318459011511884787)
        ·
          refine ⟨12760005477688517267827181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8506670318459011511884787 12760005477688517267827181)
          ·
            refine ⟨4785002054133193975435193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12760005477688517267827181 4785002054133193975435193)
            ·
              refine ⟨3588751540599895481576395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785002054133193975435193 3588751540599895481576395)
              ·
                refine ⟨5383127310899843222364593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3588751540599895481576395 5383127310899843222364593)
                ·
                  refine ⟨4037345483174882416773445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5383127310899843222364593 4037345483174882416773445)
                  ·
                    refine ⟨757002278095290453145021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037345483174882416773445 757002278095290453145021)
                    ·
                      rfl

theorem cell22_2211385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_2211385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211385 prefixEnd_2211385 := by exact prefixLift 2211385
  have htrace : WordTrace (prefixWord ++ tailWord_2211385) baseStart_2211385 baseEnd_2211385 := by
    simpa [prefixWord, tailWord_2211385, baseEnd_2211385] using wordTrace_append hprefix tailTrace_2211385
  have hstable : (prefixWord ++ tailWord_2211385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211385).length < 2 ^ (prefixWord ++ tailWord_2211385).sum := by decide
  have hdescent : baseEnd_2211385 < baseStart_2211385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211432 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 3, 3]
def baseStart_2211432 : Nat := 118140960795 + 2211432 * 2 ^ 59
def prefixEnd_2211432 : Nat := 4983230072969 + 3 ^ 40 * 2211432 * 2
def baseEnd_2211432 : Nat := 757018367155797997219877

theorem tailTrace_2211432 : CollatzResearch.WordTrace tailWord_2211432 prefixEnd_2211432 757018367155797997219877 := by
  unfold tailWord_2211432
  simp only [CollatzResearch.WordTrace]
  refine ⟨40328775662183510680934275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53771700882911347574579033 40328775662183510680934275)
  ·
    refine ⟨60493163493275266021401413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40328775662183510680934275 60493163493275266021401413)
    ·
      refine ⟨11342468154989112379012765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60493163493275266021401413 11342468154989112379012765)
      ·
        refine ⟨4253425558120917142129787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11342468154989112379012765 4253425558120917142129787)
        ·
          refine ⟨6380138337181375713194681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4253425558120917142129787 6380138337181375713194681)
          ·
            refine ⟨4785103752886031784896011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6380138337181375713194681 4785103752886031784896011)
            ·
              refine ⟨7177655629329047677344017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4785103752886031784896011 7177655629329047677344017)
              ·
                refine ⟨5383241721996785758008013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7177655629329047677344017 5383241721996785758008013)
                ·
                  refine ⟨2018715645748794659253005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5383241721996785758008013 2018715645748794659253005)
                  ·
                    refine ⟨757018367155797997219877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2018715645748794659253005 757018367155797997219877)
                    ·
                      rfl

theorem cell22_2211432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_2211432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211432 prefixEnd_2211432 := by exact prefixLift 2211432
  have htrace : WordTrace (prefixWord ++ tailWord_2211432) baseStart_2211432 baseEnd_2211432 := by
    simpa [prefixWord, tailWord_2211432, baseEnd_2211432] using wordTrace_append hprefix tailTrace_2211432
  have hstable : (prefixWord ++ tailWord_2211432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211432).length < 2 ^ (prefixWord ++ tailWord_2211432).sum := by decide
  have hdescent : baseEnd_2211432 < baseStart_2211432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211492 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_2211492 : Nat := 118140960795 + 2211492 * 2 ^ 59
def prefixEnd_2211492 : Nat := 4983230072969 + 3 ^ 40 * 2211492 * 2
def baseEnd_2211492 : Nat := 757038906381977840719693

theorem tailTrace_2211492 : CollatzResearch.WordTrace tailWord_2211492 prefixEnd_2211492 757038906381977840719693 := by
  unfold tailWord_2211492
  simp only [CollatzResearch.WordTrace]
  refine ⟨40329869852074825804526365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53773159802766434406035153 40329869852074825804526365)
  ·
    refine ⟨15123701194528059676697387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40329869852074825804526365 15123701194528059676697387)
    ·
      refine ⟨22685551791792089515046081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15123701194528059676697387 22685551791792089515046081)
      ·
        refine ⟨17014163843844067136284561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22685551791792089515046081 17014163843844067136284561)
        ·
          refine ⟨12760622882883050352213421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17014163843844067136284561 12760622882883050352213421)
          ·
            refine ⟨4785233581081143882080033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12760622882883050352213421 4785233581081143882080033)
            ·
              refine ⟨3588925185810857911560025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785233581081143882080033 3588925185810857911560025)
              ·
                refine ⟨2691693889358143433670019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588925185810857911560025 2691693889358143433670019)
                ·
                  refine ⟨4037540834037215150505029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691693889358143433670019 4037540834037215150505029)
                  ·
                    refine ⟨757038906381977840719693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037540834037215150505029 757038906381977840719693)
                    ·
                      rfl

theorem cell22_2211492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_2211492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211492 prefixEnd_2211492 := by exact prefixLift 2211492
  have htrace : WordTrace (prefixWord ++ tailWord_2211492) baseStart_2211492 baseEnd_2211492 := by
    simpa [prefixWord, tailWord_2211492, baseEnd_2211492] using wordTrace_append hprefix tailTrace_2211492
  have hstable : (prefixWord ++ tailWord_2211492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211492).length < 2 ^ (prefixWord ++ tailWord_2211492).sum := by decide
  have hdescent : baseEnd_2211492 < baseStart_2211492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211503 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 1, 6]
def baseStart_2211503 : Nat := 118140960795 + 2211503 * 2 ^ 59
def prefixEnd_2211503 : Nat := 4983230072969 + 3 ^ 40 * 2211503 * 2
def baseEnd_2211503 : Nat := 757042671906777478694659

theorem tailTrace_2211503 : CollatzResearch.WordTrace tailWord_2211503 prefixEnd_2211503 757042671906777478694659 := by
  unfold tailWord_2211503
  simp only [CollatzResearch.WordTrace]
  refine ⟨80660140907109800487703163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53773427271406533658468775 80660140907109800487703163)
  ·
    refine ⟨120990211360664700731554745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80660140907109800487703163 120990211360664700731554745)
    ·
      refine ⟨90742658520498525548666059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120990211360664700731554745 90742658520498525548666059)
      ·
        refine ⟨136113987780747788322999089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90742658520498525548666059 136113987780747788322999089)
        ·
          refine ⟨102085490835560841242249317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136113987780747788322999089 102085490835560841242249317)
          ·
            refine ⟨19141029531667657732921747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102085490835560841242249317 19141029531667657732921747)
            ·
              refine ⟨28711544297501486599382621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19141029531667657732921747 28711544297501486599382621)
              ·
                refine ⟨10766829111563057474768483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28711544297501486599382621 10766829111563057474768483)
                ·
                  refine ⟨16150243667344586212152725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10766829111563057474768483 16150243667344586212152725)
                  ·
                    refine ⟨757042671906777478694659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16150243667344586212152725 757042671906777478694659)
                    ·
                      rfl

theorem cell22_2211503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_2211503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211503 prefixEnd_2211503 := by exact prefixLift 2211503
  have htrace : WordTrace (prefixWord ++ tailWord_2211503) baseStart_2211503 baseEnd_2211503 := by
    simpa [prefixWord, tailWord_2211503, baseEnd_2211503] using wordTrace_append hprefix tailTrace_2211503
  have hstable : (prefixWord ++ tailWord_2211503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211503).length < 2 ^ (prefixWord ++ tailWord_2211503).sum := by decide
  have hdescent : baseEnd_2211503 < baseStart_2211503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211520 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_2211520 : Nat := 118140960795 + 2211520 * 2 ^ 59
def prefixEnd_2211520 : Nat := 4983230072969 + 3 ^ 40 * 2211520 * 2
def baseEnd_2211520 : Nat := 757048491354195101019607

theorem tailTrace_2211520 : CollatzResearch.WordTrace tailWord_2211520 prefixEnd_2211520 757048491354195101019607 := by
  unfold tailWord_2211520
  simp only [CollatzResearch.WordTrace]
  refine ⟨40330380474024106195536007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53773840632032141594048009 40330380474024106195536007)
  ·
    refine ⟨60495570711036159293304011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40330380474024106195536007 60495570711036159293304011)
    ·
      refine ⟨90743356066554238939956017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60495570711036159293304011 90743356066554238939956017)
      ·
        refine ⟨68057517049915679204967013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90743356066554238939956017 68057517049915679204967013)
        ·
          refine ⟨12760784446859189850931315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68057517049915679204967013 12760784446859189850931315)
          ·
            refine ⟨19141176670288784776396973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12760784446859189850931315 19141176670288784776396973)
            ·
              refine ⟨7177941251358294291148865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19141176670288784776396973 7177941251358294291148865)
              ·
                refine ⟨5383455938518720718361649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7177941251358294291148865 5383455938518720718361649)
                ·
                  refine ⟨4037591953889040538771237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5383455938518720718361649 4037591953889040538771237)
                  ·
                    refine ⟨757048491354195101019607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037591953889040538771237 757048491354195101019607)
                    ·
                      rfl

theorem cell22_2211520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_2211520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211520 prefixEnd_2211520 := by exact prefixLift 2211520
  have htrace : WordTrace (prefixWord ++ tailWord_2211520) baseStart_2211520 baseEnd_2211520 := by
    simpa [prefixWord, tailWord_2211520, baseEnd_2211520] using wordTrace_append hprefix tailTrace_2211520
  have hstable : (prefixWord ++ tailWord_2211520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211520).length < 2 ^ (prefixWord ++ tailWord_2211520).sum := by decide
  have hdescent : baseEnd_2211520 < baseStart_2211520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211524 : List Nat := [2, 3, 3, 1, 1, 1, 5, 2, 4]
def baseStart_2211524 : Nat := 118140960795 + 2211524 * 2 ^ 59
def prefixEnd_2211524 : Nat := 4983230072969 + 3 ^ 40 * 2211524 * 2
def baseEnd_2211524 : Nat := 252349953545313474639865

theorem tailTrace_2211524 : CollatzResearch.WordTrace tailWord_2211524 prefixEnd_2211524 252349953545313474639865 := by
  unfold tailWord_2211524
  simp only [CollatzResearch.WordTrace]
  refine ⟨40330453420016860537108813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53773937893355814049478417 40330453420016860537108813)
  ·
    refine ⟨15123920032506322701415805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40330453420016860537108813 15123920032506322701415805)
    ·
      refine ⟨5671470012189871013030927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15123920032506322701415805 5671470012189871013030927)
      ·
        refine ⟨8507205018284806519546391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5671470012189871013030927 8507205018284806519546391)
        ·
          refine ⟨12760807527427209779319587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8507205018284806519546391 12760807527427209779319587)
          ·
            refine ⟨19141211291140814668979381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12760807527427209779319587 19141211291140814668979381)
            ·
              refine ⟨1794488558544451375216817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19141211291140814668979381 1794488558544451375216817)
              ·
                refine ⟨1345866418908338531412613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794488558544451375216817 1345866418908338531412613)
                ·
                  refine ⟨252349953545313474639865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1345866418908338531412613 252349953545313474639865)
                  ·
                    rfl

theorem cell22_2211524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_2211524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211524 prefixEnd_2211524 := by exact prefixLift 2211524
  have htrace : WordTrace (prefixWord ++ tailWord_2211524) baseStart_2211524 baseEnd_2211524 := by
    simpa [prefixWord, tailWord_2211524, baseEnd_2211524] using wordTrace_append hprefix tailTrace_2211524
  have hstable : (prefixWord ++ tailWord_2211524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211524).length < 2 ^ (prefixWord ++ tailWord_2211524).sum := by decide
  have hdescent : baseEnd_2211524 < baseStart_2211524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211563 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 9]
def baseStart_2211563 : Nat := 118140960795 + 2211563 * 2 ^ 59
def prefixEnd_2211563 : Nat := 4983230072969 + 3 ^ 40 * 2211563 * 2
def baseEnd_2211563 : Nat := 252354403710985774064825

theorem tailTrace_2211563 : CollatzResearch.WordTrace tailWord_2211563 prefixEnd_2211563 252354403710985774064825 := by
  unfold tailWord_2211563
  simp only [CollatzResearch.WordTrace]
  refine ⟨80662329286892430734887343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53774886191261620489924895 80662329286892430734887343)
  ·
    refine ⟨120993493930338646102331015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80662329286892430734887343 120993493930338646102331015)
    ·
      refine ⟨181490240895507969153496523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120993493930338646102331015 181490240895507969153496523)
      ·
        refine ⟨272235361343261953730244785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181490240895507969153496523 272235361343261953730244785)
        ·
          refine ⟨204176521007446465297683589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272235361343261953730244785 204176521007446465297683589)
          ·
            refine ⟨38283097688896212243315673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204176521007446465297683589 38283097688896212243315673)
            ·
              refine ⟨28712323266672159182486755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38283097688896212243315673 28712323266672159182486755)
              ·
                refine ⟨43068484900008238773730133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28712323266672159182486755 43068484900008238773730133)
                ·
                  refine ⟨252354403710985774064825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43068484900008238773730133 252354403710985774064825)
                  ·
                    rfl

theorem cell22_2211563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 9].length) (baseStart_2211563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211563 prefixEnd_2211563 := by exact prefixLift 2211563
  have htrace : WordTrace (prefixWord ++ tailWord_2211563) baseStart_2211563 baseEnd_2211563 := by
    simpa [prefixWord, tailWord_2211563, baseEnd_2211563] using wordTrace_append hprefix tailTrace_2211563
  have hstable : (prefixWord ++ tailWord_2211563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211563).length < 2 ^ (prefixWord ++ tailWord_2211563).sum := by decide
  have hdescent : baseEnd_2211563 < baseStart_2211563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211590 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2211590 : Nat := 118140960795 + 2211590 * 2 ^ 59
def prefixEnd_2211590 : Nat := 4983230072969 + 3 ^ 40 * 2211590 * 2
def baseEnd_2211590 : Nat := 757072453784738251769393

theorem tailTrace_2211590 : CollatzResearch.WordTrace tailWord_2211590 prefixEnd_2211590 757072453784738251769393 := by
  unfold tailWord_2211590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520728564306081698316257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53775542705196409564080149 2520728564306081698316257)
  ·
    refine ⟨1890546423229561273737193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2520728564306081698316257 1890546423229561273737193)
    ·
      refine ⟨1417909817422170955302895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1890546423229561273737193 1417909817422170955302895)
      ·
        refine ⟨2126864726133256432954343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417909817422170955302895 2126864726133256432954343)
        ·
          refine ⟨3190297089199884649431515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2126864726133256432954343 3190297089199884649431515)
          ·
            refine ⟨4785445633799826974147273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190297089199884649431515 4785445633799826974147273)
            ·
              refine ⟨3589084225349870230610455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785445633799826974147273 3589084225349870230610455)
              ·
                refine ⟨5383626338024805345915683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589084225349870230610455 5383626338024805345915683)
                ·
                  refine ⟨8075439507037208018873525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5383626338024805345915683 8075439507037208018873525)
                  ·
                    refine ⟨757072453784738251769393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8075439507037208018873525 757072453784738251769393)
                    ·
                      rfl

theorem cell22_2211590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2211590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211590 prefixEnd_2211590 := by exact prefixLift 2211590
  have htrace : WordTrace (prefixWord ++ tailWord_2211590) baseStart_2211590 baseEnd_2211590 := by
    simpa [prefixWord, tailWord_2211590, baseEnd_2211590] using wordTrace_append hprefix tailTrace_2211590
  have hstable : (prefixWord ++ tailWord_2211590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211590).length < 2 ^ (prefixWord ++ tailWord_2211590).sum := by decide
  have hdescent : baseEnd_2211590 < baseStart_2211590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211642 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_2211642 : Nat := 118140960795 + 2211642 * 2 ^ 59
def prefixEnd_2211642 : Nat := 4983230072969 + 3 ^ 40 * 2211642 * 2
def baseEnd_2211642 : Nat := 252363418149142483156411

theorem tailTrace_2211642 : CollatzResearch.WordTrace tailWord_2211642 prefixEnd_2211642 252363418149142483156411 := by
  unfold tailWord_2211642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20166302663401556806753295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53776807102404151484675453 20166302663401556806753295)
  ·
    refine ⟨30249453995102335210129943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20166302663401556806753295 30249453995102335210129943)
    ·
      refine ⟨45374180992653502815194915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30249453995102335210129943 45374180992653502815194915)
      ·
        refine ⟨68061271488980254222792373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45374180992653502815194915 68061271488980254222792373)
        ·
          refine ⟨6380744202091898833386785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68061271488980254222792373 6380744202091898833386785)
          ·
            refine ⟨4785558151568924125040089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6380744202091898833386785 4785558151568924125040089)
            ·
              refine ⟨3589168613676693093780067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785558151568924125040089 3589168613676693093780067)
              ·
                refine ⟨5383752920515039640670101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589168613676693093780067 5383752920515039640670101)
                ·
                  refine ⟨252363418149142483156411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5383752920515039640670101 252363418149142483156411)
                  ·
                    rfl

theorem cell22_2211642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_2211642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211642 prefixEnd_2211642 := by exact prefixLift 2211642
  have htrace : WordTrace (prefixWord ++ tailWord_2211642) baseStart_2211642 baseEnd_2211642 := by
    simpa [prefixWord, tailWord_2211642, baseEnd_2211642] using wordTrace_append hprefix tailTrace_2211642
  have hstable : (prefixWord ++ tailWord_2211642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211642).length < 2 ^ (prefixWord ++ tailWord_2211642).sum := by decide
  have hdescent : baseEnd_2211642 < baseStart_2211642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211655 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2211655 : Nat := 118140960795 + 2211655 * 2 ^ 59
def prefixEnd_2211655 : Nat := 4983230072969 + 3 ^ 40 * 2211655 * 2
def baseEnd_2211655 : Nat := 757094704613099748894193

theorem tailTrace_2211655 : CollatzResearch.WordTrace tailWord_2211655 prefixEnd_2211655 757094704613099748894193 := by
  unfold tailWord_2211655
  simp only [CollatzResearch.WordTrace]
  refine ⟨80665684802559130447236419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53777123201706086964824279 80665684802559130447236419)
  ·
    refine ⟨120998527203838695670854629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80665684802559130447236419 120998527203838695670854629)
    ·
      refine ⟨22687223850719755438285243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120998527203838695670854629 22687223850719755438285243)
      ·
        refine ⟨34030835776079633157427865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22687223850719755438285243 34030835776079633157427865)
        ·
          refine ⟨25523126832059724868070899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34030835776079633157427865 25523126832059724868070899)
          ·
            refine ⟨38284690248089587302106349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25523126832059724868070899 38284690248089587302106349)
            ·
              refine ⟨14356758843033595238289881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38284690248089587302106349 14356758843033595238289881)
              ·
                refine ⟨10767569132275196428717411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14356758843033595238289881 10767569132275196428717411)
                ·
                  refine ⟨16151353698412794643076117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10767569132275196428717411 16151353698412794643076117)
                  ·
                    refine ⟨757094704613099748894193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16151353698412794643076117 757094704613099748894193)
                    ·
                      rfl

theorem cell22_2211655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2211655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211655 prefixEnd_2211655 := by exact prefixLift 2211655
  have htrace : WordTrace (prefixWord ++ tailWord_2211655) baseStart_2211655 baseEnd_2211655 := by
    simpa [prefixWord, tailWord_2211655, baseEnd_2211655] using wordTrace_append hprefix tailTrace_2211655
  have hstable : (prefixWord ++ tailWord_2211655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211655).length < 2 ^ (prefixWord ++ tailWord_2211655).sum := by decide
  have hdescent : baseEnd_2211655 < baseStart_2211655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211661 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2211661 : Nat := 118140960795 + 2211661 * 2 ^ 59
def prefixEnd_2211661 : Nat := 4983230072969 + 3 ^ 40 * 2211661 * 2
def baseEnd_2211661 : Nat := 757096758535717733244175

theorem tailTrace_2211661 : CollatzResearch.WordTrace tailWord_2211661 prefixEnd_2211661 757096758535717733244175 := by
  unfold tailWord_2211661
  simp only [CollatzResearch.WordTrace]
  refine ⟨80665903640537393471954837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53777269093691595647969891 80665903640537393471954837)
  ·
    refine ⟨3781214233150190318997883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80665903640537393471954837 3781214233150190318997883)
    ·
      refine ⟨5671821349725285478496825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3781214233150190318997883 5671821349725285478496825)
      ·
        refine ⟨4253866012293964108872619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5671821349725285478496825 4253866012293964108872619)
        ·
          refine ⟨6380799018440946163308929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4253866012293964108872619 6380799018440946163308929)
          ·
            refine ⟨4785599263830709622481697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6380799018440946163308929 4785599263830709622481697)
            ·
              refine ⟨3589199447873032216861273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785599263830709622481697 3589199447873032216861273)
              ·
                refine ⟨2691899585904774162645955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589199447873032216861273 2691899585904774162645955)
                ·
                  refine ⟨4037849378857161243968933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691899585904774162645955 4037849378857161243968933)
                  ·
                    refine ⟨757096758535717733244175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4037849378857161243968933 757096758535717733244175)
                    ·
                      rfl

theorem cell22_2211661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2211661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211661 prefixEnd_2211661 := by exact prefixLift 2211661
  have htrace : WordTrace (prefixWord ++ tailWord_2211661) baseStart_2211661 baseEnd_2211661 := by
    simpa [prefixWord, tailWord_2211661, baseEnd_2211661] using wordTrace_append hprefix tailTrace_2211661
  have hstable : (prefixWord ++ tailWord_2211661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211661).length < 2 ^ (prefixWord ++ tailWord_2211661).sum := by decide
  have hdescent : baseEnd_2211661 < baseStart_2211661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211760 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 12]
def baseStart_2211760 : Nat := 118140960795 + 2211760 * 2 ^ 59
def prefixEnd_2211760 : Nat := 4983230072969 + 3 ^ 40 * 2211760 * 2
def baseEnd_2211760 : Nat := 252376882752971491672957

theorem tailTrace_2211760 : CollatzResearch.WordTrace tailWord_2211760 prefixEnd_2211760 252376882752971491672957 := by
  unfold tailWord_2211760
  simp only [CollatzResearch.WordTrace]
  refine ⟨40334757233589366689904367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53779676311452488919872489 40334757233589366689904367)
  ·
    refine ⟨60502135850384050034856551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40334757233589366689904367 60502135850384050034856551)
    ·
      refine ⟨90753203775576075052284827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60502135850384050034856551 90753203775576075052284827)
      ·
        refine ⟨136129805663364112578427241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90753203775576075052284827 136129805663364112578427241)
        ·
          refine ⟨102097354247523084433820431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136129805663364112578427241 102097354247523084433820431)
          ·
            refine ⟨153146031371284626650730647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102097354247523084433820431 153146031371284626650730647)
            ·
              refine ⟨229719047056926939976095971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153146031371284626650730647 229719047056926939976095971)
              ·
                refine ⟨344578570585390409964143957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229719047056926939976095971 344578570585390409964143957)
                ·
                  refine ⟨252376882752971491672957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 344578570585390409964143957 252376882752971491672957)
                  ·
                    rfl

theorem cell22_2211760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_2211760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211760 prefixEnd_2211760 := by exact prefixLift 2211760
  have htrace : WordTrace (prefixWord ++ tailWord_2211760) baseStart_2211760 baseEnd_2211760 := by
    simpa [prefixWord, tailWord_2211760, baseEnd_2211760] using wordTrace_append hprefix tailTrace_2211760
  have hstable : (prefixWord ++ tailWord_2211760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211760).length < 2 ^ (prefixWord ++ tailWord_2211760).sum := by decide
  have hdescent : baseEnd_2211760 < baseStart_2211760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211792 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_2211792 : Nat := 118140960795 + 2211792 * 2 ^ 59
def prefixEnd_2211792 : Nat := 4983230072969 + 3 ^ 40 * 2211792 * 2
def baseEnd_2211792 : Nat := 757141602512877058218773

theorem tailTrace_2211792 : CollatzResearch.WordTrace tailWord_2211792 prefixEnd_2211792 757141602512877058218773 := by
  unfold tailWord_2211792
  simp only [CollatzResearch.WordTrace]
  refine ⟨40335340801531401422486815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53780454402041868563315753 40335340801531401422486815)
  ·
    refine ⟨60503011202297102133730223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40335340801531401422486815 60503011202297102133730223)
    ·
      refine ⟨90754516803445653200595335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60503011202297102133730223 90754516803445653200595335)
      ·
        refine ⟨136131775205168479800893003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90754516803445653200595335 136131775205168479800893003)
        ·
          refine ⟨204197662807752719701339505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136131775205168479800893003 204197662807752719701339505)
          ·
            refine ⟨153148247105814539776004629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204197662807752719701339505 153148247105814539776004629)
            ·
              refine ⟨7178824083085056552000217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153148247105814539776004629 7178824083085056552000217)
              ·
                refine ⟨5384118062313792414000163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7178824083085056552000217 5384118062313792414000163)
                ·
                  refine ⟨8076177093470688621000245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5384118062313792414000163 8076177093470688621000245)
                  ·
                    refine ⟨757141602512877058218773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8076177093470688621000245 757141602512877058218773)
                    ·
                      rfl

theorem cell22_2211792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_2211792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211792 prefixEnd_2211792 := by exact prefixLift 2211792
  have htrace : WordTrace (prefixWord ++ tailWord_2211792) baseStart_2211792 baseEnd_2211792 := by
    simpa [prefixWord, tailWord_2211792, baseEnd_2211792] using wordTrace_append hprefix tailTrace_2211792
  have hstable : (prefixWord ++ tailWord_2211792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211792).length < 2 ^ (prefixWord ++ tailWord_2211792).sum := by decide
  have hdescent : baseEnd_2211792 < baseStart_2211792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211912 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 10]
def baseStart_2211912 : Nat := 118140960795 + 2211912 * 2 ^ 59
def prefixEnd_2211912 : Nat := 4983230072969 + 3 ^ 40 * 2211912 * 2
def baseEnd_2211912 : Nat := 252394226988412248406135

theorem tailTrace_2211912 : CollatzResearch.WordTrace tailWord_2211912 prefixEnd_2211912 252394226988412248406135 := by
  unfold tailWord_2211912
  simp only [CollatzResearch.WordTrace]
  refine ⟨40337529181314031669670995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53783372241752042226227993 40337529181314031669670995)
  ·
    refine ⟨60506293771971047504506493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40337529181314031669670995 60506293771971047504506493)
    ·
      refine ⟨22689860164489142814189935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60506293771971047504506493 22689860164489142814189935)
      ·
        refine ⟨34034790246733714221284903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22689860164489142814189935 34034790246733714221284903)
        ·
          refine ⟨51052185370100571331927355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34034790246733714221284903 51052185370100571331927355)
          ·
            refine ⟨76578278055150856997891033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51052185370100571331927355 76578278055150856997891033)
            ·
              refine ⟨57433708541363142748418275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76578278055150856997891033 57433708541363142748418275)
              ·
                refine ⟨86150562812044714122627413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57433708541363142748418275 86150562812044714122627413)
                ·
                  refine ⟨252394226988412248406135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 86150562812044714122627413 252394226988412248406135)
                  ·
                    rfl

theorem cell22_2211912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_2211912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211912 prefixEnd_2211912 := by exact prefixLift 2211912
  have htrace : WordTrace (prefixWord ++ tailWord_2211912) baseStart_2211912 baseEnd_2211912 := by
    simpa [prefixWord, tailWord_2211912, baseEnd_2211912] using wordTrace_append hprefix tailTrace_2211912
  have hstable : (prefixWord ++ tailWord_2211912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211912).length < 2 ^ (prefixWord ++ tailWord_2211912).sum := by decide
  have hdescent : baseEnd_2211912 < baseStart_2211912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211922 : List Nat := [3, 2, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_2211922 : Nat := 118140960795 + 2211922 * 2 ^ 59
def prefixEnd_2211922 : Nat := 4983230072969 + 3 ^ 40 * 2211922 * 2
def baseEnd_2211922 : Nat := 757186104169600052468375

theorem tailTrace_2211922 : CollatzResearch.WordTrace tailWord_2211922 prefixEnd_2211922 757186104169600052468375 := by
  unfold tailWord_2211922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20168855773147958761801505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53783615395061223364804013 20168855773147958761801505)
  ·
    refine ⟨15126641829860969071351129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20168855773147958761801505 15126641829860969071351129)
    ·
      refine ⟨11344981372395726803513347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15126641829860969071351129 11344981372395726803513347)
      ·
        refine ⟨17017472058593590205270021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11344981372395726803513347 17017472058593590205270021)
        ·
          refine ⟨3190776010986298163488129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17017472058593590205270021 3190776010986298163488129)
          ·
            refine ⟨2393082008239723622616097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3190776010986298163488129 2393082008239723622616097)
            ·
              refine ⟨1794811506179792716962073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2393082008239723622616097 1794811506179792716962073)
              ·
                refine ⟨1346108629634844537721555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794811506179792716962073 1346108629634844537721555)
                ·
                  refine ⟨2019162944452266806582333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346108629634844537721555 2019162944452266806582333)
                  ·
                    refine ⟨757186104169600052468375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2019162944452266806582333 757186104169600052468375)
                    ·
                      rfl

theorem cell22_2211922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_2211922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211922 prefixEnd_2211922 := by exact prefixLift 2211922
  have htrace : WordTrace (prefixWord ++ tailWord_2211922) baseStart_2211922 baseEnd_2211922 := by
    simpa [prefixWord, tailWord_2211922, baseEnd_2211922] using wordTrace_append hprefix tailTrace_2211922
  have hstable : (prefixWord ++ tailWord_2211922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211922).length < 2 ^ (prefixWord ++ tailWord_2211922).sum := by decide
  have hdescent : baseEnd_2211922 < baseStart_2211922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211946 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_2211946 : Nat := 118140960795 + 2211946 * 2 ^ 59
def prefixEnd_2211946 : Nat := 4983230072969 + 3 ^ 40 * 2211946 * 2
def baseEnd_2211946 : Nat := 252398106620023996622767

theorem tailTrace_2211946 : CollatzResearch.WordTrace tailWord_2211946 prefixEnd_2211946 252398106620023996622767 := by
  unfold tailWord_2211946
  simp only [CollatzResearch.WordTrace]
  refine ⟨20169074611126221786519923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53784198963003258097386461 20169074611126221786519923)
  ·
    refine ⟨30253611916689332679779885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20169074611126221786519923 30253611916689332679779885)
    ·
      refine ⟨11345104468758499754917457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30253611916689332679779885 11345104468758499754917457)
      ·
        refine ⟨8508828351568874816188093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11345104468758499754917457 8508828351568874816188093)
        ·
          refine ⟨3190810631838328056070535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8508828351568874816188093 3190810631838328056070535)
          ·
            refine ⟨4786215947757492084105803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190810631838328056070535 4786215947757492084105803)
            ·
              refine ⟨7179323921636238126158705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786215947757492084105803 7179323921636238126158705)
              ·
                refine ⟨5384492941227178594619029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7179323921636238126158705 5384492941227178594619029)
                ·
                  refine ⟨252398106620023996622767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5384492941227178594619029 252398106620023996622767)
                  ·
                    rfl

theorem cell22_2211946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_2211946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211946 prefixEnd_2211946 := by exact prefixLift 2211946
  have htrace : WordTrace (prefixWord ++ tailWord_2211946) baseStart_2211946 baseEnd_2211946 := by
    simpa [prefixWord, tailWord_2211946, baseEnd_2211946] using wordTrace_append hprefix tailTrace_2211946
  have hstable : (prefixWord ++ tailWord_2211946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211946).length < 2 ^ (prefixWord ++ tailWord_2211946).sum := by decide
  have hdescent : baseEnd_2211946 < baseStart_2211946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211959 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 1, 6]
def baseStart_2211959 : Nat := 118140960795 + 2211959 * 2 ^ 59
def prefixEnd_2211959 : Nat := 4983230072969 + 3 ^ 40 * 2211959 * 2
def baseEnd_2211959 : Nat := 757198770025744289293261

theorem tailTrace_2211959 : CollatzResearch.WordTrace tailWord_2211959 prefixEnd_2211959 757198770025744289293261 := by
  unfold tailWord_2211959
  simp only [CollatzResearch.WordTrace]
  refine ⟨80676772593457790366302931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53784515062305193577535287 80676772593457790366302931)
  ·
    refine ⟨121015158890186685549454397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80676772593457790366302931 121015158890186685549454397)
    ·
      refine ⟨45380684583820007081045399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121015158890186685549454397 45380684583820007081045399)
      ·
        refine ⟨68071026875730010621568099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45380684583820007081045399 68071026875730010621568099)
        ·
          refine ⟨102106540313595015932352149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68071026875730010621568099 102106540313595015932352149)
          ·
            refine ⟨4786244077199766371829007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102106540313595015932352149 4786244077199766371829007)
            ·
              refine ⟨7179366115799649557743511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786244077199766371829007 7179366115799649557743511)
              ·
                refine ⟨10769049173699474336615267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7179366115799649557743511 10769049173699474336615267)
                ·
                  refine ⟨16153573760549211504922901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10769049173699474336615267 16153573760549211504922901)
                  ·
                    refine ⟨757198770025744289293261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16153573760549211504922901 757198770025744289293261)
                    ·
                      rfl

theorem cell22_2211959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_2211959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211959 prefixEnd_2211959 := by exact prefixLift 2211959
  have htrace : WordTrace (prefixWord ++ tailWord_2211959) baseStart_2211959 baseEnd_2211959 := by
    simpa [prefixWord, tailWord_2211959, baseEnd_2211959] using wordTrace_append hprefix tailTrace_2211959
  have hstable : (prefixWord ++ tailWord_2211959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211959).length < 2 ^ (prefixWord ++ tailWord_2211959).sum := by decide
  have hdescent : baseEnd_2211959 < baseStart_2211959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211978 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_2211978 : Nat := 118140960795 + 2211978 * 2 ^ 59
def prefixEnd_2211978 : Nat := 4983230072969 + 3 ^ 40 * 2211978 * 2
def baseEnd_2211978 : Nat := 757205274114034573068203

theorem tailTrace_2211978 : CollatzResearch.WordTrace tailWord_2211978 prefixEnd_2211978 757205274114034573068203 := by
  unfold tailWord_2211978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20169366395097239152811147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53784977053592637740829725 20169366395097239152811147)
  ·
    refine ⟨30254049592645858729216721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20169366395097239152811147 30254049592645858729216721)
    ·
      refine ⟨22690537194484394046912541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30254049592645858729216721 22690537194484394046912541)
      ·
        refine ⟨8508951447931647767592203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22690537194484394046912541 8508951447931647767592203)
        ·
          refine ⟨12763427171897471651388305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8508951447931647767592203 12763427171897471651388305)
          ·
            refine ⟨9572570378923103738541229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12763427171897471651388305 9572570378923103738541229)
            ·
              refine ⟨3589713892096163901952961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9572570378923103738541229 3589713892096163901952961)
              ·
                refine ⟨2692285419072122926464721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589713892096163901952961 2692285419072122926464721)
                ·
                  refine ⟨2019214064304092194848541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2692285419072122926464721 2019214064304092194848541)
                  ·
                    refine ⟨757205274114034573068203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2019214064304092194848541 757205274114034573068203)
                    ·
                      rfl

theorem cell22_2211978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_2211978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2211978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2211978 prefixEnd_2211978 := by exact prefixLift 2211978
  have htrace : WordTrace (prefixWord ++ tailWord_2211978) baseStart_2211978 baseEnd_2211978 := by
    simpa [prefixWord, tailWord_2211978, baseEnd_2211978] using wordTrace_append hprefix tailTrace_2211978
  have hstable : (prefixWord ++ tailWord_2211978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211978).length < 2 ^ (prefixWord ++ tailWord_2211978).sum := by decide
  have hdescent : baseEnd_2211978 < baseStart_2211978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212014 : List Nat := [4, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_2212014 : Nat := 118140960795 + 2212014 * 2 ^ 59
def prefixEnd_2212014 : Nat := 4983230072969 + 3 ^ 40 * 2212014 * 2
def baseEnd_2212014 : Nat := 252405865883247493056031

theorem tailTrace_2212014 : CollatzResearch.WordTrace tailWord_2212014 prefixEnd_2212014 252405865883247493056031 := by
  unfold tailWord_2212014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10084847326032316844944387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53785852405505689839703397 10084847326032316844944387)
  ·
    refine ⟨15127270989048475267416581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10084847326032316844944387 15127270989048475267416581)
    ·
      refine ⟨2836363310446589112640609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15127270989048475267416581 2836363310446589112640609)
      ·
        refine ⟨2127272482834941834480457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2836363310446589112640609 2127272482834941834480457)
        ·
          refine ⟨1595454362126206375860343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2127272482834941834480457 1595454362126206375860343)
          ·
            refine ⟨2393181543189309563790515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595454362126206375860343 2393181543189309563790515)
            ·
              refine ⟨3589772314783964345685773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393181543189309563790515 3589772314783964345685773)
              ·
                refine ⟨1346164618043986629632165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3589772314783964345685773 1346164618043986629632165)
                ·
                  refine ⟨252405865883247493056031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1346164618043986629632165 252405865883247493056031)
                  ·
                    rfl

theorem cell22_2212014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_2212014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212014 prefixEnd_2212014 := by exact prefixLift 2212014
  have htrace : WordTrace (prefixWord ++ tailWord_2212014) baseStart_2212014 baseEnd_2212014 := by
    simpa [prefixWord, tailWord_2212014, baseEnd_2212014] using wordTrace_append hprefix tailTrace_2212014
  have hstable : (prefixWord ++ tailWord_2212014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212014).length < 2 ^ (prefixWord ++ tailWord_2212014).sum := by decide
  have hdescent : baseEnd_2212014 < baseStart_2212014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212036 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 7]
def baseStart_2212036 : Nat := 118140960795 + 2212036 * 2 ^ 59
def prefixEnd_2212036 : Nat := 4983230072969 + 3 ^ 40 * 2212036 * 2
def baseEnd_2212036 : Nat := 252408376233113918372675

theorem tailTrace_2212036 : CollatzResearch.WordTrace tailWord_2212036 prefixEnd_2212036 252408376233113918372675 := by
  unfold tailWord_2212036
  simp only [CollatzResearch.WordTrace]
  refine ⟨40339790507089416258427981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53786387342785888344570641 40339790507089416258427981)
  ·
    refine ⟨15127421440158531096910493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40339790507089416258427981 15127421440158531096910493)
    ·
      refine ⟨5672783040059449161341435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15127421440158531096910493 5672783040059449161341435)
      ·
        refine ⟨8509174560089173742012153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5672783040059449161341435 8509174560089173742012153)
        ·
          refine ⟨6381880920066880306509115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8509174560089173742012153 6381880920066880306509115)
          ·
            refine ⟨9572821380100320459763673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6381880920066880306509115 9572821380100320459763673)
            ·
              refine ⟨7179616035075240344822755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9572821380100320459763673 7179616035075240344822755)
              ·
                refine ⟨10769424052612860517234133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7179616035075240344822755 10769424052612860517234133)
                ·
                  refine ⟨252408376233113918372675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10769424052612860517234133 252408376233113918372675)
                  ·
                    rfl

theorem cell22_2212036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_2212036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212036 prefixEnd_2212036 := by exact prefixLift 2212036
  have htrace : WordTrace (prefixWord ++ tailWord_2212036) baseStart_2212036 baseEnd_2212036 := by
    simpa [prefixWord, tailWord_2212036, baseEnd_2212036] using wordTrace_append hprefix tailTrace_2212036
  have hstable : (prefixWord ++ tailWord_2212036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212036).length < 2 ^ (prefixWord ++ tailWord_2212036).sum := by decide
  have hdescent : baseEnd_2212036 < baseStart_2212036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212053 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 5]
def baseStart_2212053 : Nat := 118140960795 + 2212053 * 2 ^ 59
def prefixEnd_2212053 : Nat := 4983230072969 + 3 ^ 40 * 2212053 * 2
def baseEnd_2212053 : Nat := 252410316048919792480991

theorem tailTrace_2212053 : CollatzResearch.WordTrace tailWord_2212053 prefixEnd_2212053 252410316048919792480991 := by
  unfold tailWord_2212053
  simp only [CollatzResearch.WordTrace]
  refine ⟨80680201055117244420224813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53786800703411496280149875 80680201055117244420224813)
  ·
    refine ⟨30255075395668966657584305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80680201055117244420224813 30255075395668966657584305)
    ·
      refine ⟨22691306546751724993188229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30255075395668966657584305 22691306546751724993188229)
      ·
        refine ⟨4254619977515948436222793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22691306546751724993188229 4254619977515948436222793)
        ·
          refine ⟨3190964983136961327167095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4254619977515948436222793 3190964983136961327167095)
          ·
            refine ⟨4786447474705441990750643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190964983136961327167095 4786447474705441990750643)
            ·
              refine ⟨7179671212058162986125965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786447474705441990750643 7179671212058162986125965)
              ·
                refine ⟨2692376704521811119797237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7179671212058162986125965 2692376704521811119797237)
                ·
                  refine ⟨252410316048919792480991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2692376704521811119797237 252410316048919792480991)
                  ·
                    rfl

theorem cell22_2212053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_2212053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212053 prefixEnd_2212053 := by exact prefixLift 2212053
  have htrace : WordTrace (prefixWord ++ tailWord_2212053) baseStart_2212053 baseEnd_2212053 := by
    simpa [prefixWord, tailWord_2212053, baseEnd_2212053] using wordTrace_append hprefix tailTrace_2212053
  have hstable : (prefixWord ++ tailWord_2212053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212053).length < 2 ^ (prefixWord ++ tailWord_2212053).sum := by decide
  have hdescent : baseEnd_2212053 < baseStart_2212053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212064 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 8]
def baseStart_2212064 : Nat := 118140960795 + 2212064 * 2 ^ 59
def prefixEnd_2212064 : Nat := 4983230072969 + 3 ^ 40 * 2212064 * 2
def baseEnd_2212064 : Nat := 252411571223853005139313

theorem tailTrace_2212064 : CollatzResearch.WordTrace tailWord_2212064 prefixEnd_2212064 252411571223853005139313 := by
  unfold tailWord_2212064
  simp only [CollatzResearch.WordTrace]
  refine ⟨40340301129038696649437623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53787068172051595532583497 40340301129038696649437623)
  ·
    refine ⟨60510451693558044974156435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40340301129038696649437623 60510451693558044974156435)
    ·
      refine ⟨90765677540337067461234653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60510451693558044974156435 90765677540337067461234653)
      ·
        refine ⟨34037129077626400297962995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90765677540337067461234653 34037129077626400297962995)
        ·
          refine ⟨51055693616439600446944493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34037129077626400297962995 51055693616439600446944493)
          ·
            refine ⟨19145885106164850167604185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51055693616439600446944493 19145885106164850167604185)
            ·
              refine ⟨14359413829623637625703139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19145885106164850167604185 14359413829623637625703139)
              ·
                refine ⟨21539120744435456438554709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14359413829623637625703139 21539120744435456438554709)
                ·
                  refine ⟨252411571223853005139313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21539120744435456438554709 252411571223853005139313)
                  ·
                    rfl

theorem cell22_2212064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_2212064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212064 prefixEnd_2212064 := by exact prefixLift 2212064
  have htrace : WordTrace (prefixWord ++ tailWord_2212064) baseStart_2212064 baseEnd_2212064 := by
    simpa [prefixWord, tailWord_2212064, baseEnd_2212064] using wordTrace_append hprefix tailTrace_2212064
  have hstable : (prefixWord ++ tailWord_2212064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212064).length < 2 ^ (prefixWord ++ tailWord_2212064).sum := by decide
  have hdescent : baseEnd_2212064 < baseStart_2212064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212083 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 1, 4]
def baseStart_2212083 : Nat := 118140960795 + 2212083 * 2 ^ 59
def prefixEnd_2212083 : Nat := 4983230072969 + 3 ^ 40 * 2212083 * 2
def baseEnd_2212083 : Nat := 757241217759849299192881

theorem tailTrace_2212083 : CollatzResearch.WordTrace tailWord_2212083 prefixEnd_2212083 757241217759849299192881 := by
  unfold tailWord_2212083
  simp only [CollatzResearch.WordTrace]
  refine ⟨80681295245008559543816903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53787530163339039695877935 80681295245008559543816903)
  ·
    refine ⟨121021942867512839315725355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80681295245008559543816903 121021942867512839315725355)
    ·
      refine ⟨181532914301269258973588033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121021942867512839315725355 181532914301269258973588033)
      ·
        refine ⟨136149685725951944230191025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181532914301269258973588033 136149685725951944230191025)
        ·
          refine ⟨102112264294463958172643269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136149685725951944230191025 102112264294463958172643269)
          ·
            refine ⟨19146049555211992157370613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102112264294463958172643269 19146049555211992157370613)
            ·
              refine ⟨1794942145801124264753495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19146049555211992157370613 1794942145801124264753495)
              ·
                refine ⟨2692413218701686397130243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794942145801124264753495 2692413218701686397130243)
                ·
                  refine ⟨4038619828052529595695365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692413218701686397130243 4038619828052529595695365)
                  ·
                    refine ⟨757241217759849299192881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4038619828052529595695365 757241217759849299192881)
                    ·
                      rfl

theorem cell22_2212083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 4].length) (baseStart_2212083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212083 prefixEnd_2212083 := by exact prefixLift 2212083
  have htrace : WordTrace (prefixWord ++ tailWord_2212083) baseStart_2212083 baseEnd_2212083 := by
    simpa [prefixWord, tailWord_2212083, baseEnd_2212083] using wordTrace_append hprefix tailTrace_2212083
  have hstable : (prefixWord ++ tailWord_2212083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212083).length < 2 ^ (prefixWord ++ tailWord_2212083).sum := by decide
  have hdescent : baseEnd_2212083 < baseStart_2212083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212096 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 4, 3]
def baseStart_2212096 : Nat := 118140960795 + 2212096 * 2 ^ 59
def prefixEnd_2212096 : Nat := 4983230072969 + 3 ^ 40 * 2212096 * 2
def baseEnd_2212096 : Nat := 757245667925521598617841

theorem tailTrace_2212096 : CollatzResearch.WordTrace tailWord_2212096 prefixEnd_2212096 757245667925521598617841 := by
  unfold tailWord_2212096
  simp only [CollatzResearch.WordTrace]
  refine ⟨40340884696980731382020071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53787846262640975176026761 40340884696980731382020071)
  ·
    refine ⟨60511327045471097073030107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40340884696980731382020071 60511327045471097073030107)
    ·
      refine ⟨90766990568206645609545161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60511327045471097073030107 90766990568206645609545161)
      ·
        refine ⟨68075242926154984207158871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90766990568206645609545161 68075242926154984207158871)
        ·
          refine ⟨102112864389232476310738307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68075242926154984207158871 102112864389232476310738307)
          ·
            refine ⟨153169296583848714466107461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102112864389232476310738307 153169296583848714466107461)
            ·
              refine ⟨28719243109471633962395149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153169296583848714466107461 28719243109471633962395149)
              ·
                refine ⟨10769716166051862735898181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28719243109471633962395149 10769716166051862735898181)
                ·
                  refine ⟨2019321781134724262980909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10769716166051862735898181 2019321781134724262980909)
                  ·
                    refine ⟨757245667925521598617841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2019321781134724262980909 757245667925521598617841)
                    ·
                      rfl

theorem cell22_2212096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_2212096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212096 prefixEnd_2212096 := by exact prefixLift 2212096
  have htrace : WordTrace (prefixWord ++ tailWord_2212096) baseStart_2212096 baseEnd_2212096 := by
    simpa [prefixWord, tailWord_2212096, baseEnd_2212096] using wordTrace_append hprefix tailTrace_2212096
  have hstable : (prefixWord ++ tailWord_2212096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212096).length < 2 ^ (prefixWord ++ tailWord_2212096).sum := by decide
  have hdescent : baseEnd_2212096 < baseStart_2212096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212113 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 2, 3]
def baseStart_2212113 : Nat := 118140960795 + 2212113 * 2 ^ 59
def prefixEnd_2212113 : Nat := 4983230072969 + 3 ^ 40 * 2212113 * 2
def baseEnd_2212113 : Nat := 757251487372939220942789

theorem tailTrace_2212113 : CollatzResearch.WordTrace tailWord_2212113 prefixEnd_2212113 757251487372939220942789 := by
  unfold tailWord_2212113
  simp only [CollatzResearch.WordTrace]
  refine ⟨80682389434899874667408993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53788259623266583111605995 80682389434899874667408993)
  ·
    refine ⟨60511792076174906000556745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80682389434899874667408993 60511792076174906000556745)
    ·
      refine ⟨45383844057131179500417559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60511792076174906000556745 45383844057131179500417559)
      ·
        refine ⟨68075766085696769250626339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45383844057131179500417559 68075766085696769250626339)
        ·
          refine ⟨102113649128545153875939509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68075766085696769250626339 102113649128545153875939509)
          ·
            refine ⟨9573154605801108175869329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102113649128545153875939509 9573154605801108175869329)
            ·
              refine ⟨7179865954350831131901997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9573154605801108175869329 7179865954350831131901997)
              ·
                refine ⟨2692449732881561674463249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7179865954350831131901997 2692449732881561674463249)
                ·
                  refine ⟨2019337299661171255847437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2692449732881561674463249 2019337299661171255847437)
                  ·
                    refine ⟨757251487372939220942789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2019337299661171255847437 757251487372939220942789)
                    ·
                      rfl

theorem cell22_2212113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_2212113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212113 prefixEnd_2212113 := by exact prefixLift 2212113
  have htrace : WordTrace (prefixWord ++ tailWord_2212113) baseStart_2212113 baseEnd_2212113 := by
    simpa [prefixWord, tailWord_2212113, baseEnd_2212113] using wordTrace_append hprefix tailTrace_2212113
  have hstable : (prefixWord ++ tailWord_2212113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212113).length < 2 ^ (prefixWord ++ tailWord_2212113).sum := by decide
  have hdescent : baseEnd_2212113 < baseStart_2212113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212128 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_2212128 : Nat := 118140960795 + 2212128 * 2 ^ 59
def prefixEnd_2212128 : Nat := 4983230072969 + 3 ^ 40 * 2212128 * 2
def baseEnd_2212128 : Nat := 757256622179484181817743

theorem tailTrace_2212128 : CollatzResearch.WordTrace tailWord_2212128 prefixEnd_2212128 757256622179484181817743 := by
  unfold tailWord_2212128
  simp only [CollatzResearch.WordTrace]
  refine ⟨40341468264922766114602519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53788624353230354819470025 40341468264922766114602519)
  ·
    refine ⟨60512202397384149171903779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40341468264922766114602519 60512202397384149171903779)
    ·
      refine ⟨90768303596076223757855669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60512202397384149171903779 90768303596076223757855669)
      ·
        refine ⟨8509528462132145977298969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90768303596076223757855669 8509528462132145977298969)
        ·
          refine ⟨6382146346599109482974227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8509528462132145977298969 6382146346599109482974227)
          ·
            refine ⟨9573219519898664224461341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6382146346599109482974227 9573219519898664224461341)
            ·
              refine ⟨3589957319961999084173003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9573219519898664224461341 3589957319961999084173003)
              ·
                refine ⟨5384935979942998626259505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589957319961999084173003 5384935979942998626259505)
                ·
                  refine ⟨4038701984957248969694629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5384935979942998626259505 4038701984957248969694629)
                  ·
                    refine ⟨757256622179484181817743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4038701984957248969694629 757256622179484181817743)
                    ·
                      rfl

theorem cell22_2212128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_2212128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212128 prefixEnd_2212128 := by exact prefixLift 2212128
  have htrace : WordTrace (prefixWord ++ tailWord_2212128) baseStart_2212128 baseEnd_2212128 := by
    simpa [prefixWord, tailWord_2212128, baseEnd_2212128] using wordTrace_append hprefix tailTrace_2212128
  have hstable : (prefixWord ++ tailWord_2212128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212128).length < 2 ^ (prefixWord ++ tailWord_2212128).sum := by decide
  have hdescent : baseEnd_2212128 < baseStart_2212128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212164 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2212164 : Nat := 118140960795 + 2212164 * 2 ^ 59
def prefixEnd_2212164 : Nat := 4983230072969 + 3 ^ 40 * 2212164 * 2
def baseEnd_2212164 : Nat := 757268945715192087917633

theorem tailTrace_2212164 : CollatzResearch.WordTrace tailWord_2212164 prefixEnd_2212164 757268945715192087917633 := by
  unfold tailWord_2212164
  simp only [CollatzResearch.WordTrace]
  refine ⟨40342124778857555188757773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53789499705143406918343697 40342124778857555188757773)
  ·
    refine ⟨15128296792071583195784165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40342124778857555188757773 15128296792071583195784165)
    ·
      refine ⟨2836555648513421849209531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15128296792071583195784165 2836555648513421849209531)
      ·
        refine ⟨4254833472770132773814297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836555648513421849209531 4254833472770132773814297)
        ·
          refine ⟨3191125104577599580360723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4254833472770132773814297 3191125104577599580360723)
          ·
            refine ⟨4786687656866399370541085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191125104577599580360723 4786687656866399370541085)
            ·
              refine ⟨1795007871324899763952907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4786687656866399370541085 1795007871324899763952907)
              ·
                refine ⟨2692511806987349645929361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795007871324899763952907 2692511806987349645929361)
                ·
                  refine ⟨2019383855240512234447021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2692511806987349645929361 2019383855240512234447021)
                  ·
                    refine ⟨757268945715192087917633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2019383855240512234447021 757268945715192087917633)
                    ·
                      rfl

theorem cell22_2212164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2212164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212164 prefixEnd_2212164 := by exact prefixLift 2212164
  have htrace : WordTrace (prefixWord ++ tailWord_2212164) baseStart_2212164 baseEnd_2212164 := by
    simpa [prefixWord, tailWord_2212164, baseEnd_2212164] using wordTrace_append hprefix tailTrace_2212164
  have hstable : (prefixWord ++ tailWord_2212164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212164).length < 2 ^ (prefixWord ++ tailWord_2212164).sum := by decide
  have hdescent : baseEnd_2212164 < baseStart_2212164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212235 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 1, 4]
def baseStart_2212235 : Nat := 118140960795 + 2212235 * 2 ^ 59
def prefixEnd_2212235 : Nat := 4983230072969 + 3 ^ 40 * 2212235 * 2
def baseEnd_2212235 : Nat := 757293250466171569392415

theorem tailTrace_2212235 : CollatzResearch.WordTrace tailWord_2212235 prefixEnd_2212235 757293250466171569392415 := by
  unfold tailWord_2212235
  simp only [CollatzResearch.WordTrace]
  refine ⟨80686839140457889503350159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53791226093638593002233439 80686839140457889503350159)
  ·
    refine ⟨121030258710686834255025239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80686839140457889503350159 121030258710686834255025239)
    ·
      refine ⟨181545388066030251382537859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121030258710686834255025239 181545388066030251382537859)
      ·
        refine ⟨272318082099045377073806789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181545388066030251382537859 272318082099045377073806789)
        ·
          refine ⟨51059640393571008201338773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272318082099045377073806789 51059640393571008201338773)
          ·
            refine ⟨2393420643448641009437755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51059640393571008201338773 2393420643448641009437755)
            ·
              refine ⟨3590130965172961514156633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393420643448641009437755 3590130965172961514156633)
              ·
                refine ⟨2692598223879721135617475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3590130965172961514156633 2692598223879721135617475)
                ·
                  refine ⟨4038897335819581703426213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692598223879721135617475 4038897335819581703426213)
                  ·
                    refine ⟨757293250466171569392415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4038897335819581703426213 757293250466171569392415)
                    ·
                      rfl

theorem cell22_2212235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 4].length) (baseStart_2212235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212235 prefixEnd_2212235 := by exact prefixLift 2212235
  have htrace : WordTrace (prefixWord ++ tailWord_2212235) baseStart_2212235 baseEnd_2212235 := by
    simpa [prefixWord, tailWord_2212235, baseEnd_2212235] using wordTrace_append hprefix tailTrace_2212235
  have hstable : (prefixWord ++ tailWord_2212235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212235).length < 2 ^ (prefixWord ++ tailWord_2212235).sum := by decide
  have hdescent : baseEnd_2212235 < baseStart_2212235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212248 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_2212248 : Nat := 118140960795 + 2212248 * 2 ^ 59
def prefixEnd_2212248 : Nat := 4983230072969 + 3 ^ 40 * 2212248 * 2
def baseEnd_2212248 : Nat := 757297700631843868817375

theorem tailTrace_2212248 : CollatzResearch.WordTrace tailWord_2212248 prefixEnd_2212248 757297700631843868817375 := by
  unfold tailWord_2212248
  simp only [CollatzResearch.WordTrace]
  refine ⟨40343656644705396361786699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53791542192940528482382265 40343656644705396361786699)
  ·
    refine ⟨60515484967058094542680049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40343656644705396361786699 60515484967058094542680049)
    ·
      refine ⟨45386613725293570907010037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60515484967058094542680049 45386613725293570907010037)
      ·
        refine ⟨4254995036746272272532191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45386613725293570907010037 4254995036746272272532191)
        ·
          refine ⟨6382492555119408408798287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4254995036746272272532191 6382492555119408408798287)
          ·
            refine ⟨9573738832679112613197431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6382492555119408408798287 9573738832679112613197431)
            ·
              refine ⟨14360608249018668919796147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9573738832679112613197431 14360608249018668919796147)
              ·
                refine ⟨21540912373528003379694221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14360608249018668919796147 21540912373528003379694221)
                ·
                  refine ⟨8077842140073001267385333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21540912373528003379694221 8077842140073001267385333)
                  ·
                    refine ⟨757297700631843868817375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8077842140073001267385333 757297700631843868817375)
                    ·
                      rfl

theorem cell22_2212248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_2212248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212248 prefixEnd_2212248 := by exact prefixLift 2212248
  have htrace : WordTrace (prefixWord ++ tailWord_2212248) baseStart_2212248 baseEnd_2212248 := by
    simpa [prefixWord, tailWord_2212248, baseEnd_2212248] using wordTrace_append hprefix tailTrace_2212248
  have hstable : (prefixWord ++ tailWord_2212248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212248).length < 2 ^ (prefixWord ++ tailWord_2212248).sum := by decide
  have hdescent : baseEnd_2212248 < baseStart_2212248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212291 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 4, 6]
def baseStart_2212291 : Nat := 118140960795 + 2212291 * 2 ^ 59
def prefixEnd_2212291 : Nat := 4983230072969 + 3 ^ 40 * 2212291 * 2
def baseEnd_2212291 : Nat := 757312420410606089992243

theorem tailTrace_2212291 : CollatzResearch.WordTrace tailWord_2212291 prefixEnd_2212291 757312420410606089992243 := by
  unfold tailWord_2212291
  simp only [CollatzResearch.WordTrace]
  refine ⟨80688881628255011067388727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53792587752170007378259151 80688881628255011067388727)
  ·
    refine ⟨121033322442382516601083091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80688881628255011067388727 121033322442382516601083091)
    ·
      refine ⟨181549983663573774901624637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121033322442382516601083091 181549983663573774901624637)
      ·
        refine ⟨68081243873840165588109239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181549983663573774901624637 68081243873840165588109239)
        ·
          refine ⟨102121865810760248382163859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68081243873840165588109239 102121865810760248382163859)
          ·
            refine ⟨153182798716140372573245789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102121865810760248382163859 153182798716140372573245789)
            ·
              refine ⟨57443549518552639714967171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153182798716140372573245789 57443549518552639714967171)
              ·
                refine ⟨86165324277828959572450757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57443549518552639714967171 86165324277828959572450757)
                ·
                  refine ⟨16155998302092929919834517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86165324277828959572450757 16155998302092929919834517)
                  ·
                    refine ⟨757312420410606089992243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16155998302092929919834517 757312420410606089992243)
                    ·
                      rfl

theorem cell22_2212291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_2212291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212291 prefixEnd_2212291 := by exact prefixLift 2212291
  have htrace : WordTrace (prefixWord ++ tailWord_2212291) baseStart_2212291 baseEnd_2212291 := by
    simpa [prefixWord, tailWord_2212291, baseEnd_2212291] using wordTrace_append hprefix tailTrace_2212291
  have hstable : (prefixWord ++ tailWord_2212291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212291).length < 2 ^ (prefixWord ++ tailWord_2212291).sum := by decide
  have hdescent : baseEnd_2212291 < baseStart_2212291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212327 : List Nat := [1, 1, 5, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2212327 : Nat := 118140960795 + 2212327 * 2 ^ 59
def prefixEnd_2212327 : Nat := 4983230072969 + 3 ^ 40 * 2212327 * 2
def baseEnd_2212327 : Nat := 757324743946313996092133

theorem tailTrace_2212327 : CollatzResearch.WordTrace tailWord_2212327 prefixEnd_2212327 757324743946313996092133 := by
  unfold tailWord_2212327
  simp only [CollatzResearch.WordTrace]
  refine ⟨80690194656124589215699235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53793463104083059477132823 80690194656124589215699235)
  ·
    refine ⟨121035291984186883823548853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80690194656124589215699235 121035291984186883823548853)
    ·
      refine ⟨11347058623517520358457705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121035291984186883823548853 11347058623517520358457705)
      ·
        refine ⟨8510293967638140268843279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11347058623517520358457705 8510293967638140268843279)
        ·
          refine ⟨12765440951457210403264919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8510293967638140268843279 12765440951457210403264919)
          ·
            refine ⟨19148161427185815604897379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12765440951457210403264919 19148161427185815604897379)
            ·
              refine ⟨28722242140778723407346069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19148161427185815604897379 28722242140778723407346069)
              ·
                refine ⟨1346355100349002659719347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28722242140778723407346069 1346355100349002659719347)
                ·
                  refine ⟨2019532650523503989579021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346355100349002659719347 2019532650523503989579021)
                  ·
                    refine ⟨757324743946313996092133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2019532650523503989579021 757324743946313996092133)
                    ·
                      rfl

theorem cell22_2212327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2212327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212327 prefixEnd_2212327 := by exact prefixLift 2212327
  have htrace : WordTrace (prefixWord ++ tailWord_2212327) baseStart_2212327 baseEnd_2212327 := by
    simpa [prefixWord, tailWord_2212327, baseEnd_2212327] using wordTrace_append hprefix tailTrace_2212327
  have hstable : (prefixWord ++ tailWord_2212327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212327).length < 2 ^ (prefixWord ++ tailWord_2212327).sum := by decide
  have hdescent : baseEnd_2212327 < baseStart_2212327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212391 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 5]
def baseStart_2212391 : Nat := 118140960795 + 2212391 * 2 ^ 59
def prefixEnd_2212391 : Nat := 4983230072969 + 3 ^ 40 * 2212391 * 2
def baseEnd_2212391 : Nat := 252448884151413054163979

theorem tailTrace_2212391 : CollatzResearch.WordTrace tailWord_2212391 prefixEnd_2212391 252448884151413054163979 := by
  unfold tailWord_2212391
  simp only [CollatzResearch.WordTrace]
  refine ⟨80692528927892728146029027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53795019285261818764019351 80692528927892728146029027)
  ·
    refine ⟨121038793391839092219043541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80692528927892728146029027 121038793391839092219043541)
    ·
      refine ⟨2836846720121228723883833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 121038793391839092219043541 2836846720121228723883833)
      ·
        refine ⟨2127635040090921542912875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2836846720121228723883833 2127635040090921542912875)
        ·
          refine ⟨3191452560136382314369313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127635040090921542912875 3191452560136382314369313)
          ·
            refine ⟨2393589420102286735776985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3191452560136382314369313 2393589420102286735776985)
            ·
              refine ⟨1795192065076715051832739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2393589420102286735776985 1795192065076715051832739)
              ·
                refine ⟨2692788097615072577749109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795192065076715051832739 2692788097615072577749109)
                ·
                  refine ⟨252448884151413054163979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2692788097615072577749109 252448884151413054163979)
                  ·
                    rfl

theorem cell22_2212391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 5].length) (baseStart_2212391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212391 prefixEnd_2212391 := by exact prefixLift 2212391
  have htrace : WordTrace (prefixWord ++ tailWord_2212391) baseStart_2212391 baseEnd_2212391 := by
    simpa [prefixWord, tailWord_2212391, baseEnd_2212391] using wordTrace_append hprefix tailTrace_2212391
  have hstable : (prefixWord ++ tailWord_2212391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212391).length < 2 ^ (prefixWord ++ tailWord_2212391).sum := by decide
  have hdescent : baseEnd_2212391 < baseStart_2212391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212404 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2212404 : Nat := 118140960795 + 2212404 * 2 ^ 59
def prefixEnd_2212404 : Nat := 4983230072969 + 3 ^ 40 * 2212404 * 2
def baseEnd_2212404 : Nat := 757351102619911461916897

theorem tailTrace_2212404 : CollatzResearch.WordTrace tailWord_2212404 prefixEnd_2212404 757351102619911461916897 := by
  unfold tailWord_2212404
  simp only [CollatzResearch.WordTrace]
  refine ⟨40346501538422815683126133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53795335384563754244168177 40346501538422815683126133)
  ·
    refine ⟨3782484519227138970293075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40346501538422815683126133 3782484519227138970293075)
    ·
      refine ⟨5673726778840708455439613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3782484519227138970293075 5673726778840708455439613)
      ·
        refine ⟨2127647542065265670789855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5673726778840708455439613 2127647542065265670789855)
        ·
          refine ⟨3191471313097898506184783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127647542065265670789855 3191471313097898506184783)
          ·
            refine ⟨4787206969646847759277175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191471313097898506184783 4787206969646847759277175)
            ·
              refine ⟨7180810454470271638915763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4787206969646847759277175 7180810454470271638915763)
              ·
                refine ⟨10771215681705407458373645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7180810454470271638915763 10771215681705407458373645)
                ·
                  refine ⟨4039205880639527796890117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10771215681705407458373645 4039205880639527796890117)
                  ·
                    refine ⟨757351102619911461916897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4039205880639527796890117 757351102619911461916897)
                    ·
                      rfl

theorem cell22_2212404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2212404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212404 prefixEnd_2212404 := by exact prefixLift 2212404
  have htrace : WordTrace (prefixWord ++ tailWord_2212404) baseStart_2212404 baseEnd_2212404 := by
    simpa [prefixWord, tailWord_2212404, baseEnd_2212404] using wordTrace_append hprefix tailTrace_2212404
  have hstable : (prefixWord ++ tailWord_2212404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212404).length < 2 ^ (prefixWord ++ tailWord_2212404).sum := by decide
  have hdescent : baseEnd_2212404 < baseStart_2212404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212415 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 2, 4]
def baseStart_2212415 : Nat := 118140960795 + 2212415 * 2 ^ 59
def prefixEnd_2212415 : Nat := 4983230072969 + 3 ^ 40 * 2212415 * 2
def baseEnd_2212415 : Nat := 757354868144711099891863

theorem tailTrace_2212415 : CollatzResearch.WordTrace tailWord_2212415 prefixEnd_2212415 757354868144711099891863 := by
  unfold tailWord_2212415
  simp only [CollatzResearch.WordTrace]
  refine ⟨80693404279805780244902699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53795602853203853496601799 80693404279805780244902699)
  ·
    refine ⟨121040106419708670367354049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80693404279805780244902699 121040106419708670367354049)
    ·
      refine ⟨90780079814781502775515537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121040106419708670367354049 90780079814781502775515537)
      ·
        refine ⟨68085059861086127081636653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90780079814781502775515537 68085059861086127081636653)
        ·
          refine ⟨25531897447907297655613745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68085059861086127081636653 25531897447907297655613745)
          ·
            refine ⟨19148923085930473241710309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25531897447907297655613745 19148923085930473241710309)
            ·
              refine ⟨3590423078611963732820683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19148923085930473241710309 3590423078611963732820683)
              ·
                refine ⟨5385634617917945599231025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590423078611963732820683 5385634617917945599231025)
                ·
                  refine ⟨4039225963438459199423269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5385634617917945599231025 4039225963438459199423269)
                  ·
                    refine ⟨757354868144711099891863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4039225963438459199423269 757354868144711099891863)
                    ·
                      rfl

theorem cell22_2212415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_2212415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212415 prefixEnd_2212415 := by exact prefixLift 2212415
  have htrace : WordTrace (prefixWord ++ tailWord_2212415) baseStart_2212415 baseEnd_2212415 := by
    simpa [prefixWord, tailWord_2212415, baseEnd_2212415] using wordTrace_append hprefix tailTrace_2212415
  have hstable : (prefixWord ++ tailWord_2212415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212415).length < 2 ^ (prefixWord ++ tailWord_2212415).sum := by decide
  have hdescent : baseEnd_2212415 < baseStart_2212415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212462 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2212462 : Nat := 118140960795 + 2212462 * 2 ^ 59
def prefixEnd_2212462 : Nat := 4983230072969 + 3 ^ 40 * 2212462 * 2
def baseEnd_2212462 : Nat := 757370957205218643966719

theorem tailTrace_2212462 : CollatzResearch.WordTrace tailWord_2212462 prefixEnd_2212462 757370957205218643966719 := by
  unfold tailWord_2212462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10086889813829438408982955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53796745673757004847909093 10086889813829438408982955)
  ·
    refine ⟨15130334720744157613474433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10086889813829438408982955 15130334720744157613474433)
    ·
      refine ⟨11347751040558118210105825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15130334720744157613474433 11347751040558118210105825)
      ·
        refine ⟨8510813280418588657579369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11347751040558118210105825 8510813280418588657579369)
        ·
          refine ⟨6383109960313941493184527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8510813280418588657579369 6383109960313941493184527)
          ·
            refine ⟨9574664940470912239776791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6383109960313941493184527 9574664940470912239776791)
            ·
              refine ⟨14361997410706368359665187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9574664940470912239776791 14361997410706368359665187)
              ·
                refine ⟨21542996116059552539497781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14361997410706368359665187 21542996116059552539497781)
                ·
                  refine ⟨2019655885880583050577917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21542996116059552539497781 2019655885880583050577917)
                  ·
                    refine ⟨757370957205218643966719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2019655885880583050577917 757370957205218643966719)
                    ·
                      rfl

theorem cell22_2212462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2212462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212462 prefixEnd_2212462 := by exact prefixLift 2212462
  have htrace : WordTrace (prefixWord ++ tailWord_2212462) baseStart_2212462 baseEnd_2212462 := by
    simpa [prefixWord, tailWord_2212462, baseEnd_2212462] using wordTrace_append hprefix tailTrace_2212462
  have hstable : (prefixWord ++ tailWord_2212462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212462).length < 2 ^ (prefixWord ++ tailWord_2212462).sum := by decide
  have hdescent : baseEnd_2212462 < baseStart_2212462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212552 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 4, 3]
def baseStart_2212552 : Nat := 118140960795 + 2212552 * 2 ^ 59
def prefixEnd_2212552 : Nat := 4983230072969 + 3 ^ 40 * 2212552 * 2
def baseEnd_2212552 : Nat := 757401766044488409216443

theorem tailTrace_2212552 : CollatzResearch.WordTrace tailWord_2212552 prefixEnd_2212552 757401766044488409216443 := by
  unfold tailWord_2212552
  simp only [CollatzResearch.WordTrace]
  refine ⟨40349200540154726321319955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53798934053539635095093273 40349200540154726321319955)
  ·
    refine ⟨60523800810232089481979933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40349200540154726321319955 60523800810232089481979933)
    ·
      refine ⟨22696425303837033555742475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60523800810232089481979933 22696425303837033555742475)
      ·
        refine ⟨34044637955755550333613713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22696425303837033555742475 34044637955755550333613713)
        ·
          refine ⟨25533478466816662750210285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34044637955755550333613713 25533478466816662750210285)
          ·
            refine ⟨9575054425056248531328857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25533478466816662750210285 9575054425056248531328857)
            ·
              refine ⟨7181290818792186398496643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9575054425056248531328857 7181290818792186398496643)
              ·
                refine ⟨10771936228188279597744965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7181290818792186398496643 10771936228188279597744965)
                ·
                  refine ⟨2019738042785302424577181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10771936228188279597744965 2019738042785302424577181)
                  ·
                    refine ⟨757401766044488409216443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2019738042785302424577181 757401766044488409216443)
                    ·
                      rfl

theorem cell22_2212552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_2212552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212552 prefixEnd_2212552 := by exact prefixLift 2212552
  have htrace : WordTrace (prefixWord ++ tailWord_2212552) baseStart_2212552 baseEnd_2212552 := by
    simpa [prefixWord, tailWord_2212552, baseEnd_2212552] using wordTrace_append hprefix tailTrace_2212552
  have hstable : (prefixWord ++ tailWord_2212552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212552).length < 2 ^ (prefixWord ++ tailWord_2212552).sum := by decide
  have hdescent : baseEnd_2212552 < baseStart_2212552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212584 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_2212584 : Nat := 118140960795 + 2212584 * 2 ^ 59
def prefixEnd_2212584 : Nat := 4983230072969 + 3 ^ 40 * 2212584 * 2
def baseEnd_2212584 : Nat := 757412720298450992416345

theorem tailTrace_2212584 : CollatzResearch.WordTrace tailWord_2212584 prefixEnd_2212584 757412720298450992416345 := by
  unfold tailWord_2212584
  simp only [CollatzResearch.WordTrace]
  refine ⟨40349784108096761053902403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53799712144129014738536537 40349784108096761053902403)
  ·
    refine ⟨60524676162145141580853605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40349784108096761053902403 60524676162145141580853605)
    ·
      refine ⟨11348376780402214046410051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60524676162145141580853605 11348376780402214046410051)
      ·
        refine ⟨17022565170603321069615077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11348376780402214046410051 17022565170603321069615077)
        ·
          refine ⟨3191730969488122700552827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17022565170603321069615077 3191730969488122700552827)
          ·
            refine ⟨4787596454232184050829241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191730969488122700552827 4787596454232184050829241)
            ·
              refine ⟨3590697340674138038121931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4787596454232184050829241 3590697340674138038121931)
              ·
                refine ⟨5386046011011207057182897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590697340674138038121931 5386046011011207057182897)
                ·
                  refine ⟨4039534508258405292887173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5386046011011207057182897 4039534508258405292887173)
                  ·
                    refine ⟨757412720298450992416345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4039534508258405292887173 757412720298450992416345)
                    ·
                      rfl

theorem cell22_2212584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_2212584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212584 prefixEnd_2212584 := by exact prefixLift 2212584
  have htrace : WordTrace (prefixWord ++ tailWord_2212584) baseStart_2212584 baseEnd_2212584 := by
    simpa [prefixWord, tailWord_2212584, baseEnd_2212584] using wordTrace_append hprefix tailTrace_2212584
  have hstable : (prefixWord ++ tailWord_2212584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212584).length < 2 ^ (prefixWord ++ tailWord_2212584).sum := by decide
  have hdescent : baseEnd_2212584 < baseStart_2212584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212625 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_2212625 : Nat := 118140960795 + 2212625 * 2 ^ 59
def prefixEnd_2212625 : Nat := 4983230072969 + 3 ^ 40 * 2212625 * 2
def baseEnd_2212625 : Nat := 757426755436340552141219

theorem tailTrace_2212625 : CollatzResearch.WordTrace tailWord_2212625 prefixEnd_2212625 757426755436340552141219 := by
  unfold tailWord_2212625
  simp only [CollatzResearch.WordTrace]
  refine ⟨80701063609044986110047329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53800709072696657406698219 80701063609044986110047329)
  ·
    refine ⟨60525797706783739582535497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80701063609044986110047329 60525797706783739582535497)
    ·
      refine ⟨45394348280087804686901623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60525797706783739582535497 45394348280087804686901623)
      ·
        refine ⟨68091522420131707030352435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45394348280087804686901623 68091522420131707030352435)
        ·
          refine ⟨102137283630197560545528653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68091522420131707030352435 102137283630197560545528653)
          ·
            refine ⟨38301481361324085204573245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102137283630197560545528653 38301481361324085204573245)
            ·
              refine ⟨14363055510496531951714967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38301481361324085204573245 14363055510496531951714967)
              ·
                refine ⟨21544583265744797927572451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14363055510496531951714967 21544583265744797927572451)
                ·
                  refine ⟨32316874898617196891358677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21544583265744797927572451 32316874898617196891358677)
                  ·
                    refine ⟨757426755436340552141219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32316874898617196891358677 757426755436340552141219)
                    ·
                      rfl

theorem cell22_2212625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_2212625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212625 prefixEnd_2212625 := by exact prefixLift 2212625
  have htrace : WordTrace (prefixWord ++ tailWord_2212625) baseStart_2212625 baseEnd_2212625 := by
    simpa [prefixWord, tailWord_2212625, baseEnd_2212625] using wordTrace_append hprefix tailTrace_2212625
  have hstable : (prefixWord ++ tailWord_2212625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212625).length < 2 ^ (prefixWord ++ tailWord_2212625).sum := by decide
  have hdescent : baseEnd_2212625 < baseStart_2212625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212777 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_2212777 : Nat := 118140960795 + 2212777 * 2 ^ 59
def prefixEnd_2212777 : Nat := 4983230072969 + 3 ^ 40 * 2212777 * 2
def baseEnd_2212777 : Nat := 757478788142662822340753

theorem tailTrace_2212777 : CollatzResearch.WordTrace tailWord_2212777 prefixEnd_2212777 757478788142662822340753 := by
  unfold tailWord_2212777
  simp only [CollatzResearch.WordTrace]
  refine ⟨80706607504494316069580585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53804405002996210713053723 80706607504494316069580585)
  ·
    refine ⟨60529955628370737052185439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80706607504494316069580585 60529955628370737052185439)
    ·
      refine ⟨90794933442556105578278159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60529955628370737052185439 90794933442556105578278159)
      ·
        refine ⟨136192400163834158367417239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90794933442556105578278159 136192400163834158367417239)
        ·
          refine ⟨204288600245751237551125859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136192400163834158367417239 204288600245751237551125859)
          ·
            refine ⟨306432900368626856326688789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204288600245751237551125859 306432900368626856326688789)
            ·
              refine ⟨14364042204779383890313537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 306432900368626856326688789 14364042204779383890313537)
              ·
                refine ⟨10773031653584537917735153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14364042204779383890313537 10773031653584537917735153)
                ·
                  refine ⟨8079773740188403438301365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10773031653584537917735153 8079773740188403438301365)
                  ·
                    refine ⟨757478788142662822340753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8079773740188403438301365 757478788142662822340753)
                    ·
                      rfl

theorem cell22_2212777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_2212777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212777 prefixEnd_2212777 := by exact prefixLift 2212777
  have htrace : WordTrace (prefixWord ++ tailWord_2212777) baseStart_2212777 baseEnd_2212777 := by
    simpa [prefixWord, tailWord_2212777, baseEnd_2212777] using wordTrace_append hprefix tailTrace_2212777
  have hstable : (prefixWord ++ tailWord_2212777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212777).length < 2 ^ (prefixWord ++ tailWord_2212777).sum := by decide
  have hdescent : baseEnd_2212777 < baseStart_2212777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212807 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 8]
def baseStart_2212807 : Nat := 118140960795 + 2212807 * 2 ^ 59
def prefixEnd_2212807 : Nat := 4983230072969 + 3 ^ 40 * 2212807 * 2
def baseEnd_2212807 : Nat := 252496352585250914696887

theorem tailTrace_2212807 : CollatzResearch.WordTrace tailWord_2212807 prefixEnd_2212807 252496352585250914696887 := by
  unfold tailWord_2212807
  simp only [CollatzResearch.WordTrace]
  refine ⟨80707701694385631193172675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53805134462923754128781783 80707701694385631193172675)
  ·
    refine ⟨121061552541578446789759013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80707701694385631193172675 121061552541578446789759013)
    ·
      refine ⟨22699041101545958773079815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121061552541578446789759013 22699041101545958773079815)
      ·
        refine ⟨34048561652318938159619723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22699041101545958773079815 34048561652318938159619723)
        ·
          refine ⟨51072842478478407239429585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34048561652318938159619723 51072842478478407239429585)
          ·
            refine ⟨38304631858858805429572189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51072842478478407239429585 38304631858858805429572189)
            ·
              refine ⟨14364236947072052036089571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38304631858858805429572189 14364236947072052036089571)
              ·
                refine ⟨21546355420608078054134357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14364236947072052036089571 21546355420608078054134357)
                ·
                  refine ⟨252496352585250914696887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21546355420608078054134357 252496352585250914696887)
                  ·
                    rfl

theorem cell22_2212807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 8].length) (baseStart_2212807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212807 prefixEnd_2212807 := by exact prefixLift 2212807
  have htrace : WordTrace (prefixWord ++ tailWord_2212807) baseStart_2212807 baseEnd_2212807 := by
    simpa [prefixWord, tailWord_2212807, baseEnd_2212807] using wordTrace_append hprefix tailTrace_2212807
  have hstable : (prefixWord ++ tailWord_2212807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212807).length < 2 ^ (prefixWord ++ tailWord_2212807).sum := by decide
  have hdescent : baseEnd_2212807 < baseStart_2212807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212826 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_2212826 : Nat := 118140960795 + 2212826 * 2 ^ 59
def prefixEnd_2212826 : Nat := 4983230072969 + 3 ^ 40 * 2212826 * 2
def baseEnd_2212826 : Nat := 757495561844043027865603

theorem tailTrace_2212826 : CollatzResearch.WordTrace tailWord_2212826 prefixEnd_2212826 757495561844043027865603 := by
  unfold tailWord_2212826
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177098670329199359528583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53805596454211198292076221 20177098670329199359528583)
  ·
    refine ⟨30265648005493799039292875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20177098670329199359528583 30265648005493799039292875)
    ·
      refine ⟨45398472008240698558939313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30265648005493799039292875 45398472008240698558939313)
      ·
        refine ⟨34048854006180523919204485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45398472008240698558939313 34048854006180523919204485)
        ·
          refine ⟨6384160126158848234850841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34048854006180523919204485 6384160126158848234850841)
          ·
            refine ⟨4788120094619136176138131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6384160126158848234850841 4788120094619136176138131)
            ·
              refine ⟨7182180141928704264207197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4788120094619136176138131 7182180141928704264207197)
              ·
                refine ⟨2693317553223264099077699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7182180141928704264207197 2693317553223264099077699)
                ·
                  refine ⟨4039976329834896148616549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693317553223264099077699 4039976329834896148616549)
                  ·
                    refine ⟨757495561844043027865603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4039976329834896148616549 757495561844043027865603)
                    ·
                      rfl

theorem cell22_2212826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_2212826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212826 prefixEnd_2212826 := by exact prefixLift 2212826
  have htrace : WordTrace (prefixWord ++ tailWord_2212826) baseStart_2212826 baseEnd_2212826 := by
    simpa [prefixWord, tailWord_2212826, baseEnd_2212826] using wordTrace_append hprefix tailTrace_2212826
  have hstable : (prefixWord ++ tailWord_2212826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212826).length < 2 ^ (prefixWord ++ tailWord_2212826).sum := by decide
  have hdescent : baseEnd_2212826 < baseStart_2212826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212959 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 6]
def baseStart_2212959 : Nat := 118140960795 + 2212959 * 2 ^ 59
def prefixEnd_2212959 : Nat := 4983230072969 + 3 ^ 40 * 2212959 * 2
def baseEnd_2212959 : Nat := 252513696820691671430065

theorem tailTrace_2212959 : CollatzResearch.WordTrace tailWord_2212959 prefixEnd_2212959 252513696820691671430065 := by
  unfold tailWord_2212959
  simp only [CollatzResearch.WordTrace]
  refine ⟨80713245589834961152705931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53808830393223307435137287 80713245589834961152705931)
  ·
    refine ⟨121069868384752441729058897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80713245589834961152705931 121069868384752441729058897)
    ·
      refine ⟨90802401288564331296794173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121069868384752441729058897 90802401288564331296794173)
      ·
        refine ⟨34050900483211624236297815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90802401288564331296794173 34050900483211624236297815)
        ·
          refine ⟨51076350724817436354446723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34050900483211624236297815 51076350724817436354446723)
          ·
            refine ⟨76614526087226154531670085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51076350724817436354446723 76614526087226154531670085)
            ·
              refine ⟨14365223641354903974688141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76614526087226154531670085 14365223641354903974688141)
              ·
                refine ⟨5386958865508088990508053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14365223641354903974688141 5386958865508088990508053)
                ·
                  refine ⟨252513696820691671430065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5386958865508088990508053 252513696820691671430065)
                  ·
                    rfl

theorem cell22_2212959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 6].length) (baseStart_2212959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212959 prefixEnd_2212959 := by exact prefixLift 2212959
  have htrace : WordTrace (prefixWord ++ tailWord_2212959) baseStart_2212959 baseEnd_2212959 := by
    simpa [prefixWord, tailWord_2212959, baseEnd_2212959] using wordTrace_append hprefix tailTrace_2212959
  have hstable : (prefixWord ++ tailWord_2212959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212959).length < 2 ^ (prefixWord ++ tailWord_2212959).sum := by decide
  have hdescent : baseEnd_2212959 < baseStart_2212959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212993 : List Nat := [1, 2, 4, 2, 2, 1, 1, 5, 4]
def baseStart_2212993 : Nat := 118140960795 + 2212993 * 2 ^ 59
def prefixEnd_2212993 : Nat := 4983230072969 + 3 ^ 40 * 2212993 * 2
def baseEnd_2212993 : Nat := 252517576452303419646697

theorem tailTrace_2212993 : CollatzResearch.WordTrace tailWord_2212993 prefixEnd_2212993 252517576452303419646697 := by
  unfold tailWord_2212993
  simp only [CollatzResearch.WordTrace]
  refine ⟨80714485671711784959443633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53809657114474523306295755 80714485671711784959443633)
  ·
    refine ⟨60535864253783838719582725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80714485671711784959443633 60535864253783838719582725)
    ·
      refine ⟨11350474547584469759921761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60535864253783838719582725 11350474547584469759921761)
      ·
        refine ⟨8512855910688352319941321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11350474547584469759921761 8512855910688352319941321)
        ·
          refine ⟨6384641933016264239955991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8512855910688352319941321 6384641933016264239955991)
          ·
            refine ⟨9576962899524396359933987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6384641933016264239955991 9576962899524396359933987)
            ·
              refine ⟨14365444349286594539900981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9576962899524396359933987 14365444349286594539900981)
              ·
                refine ⟨1346760407745618238115717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14365444349286594539900981 1346760407745618238115717)
                ·
                  refine ⟨252517576452303419646697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1346760407745618238115717 252517576452303419646697)
                  ·
                    rfl

theorem cell22_2212993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 4].length) (baseStart_2212993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2212993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2212993 prefixEnd_2212993 := by exact prefixLift 2212993
  have htrace : WordTrace (prefixWord ++ tailWord_2212993) baseStart_2212993 baseEnd_2212993 := by
    simpa [prefixWord, tailWord_2212993, baseEnd_2212993] using wordTrace_append hprefix tailTrace_2212993
  have hstable : (prefixWord ++ tailWord_2212993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212993).length < 2 ^ (prefixWord ++ tailWord_2212993).sum := by decide
  have hdescent : baseEnd_2212993 < baseStart_2212993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213025 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 2, 3]
def baseStart_2213025 : Nat := 118140960795 + 2213025 * 2 ^ 59
def prefixEnd_2213025 : Nat := 4983230072969 + 3 ^ 40 * 2213025 * 2
def baseEnd_2213025 : Nat := 757563683610872842139993

theorem tailTrace_2213025 : CollatzResearch.WordTrace tailWord_2213025 prefixEnd_2213025 757563683610872842139993 := by
  unfold tailWord_2213025
  simp only [CollatzResearch.WordTrace]
  refine ⟨80715652807595854424608529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53810435205063902949739019 80715652807595854424608529)
  ·
    refine ⟨60536739605696890818456397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80715652807595854424608529 60536739605696890818456397)
    ·
      refine ⟨22701277352136334056921149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60536739605696890818456397 22701277352136334056921149)
      ·
        refine ⟨8512979007051125271345431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22701277352136334056921149 8512979007051125271345431)
        ·
          refine ⟨12769468510576687907018147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8512979007051125271345431 12769468510576687907018147)
          ·
            refine ⟨19154202765865031860527221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12769468510576687907018147 19154202765865031860527221)
            ·
              refine ⟨1795706509299846736924427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19154202765865031860527221 1795706509299846736924427)
              ·
                refine ⟨2693559763949770105386641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795706509299846736924427 2693559763949770105386641)
                ·
                  refine ⟨2020169822962327579039981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2693559763949770105386641 2020169822962327579039981)
                  ·
                    refine ⟨757563683610872842139993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2020169822962327579039981 757563683610872842139993)
                    ·
                      rfl

theorem cell22_2213025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_2213025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213025 prefixEnd_2213025 := by exact prefixLift 2213025
  have htrace : WordTrace (prefixWord ++ tailWord_2213025) baseStart_2213025 baseEnd_2213025 := by
    simpa [prefixWord, tailWord_2213025, baseEnd_2213025] using wordTrace_append hprefix tailTrace_2213025
  have hstable : (prefixWord ++ tailWord_2213025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213025).length < 2 ^ (prefixWord ++ tailWord_2213025).sum := by decide
  have hdescent : baseEnd_2213025 < baseStart_2213025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213036 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_2213036 : Nat := 118140960795 + 2213036 * 2 ^ 59
def prefixEnd_2213036 : Nat := 4983230072969 + 3 ^ 40 * 2213036 * 2
def baseEnd_2213036 : Nat := 757567449135672480114959

theorem tailTrace_2213036 : CollatzResearch.WordTrace tailWord_2213036 prefixEnd_2213036 757567449135672480114959 := by
  unfold tailWord_2213036
  simp only [CollatzResearch.WordTrace]
  refine ⟨40358027005278001651629481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53810702673704002202172641 40358027005278001651629481)
  ·
    refine ⟨30268520253958501238722111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40358027005278001651629481 30268520253958501238722111)
    ·
      refine ⟨45402780380937751858083167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30268520253958501238722111 45402780380937751858083167)
      ·
        refine ⟨68104170571406627787124751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45402780380937751858083167 68104170571406627787124751)
        ·
          refine ⟨102156255857109941680687127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68104170571406627787124751 102156255857109941680687127)
          ·
            refine ⟨153234383785664912521030691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102156255857109941680687127 153234383785664912521030691)
            ·
              refine ⟨229851575678497368781546037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153234383785664912521030691 229851575678497368781546037)
              ·
                refine ⟨21548585219859128323269941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229851575678497368781546037 21548585219859128323269941)
                ·
                  refine ⟨2020179864361793280306557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21548585219859128323269941 2020179864361793280306557)
                  ·
                    refine ⟨757567449135672480114959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2020179864361793280306557 757567449135672480114959)
                    ·
                      rfl

theorem cell22_2213036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_2213036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213036 prefixEnd_2213036 := by exact prefixLift 2213036
  have htrace : WordTrace (prefixWord ++ tailWord_2213036) baseStart_2213036 baseEnd_2213036 := by
    simpa [prefixWord, tailWord_2213036, baseEnd_2213036] using wordTrace_append hprefix tailTrace_2213036
  have hstable : (prefixWord ++ tailWord_2213036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213036).length < 2 ^ (prefixWord ++ tailWord_2213036).sum := by decide
  have hdescent : baseEnd_2213036 < baseStart_2213036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213066 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_2213066 : Nat := 118140960795 + 2213066 * 2 ^ 59
def prefixEnd_2213066 : Nat := 4983230072969 + 3 ^ 40 * 2213066 * 2
def baseEnd_2213066 : Nat := 252525906249587467288289

theorem tailTrace_2213066 : CollatzResearch.WordTrace tailWord_2213066 prefixEnd_2213066 252525906249587467288289 := by
  unfold tailWord_2213066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20179287050111829606712763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53811432133631545617900701 20179287050111829606712763)
  ·
    refine ⟨30268930575167744410069145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20179287050111829606712763 30268930575167744410069145)
    ·
      refine ⟨22701697931375808307551859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30268930575167744410069145 22701697931375808307551859)
      ·
        refine ⟨34052546897063712461327789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22701697931375808307551859 34052546897063712461327789)
        ·
          refine ⟨12769705086398892172997921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34052546897063712461327789 12769705086398892172997921)
          ·
            refine ⟨9577278814799169129748441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12769705086398892172997921 9577278814799169129748441)
            ·
              refine ⟨7182959111099376847311331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9577278814799169129748441 7182959111099376847311331)
              ·
                refine ⟨10774438666649065270966997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7182959111099376847311331 10774438666649065270966997)
                ·
                  refine ⟨252525906249587467288289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10774438666649065270966997 252525906249587467288289)
                  ·
                    rfl

theorem cell22_2213066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_2213066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213066 prefixEnd_2213066 := by exact prefixLift 2213066
  have htrace : WordTrace (prefixWord ++ tailWord_2213066) baseStart_2213066 baseEnd_2213066 := by
    simpa [prefixWord, tailWord_2213066, baseEnd_2213066] using wordTrace_append hprefix tailTrace_2213066
  have hstable : (prefixWord ++ tailWord_2213066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213066).length < 2 ^ (prefixWord ++ tailWord_2213066).sum := by decide
  have hdescent : baseEnd_2213066 < baseStart_2213066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213076 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2213076 : Nat := 118140960795 + 2213076 * 2 ^ 59
def prefixEnd_2213076 : Nat := 4983230072969 + 3 ^ 40 * 2213076 * 2
def baseEnd_2213076 : Nat := 757581141953125709114837

theorem tailTrace_2213076 : CollatzResearch.WordTrace tailWord_2213076 prefixEnd_2213076 757581141953125709114837 := by
  unfold tailWord_2213076
  simp only [CollatzResearch.WordTrace]
  refine ⟨40358756465205545067357541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53811675286940726756476721 40358756465205545067357541)
  ·
    refine ⟨7567266837226039700129539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40358756465205545067357541 7567266837226039700129539)
    ·
      refine ⟨11350900255839059550194309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7567266837226039700129539 11350900255839059550194309)
      ·
        refine ⟨2128293797969823665661433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11350900255839059550194309 2128293797969823665661433)
        ·
          refine ⟨1596220348477367749246075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2128293797969823665661433 1596220348477367749246075)
          ·
            refine ⟨2394330522716051623869113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596220348477367749246075 2394330522716051623869113)
            ·
              refine ⟨1795747892037038717901835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394330522716051623869113 1795747892037038717901835)
              ·
                refine ⟨2693621838055558076852753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795747892037038717901835 2693621838055558076852753)
                ·
                  refine ⟨2020216378541668557639565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2693621838055558076852753 2020216378541668557639565)
                  ·
                    refine ⟨757581141953125709114837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2020216378541668557639565 757581141953125709114837)
                    ·
                      rfl

theorem cell22_2213076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2213076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213076 prefixEnd_2213076 := by exact prefixLift 2213076
  have htrace : WordTrace (prefixWord ++ tailWord_2213076) baseStart_2213076 baseEnd_2213076 := by
    simpa [prefixWord, tailWord_2213076, baseEnd_2213076] using wordTrace_append hprefix tailTrace_2213076
  have hstable : (prefixWord ++ tailWord_2213076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213076).length < 2 ^ (prefixWord ++ tailWord_2213076).sum := by decide
  have hdescent : baseEnd_2213076 < baseStart_2213076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213141 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_2213141 : Nat := 118140960795 + 2213141 * 2 ^ 59
def prefixEnd_2213141 : Nat := 4983230072969 + 3 ^ 40 * 2213141 * 2
def baseEnd_2213141 : Nat := 757603392781487206239637

theorem tailTrace_2213141 : CollatzResearch.WordTrace tailWord_2213141 prefixEnd_2213141 757603392781487206239637 := by
  unfold tailWord_2213141
  simp only [CollatzResearch.WordTrace]
  refine ⟨80719883675175606235831277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53813255783450404157220851 80719883675175606235831277)
  ·
    refine ⟨30269956378190852338436729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80719883675175606235831277 30269956378190852338436729)
    ·
      refine ⟨22702467283643139253827547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30269956378190852338436729 22702467283643139253827547)
      ·
        refine ⟨34053700925464708880741321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22702467283643139253827547 34053700925464708880741321)
        ·
          refine ⟨25540275694098531660555991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34053700925464708880741321 25540275694098531660555991)
          ·
            refine ⟨38310413541147797490833987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25540275694098531660555991 38310413541147797490833987)
            ·
              refine ⟨57465620311721696236250981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38310413541147797490833987 57465620311721696236250981)
              ·
                refine ⟨10774803808447818044297059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57465620311721696236250981 10774803808447818044297059)
                ·
                  refine ⟨16162205712671727066445589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10774803808447818044297059 16162205712671727066445589)
                  ·
                    refine ⟨757603392781487206239637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16162205712671727066445589 757603392781487206239637)
                    ·
                      rfl

theorem cell22_2213141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_2213141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213141 prefixEnd_2213141 := by exact prefixLift 2213141
  have htrace : WordTrace (prefixWord ++ tailWord_2213141) baseStart_2213141 baseEnd_2213141 := by
    simpa [prefixWord, tailWord_2213141, baseEnd_2213141] using wordTrace_append hprefix tailTrace_2213141
  have hstable : (prefixWord ++ tailWord_2213141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213141).length < 2 ^ (prefixWord ++ tailWord_2213141).sum := by decide
  have hdescent : baseEnd_2213141 < baseStart_2213141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213143 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 1, 5]
def baseStart_2213143 : Nat := 118140960795 + 2213143 * 2 ^ 59
def prefixEnd_2213143 : Nat := 4983230072969 + 3 ^ 40 * 2213143 * 2
def baseEnd_2213143 : Nat := 757604077422359867689631

theorem tailTrace_2213143 : CollatzResearch.WordTrace tailWord_2213143 prefixEnd_2213143 757604077422359867689631 := by
  unfold tailWord_2213143
  simp only [CollatzResearch.WordTrace]
  refine ⟨80719956621168360577404083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53813304414112240384936055 80719956621168360577404083)
  ·
    refine ⟨121079934931752540866106125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80719956621168360577404083 121079934931752540866106125)
    ·
      refine ⟨45404975599407202824789797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121079934931752540866106125 45404975599407202824789797)
      ·
        refine ⟨8513432924888850529648087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45404975599407202824789797 8513432924888850529648087)
        ·
          refine ⟨12770149387333275794472131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8513432924888850529648087 12770149387333275794472131)
          ·
            refine ⟨19155224080999913691708197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12770149387333275794472131 19155224080999913691708197)
            ·
              refine ⟨3591604515187483817195287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19155224080999913691708197 3591604515187483817195287)
              ·
                refine ⟨5387406772781225725792931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591604515187483817195287 5387406772781225725792931)
                ·
                  refine ⟨8081110159171838588689397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5387406772781225725792931 8081110159171838588689397)
                  ·
                    refine ⟨757604077422359867689631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8081110159171838588689397 757604077422359867689631)
                    ·
                      rfl

theorem cell22_2213143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_2213143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213143 prefixEnd_2213143 := by exact prefixLift 2213143
  have htrace : WordTrace (prefixWord ++ tailWord_2213143) baseStart_2213143 baseEnd_2213143 := by
    simpa [prefixWord, tailWord_2213143, baseEnd_2213143] using wordTrace_append hprefix tailTrace_2213143
  have hstable : (prefixWord ++ tailWord_2213143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213143).length < 2 ^ (prefixWord ++ tailWord_2213143).sum := by decide
  have hdescent : baseEnd_2213143 < baseStart_2213143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213162 : List Nat := [3, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_2213162 : Nat := 118140960795 + 2213162 * 2 ^ 59
def prefixEnd_2213162 : Nat := 4983230072969 + 3 ^ 40 * 2213162 * 2
def baseEnd_2213162 : Nat := 252536860503550050488191

theorem tailTrace_2213162 : CollatzResearch.WordTrace tailWord_2213162 prefixEnd_2213162 252536860503550050488191 := by
  unfold tailWord_2213162
  simp only [CollatzResearch.WordTrace]
  refine ⟨20180162402024881705586435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53813766405399684548230493 20180162402024881705586435)
  ·
    refine ⟨30270243603037322558379653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20180162402024881705586435 30270243603037322558379653)
    ·
      refine ⟨5675670675569497979696185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30270243603037322558379653 5675670675569497979696185)
      ·
        refine ⟨4256753006677123484772139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5675670675569497979696185 4256753006677123484772139)
        ·
          refine ⟨6385129510015685227158209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4256753006677123484772139 6385129510015685227158209)
          ·
            refine ⟨4788847132511763920368657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6385129510015685227158209 4788847132511763920368657)
            ·
              refine ⟨3591635349383822940276493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4788847132511763920368657 3591635349383822940276493)
              ·
                refine ⟨1346863256018933602603685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3591635349383822940276493 1346863256018933602603685)
                ·
                  refine ⟨252536860503550050488191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1346863256018933602603685 252536860503550050488191)
                  ·
                    rfl

theorem cell22_2213162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_2213162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213162 prefixEnd_2213162 := by exact prefixLift 2213162
  have htrace : WordTrace (prefixWord ++ tailWord_2213162) baseStart_2213162 baseEnd_2213162 := by
    simpa [prefixWord, tailWord_2213162, baseEnd_2213162] using wordTrace_append hprefix tailTrace_2213162
  have hstable : (prefixWord ++ tailWord_2213162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213162).length < 2 ^ (prefixWord ++ tailWord_2213162).sum := by decide
  have hdescent : baseEnd_2213162 < baseStart_2213162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213205 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_2213205 : Nat := 118140960795 + 2213205 * 2 ^ 59
def prefixEnd_2213205 : Nat := 4983230072969 + 3 ^ 40 * 2213205 * 2
def baseEnd_2213205 : Nat := 757625301289412372639441

theorem tailTrace_2213205 : CollatzResearch.WordTrace tailWord_2213205 prefixEnd_2213205 757625301289412372639441 := by
  unfold tailWord_2213205
  simp only [CollatzResearch.WordTrace]
  refine ⟨80722217946943745166161069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53814811964629163444107379 80722217946943745166161069)
  ·
    refine ⟨30270831730103904437310401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80722217946943745166161069 30270831730103904437310401)
    ·
      refine ⟨22703123797577928327982801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30270831730103904437310401 22703123797577928327982801)
      ·
        refine ⟨17027342848183446245987101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22703123797577928327982801 17027342848183446245987101)
        ·
          refine ⟨6385253568068792342245163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17027342848183446245987101 6385253568068792342245163)
          ·
            refine ⟨9577880352103188513367745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6385253568068792342245163 9577880352103188513367745)
            ·
              refine ⟨7183410264077391385025809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9577880352103188513367745 7183410264077391385025809)
              ·
                refine ⟨5387557698058043538769357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7183410264077391385025809 5387557698058043538769357)
                ·
                  refine ⟨2020334136771766327038509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5387557698058043538769357 2020334136771766327038509)
                  ·
                    refine ⟨757625301289412372639441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2020334136771766327038509 757625301289412372639441)
                    ·
                      rfl

theorem cell22_2213205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_2213205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213205 prefixEnd_2213205 := by exact prefixLift 2213205
  have htrace : WordTrace (prefixWord ++ tailWord_2213205) baseStart_2213205 baseEnd_2213205 := by
    simpa [prefixWord, tailWord_2213205, baseEnd_2213205] using wordTrace_append hprefix tailTrace_2213205
  have hstable : (prefixWord ++ tailWord_2213205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213205).length < 2 ^ (prefixWord ++ tailWord_2213205).sum := by decide
  have hdescent : baseEnd_2213205 < baseStart_2213205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213213 : List Nat := [1, 4, 5, 1, 2, 1, 1, 3, 4]
def baseStart_2213213 : Nat := 118140960795 + 2213213 * 2 ^ 59
def prefixEnd_2213213 : Nat := 4983230072969 + 3 ^ 40 * 2213213 * 2
def baseEnd_2213213 : Nat := 252542679950967672813139

theorem tailTrace_2213213 : CollatzResearch.WordTrace tailWord_2213213 prefixEnd_2213213 252542679950967672813139 := by
  unfold tailWord_2213213
  simp only [CollatzResearch.WordTrace]
  refine ⟨80722509730914762532452293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53815006487276508354968195 80722509730914762532452293)
  ·
    refine ⟨15135470574546517974834805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80722509730914762532452293 15135470574546517974834805)
    ·
      refine ⟨1418950366363736060140763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15135470574546517974834805 1418950366363736060140763)
      ·
        refine ⟨2128425549545604090211145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418950366363736060140763 2128425549545604090211145)
        ·
          refine ⟨1596319162159203067658359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2128425549545604090211145 1596319162159203067658359)
          ·
            refine ⟨2394478743238804601487539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596319162159203067658359 2394478743238804601487539)
            ·
              refine ⟨3591718114858206902231309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394478743238804601487539 3591718114858206902231309)
              ·
                refine ⟨1346894293071827588336741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3591718114858206902231309 1346894293071827588336741)
                ·
                  refine ⟨252542679950967672813139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1346894293071827588336741 252542679950967672813139)
                  ·
                    rfl

theorem cell22_2213213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_2213213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2213213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2213213 prefixEnd_2213213 := by exact prefixLift 2213213
  have htrace : WordTrace (prefixWord ++ tailWord_2213213) baseStart_2213213 baseEnd_2213213 := by
    simpa [prefixWord, tailWord_2213213, baseEnd_2213213] using wordTrace_append hprefix tailTrace_2213213
  have hstable : (prefixWord ++ tailWord_2213213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213213).length < 2 ^ (prefixWord ++ tailWord_2213213).sum := by decide
  have hdescent : baseEnd_2213213 < baseStart_2213213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
