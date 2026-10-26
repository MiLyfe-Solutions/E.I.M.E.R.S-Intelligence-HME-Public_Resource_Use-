import V185TrunkScan22Chunk028

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_259913 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 9]
def baseStart_259913 : Nat := 118140960795 + 259913 * 2 ^ 59
def prefixEnd_259913 : Nat := 4983230072969 + 3 ^ 40 * 259913 * 2
def baseEnd_259913 : Nat := 29657843856032627309375

theorem tailTrace_259913 : CollatzResearch.WordTrace tailWord_259913 prefixEnd_259913 29657843856032627309375 := by
  unfold tailWord_259913
  simp only [CollatzResearch.WordTrace]
  refine ⟨9479805907387065451472393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6319870604924710300981595 9479805907387065451472393)
  ·
    refine ⟨7109854430540299088604295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9479805907387065451472393 7109854430540299088604295)
    ·
      refine ⟨10664781645810448632906443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7109854430540299088604295 10664781645810448632906443)
      ·
        refine ⟨15997172468715672949359665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10664781645810448632906443 15997172468715672949359665)
        ·
          refine ⟨11997879351536754712019749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15997172468715672949359665 11997879351536754712019749)
          ·
            refine ⟨2249602378413141508503703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11997879351536754712019749 2249602378413141508503703)
            ·
              refine ⟨3374403567619712262755555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249602378413141508503703 3374403567619712262755555)
              ·
                refine ⟨5061605351429568394133333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374403567619712262755555 5061605351429568394133333)
                ·
                  refine ⟨29657843856032627309375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5061605351429568394133333 29657843856032627309375)
                  ·
                    rfl

theorem cell22_259913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_259913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259913 prefixEnd_259913 := by exact prefixLift 259913
  have htrace : WordTrace (prefixWord ++ tailWord_259913) baseStart_259913 baseEnd_259913 := by
    simpa [prefixWord, tailWord_259913, baseEnd_259913] using wordTrace_append hprefix tailTrace_259913
  have hstable : (prefixWord ++ tailWord_259913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259913).length < 2 ^ (prefixWord ++ tailWord_259913).sum := by decide
  have hdescent : baseEnd_259913 < baseStart_259913 := by decide
  rcases family_descends (prefixWord ++ tailWord_259913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259930 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_259930 : Nat := 118140960795 + 259930 * 2 ^ 59
def prefixEnd_259930 : Nat := 4983230072969 + 3 ^ 40 * 259930 * 2
def baseEnd_259930 : Nat := 29659783671838501417691

theorem tailTrace_259930 : CollatzResearch.WordTrace tailWord_259930 prefixEnd_259930 29659783671838501417691 := by
  unfold tailWord_259930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370106487081369338710311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6320283965550318236560829 2370106487081369338710311)
  ·
    refine ⟨3555159730622054008065467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370106487081369338710311 3555159730622054008065467)
    ·
      refine ⟨5332739595933081012098201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555159730622054008065467 5332739595933081012098201)
      ·
        refine ⟨3999554696949810759073651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5332739595933081012098201 3999554696949810759073651)
        ·
          refine ⟨5999332045424716138610477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999554696949810759073651 5999332045424716138610477)
          ·
            refine ⟨2249749517034268551978929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5999332045424716138610477 2249749517034268551978929)
            ·
              refine ⟨1687312137775701413984197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2249749517034268551978929 1687312137775701413984197)
              ·
                refine ⟨316371025832944015122037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1687312137775701413984197 316371025832944015122037)
                ·
                  refine ⟨29659783671838501417691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 316371025832944015122037 29659783671838501417691)
                  ·
                    rfl

theorem cell22_259930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_259930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259930 prefixEnd_259930 := by exact prefixLift 259930
  have htrace : WordTrace (prefixWord ++ tailWord_259930) baseStart_259930 baseEnd_259930 := by
    simpa [prefixWord, tailWord_259930, baseEnd_259930] using wordTrace_append hprefix tailTrace_259930
  have hstable : (prefixWord ++ tailWord_259930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259930).length < 2 ^ (prefixWord ++ tailWord_259930).sum := by decide
  have hdescent : baseEnd_259930 < baseStart_259930 := by decide
  rcases family_descends (prefixWord ++ tailWord_259930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260005 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_260005 : Nat := 118140960795 + 260005 * 2 ^ 59
def prefixEnd_260005 : Nat := 4983230072969 + 3 ^ 40 * 260005 * 2
def baseEnd_260005 : Nat := 89005025048240308627843

theorem tailTrace_260005 : CollatzResearch.WordTrace tailWord_260005 prefixEnd_260005 89005025048240308627843 := by
  unfold tailWord_260005
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483161423053765163821469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6322107615369176775880979 9483161423053765163821469)
  ·
    refine ⟨3556185533645161936433051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9483161423053765163821469 3556185533645161936433051)
    ·
      refine ⟨5334278300467742904649577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556185533645161936433051 5334278300467742904649577)
      ·
        refine ⟨4000708725350807178487183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5334278300467742904649577 4000708725350807178487183)
        ·
          refine ⟨6001063088026210767730775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4000708725350807178487183 6001063088026210767730775)
          ·
            refine ⟨9001594632039316151596163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6001063088026210767730775 9001594632039316151596163)
            ·
              refine ⟨13502391948058974227394245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001594632039316151596163 13502391948058974227394245)
              ·
                refine ⟨2531698490261057667636421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13502391948058974227394245 2531698490261057667636421)
                ·
                  refine ⟨474693466923948312681829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531698490261057667636421 474693466923948312681829)
                  ·
                    refine ⟨89005025048240308627843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474693466923948312681829 89005025048240308627843)
                    ·
                      rfl

theorem cell22_260005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_260005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260005 prefixEnd_260005 := by exact prefixLift 260005
  have htrace : WordTrace (prefixWord ++ tailWord_260005) baseStart_260005 baseEnd_260005 := by
    simpa [prefixWord, tailWord_260005, baseEnd_260005] using wordTrace_append hprefix tailTrace_260005
  have hstable : (prefixWord ++ tailWord_260005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260005).length < 2 ^ (prefixWord ++ tailWord_260005).sum := by decide
  have hdescent : baseEnd_260005 < baseStart_260005 := by decide
  rcases family_descends (prefixWord ++ tailWord_260005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260007 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 1, 5]
def baseStart_260007 : Nat := 118140960795 + 260007 * 2 ^ 59
def prefixEnd_260007 : Nat := 4983230072969 + 3 ^ 40 * 260007 * 2
def baseEnd_260007 : Nat := 89005709689112970077837

theorem tailTrace_260007 : CollatzResearch.WordTrace tailWord_260007 prefixEnd_260007 89005709689112970077837 := by
  unfold tailWord_260007
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483234369046519505394275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6322156246031013003596183 9483234369046519505394275)
  ·
    refine ⟨14224851553569779258091413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9483234369046519505394275 14224851553569779258091413)
    ·
      refine ⟨666789916573583402723035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14224851553569779258091413 666789916573583402723035)
      ·
        refine ⟨1000184874860375104084553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666789916573583402723035 1000184874860375104084553)
        ·
          refine ⟨750138656145281328063415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000184874860375104084553 750138656145281328063415)
          ·
            refine ⟨1125207984217921992095123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750138656145281328063415 1125207984217921992095123)
            ·
              refine ⟨1687811976326882988142685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125207984217921992095123 1687811976326882988142685)
              ·
                refine ⟨632929491122581120553507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1687811976326882988142685 632929491122581120553507)
                ·
                  refine ⟨949394236683871680830261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632929491122581120553507 949394236683871680830261)
                  ·
                    refine ⟨89005709689112970077837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 949394236683871680830261 89005709689112970077837)
                    ·
                      rfl

theorem cell22_260007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_260007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260007 prefixEnd_260007 := by exact prefixLift 260007
  have htrace : WordTrace (prefixWord ++ tailWord_260007) baseStart_260007 baseEnd_260007 := by
    simpa [prefixWord, tailWord_260007, baseEnd_260007] using wordTrace_append hprefix tailTrace_260007
  have hstable : (prefixWord ++ tailWord_260007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260007).length < 2 ^ (prefixWord ++ tailWord_260007).sum := by decide
  have hdescent : baseEnd_260007 < baseStart_260007 := by decide
  rcases family_descends (prefixWord ++ tailWord_260007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260028 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_260028 : Nat := 118140960795 + 260028 * 2 ^ 59
def prefixEnd_260028 : Nat := 4983230072969 + 3 ^ 40 * 260028 * 2
def baseEnd_260028 : Nat := 89012898418275915302773

theorem tailTrace_260028 : CollatzResearch.WordTrace tailWord_260028 prefixEnd_260028 89012898418275915302773 := by
  unfold tailWord_260028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742000150985220045954369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6322666867980293394605825 4742000150985220045954369)
  ·
    refine ⟨3556500113238915034465777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4742000150985220045954369 3556500113238915034465777)
    ·
      refine ⟨2667375084929186275849333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3556500113238915034465777 2667375084929186275849333)
      ·
        refine ⟨250066414212111213360875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2667375084929186275849333 250066414212111213360875)
        ·
          refine ⟨375099621318166820041313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250066414212111213360875 375099621318166820041313)
          ·
            refine ⟨281324715988625115030985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375099621318166820041313 281324715988625115030985)
            ·
              refine ⟨210993536991468836273239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281324715988625115030985 210993536991468836273239)
              ·
                refine ⟨316490305487203254409859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210993536991468836273239 316490305487203254409859)
                ·
                  refine ⟨474735458230804881614789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316490305487203254409859 474735458230804881614789)
                  ·
                    refine ⟨89012898418275915302773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474735458230804881614789 89012898418275915302773)
                    ·
                      rfl

theorem cell22_260028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_260028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260028 prefixEnd_260028 := by exact prefixLift 260028
  have htrace : WordTrace (prefixWord ++ tailWord_260028) baseStart_260028 baseEnd_260028 := by
    simpa [prefixWord, tailWord_260028, baseEnd_260028] using wordTrace_append hprefix tailTrace_260028
  have hstable : (prefixWord ++ tailWord_260028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260028).length < 2 ^ (prefixWord ++ tailWord_260028).sum := by decide
  have hdescent : baseEnd_260028 < baseStart_260028 := by decide
  rcases family_descends (prefixWord ++ tailWord_260028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260071 : List Nat := [1, 1, 5, 2, 4, 1, 2, 6]
def baseStart_260071 : Nat := 118140960795 + 260071 * 2 ^ 59
def prefixEnd_260071 : Nat := 4983230072969 + 3 ^ 40 * 260071 * 2
def baseEnd_260071 : Nat := 9891957577448681830849

theorem tailTrace_260071 : CollatzResearch.WordTrace tailWord_260071 prefixEnd_260071 9891957577448681830849 := by
  unfold tailWord_260071
  simp only [CollatzResearch.WordTrace]
  refine ⟨9485568640814658435724067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6323712427209772290482711 9485568640814658435724067)
  ·
    refine ⟨14228352961221987653586101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9485568640814658435724067 14228352961221987653586101)
    ·
      refine ⟨1333908090114561342523697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14228352961221987653586101 1333908090114561342523697)
      ·
        refine ⟨1000431067585921006892773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1333908090114561342523697 1000431067585921006892773)
        ·
          refine ⟨187580825172360188792395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1000431067585921006892773 187580825172360188792395)
          ·
            refine ⟨281371237758540283188593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187580825172360188792395 281371237758540283188593)
            ·
              refine ⟨211028428318905212391445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281371237758540283188593 211028428318905212391445)
              ·
                refine ⟨9891957577448681830849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211028428318905212391445 9891957577448681830849)
                ·
                  rfl

theorem cell22_260071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 6].length) (baseStart_260071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260071 prefixEnd_260071 := by exact prefixLift 260071
  have htrace : WordTrace (prefixWord ++ tailWord_260071) baseStart_260071 baseEnd_260071 := by
    simpa [prefixWord, tailWord_260071, baseEnd_260071] using wordTrace_append hprefix tailTrace_260071
  have hstable : (prefixWord ++ tailWord_260071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260071).length < 2 ^ (prefixWord ++ tailWord_260071).sum := by decide
  have hdescent : baseEnd_260071 < baseStart_260071 := by decide
  rcases family_descends (prefixWord ++ tailWord_260071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260080 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_260080 : Nat := 118140960795 + 260080 * 2 ^ 59
def prefixEnd_260080 : Nat := 4983230072969 + 3 ^ 40 * 260080 * 2
def baseEnd_260080 : Nat := 89030699080965113002613

theorem tailTrace_260080 : CollatzResearch.WordTrace tailWord_260080 prefixEnd_260080 89030699080965113002613 := by
  unfold tailWord_260080
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742948448891026486400847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6323931265188035315201129 4742948448891026486400847)
  ·
    refine ⟨7114422673336539729601271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4742948448891026486400847 7114422673336539729601271)
    ·
      refine ⟨10671634010004809594401907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7114422673336539729601271 10671634010004809594401907)
      ·
        refine ⟨16007451015007214391602861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10671634010004809594401907 16007451015007214391602861)
        ·
          refine ⟨6002794130627705396851073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16007451015007214391602861 6002794130627705396851073)
          ·
            refine ⟨4502095597970779047638305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6002794130627705396851073 4502095597970779047638305)
            ·
              refine ⟨3376571698478084285728729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4502095597970779047638305 3376571698478084285728729)
              ·
                refine ⟨2532428773858563214296547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3376571698478084285728729 2532428773858563214296547)
                ·
                  refine ⟨3798643160787844821444821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532428773858563214296547 3798643160787844821444821)
                  ·
                    refine ⟨89030699080965113002613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3798643160787844821444821 89030699080965113002613)
                    ·
                      rfl

theorem cell22_260080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_260080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260080 prefixEnd_260080 := by exact prefixLift 260080
  have htrace : WordTrace (prefixWord ++ tailWord_260080) baseStart_260080 baseEnd_260080 := by
    simpa [prefixWord, tailWord_260080, baseEnd_260080] using wordTrace_append hprefix tailTrace_260080
  have hstable : (prefixWord ++ tailWord_260080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260080).length < 2 ^ (prefixWord ++ tailWord_260080).sum := by decide
  have hdescent : baseEnd_260080 < baseStart_260080 := by decide
  rcases family_descends (prefixWord ++ tailWord_260080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260103 : List Nat := [1, 1, 4, 3, 1, 3, 3, 2, 1, 3]
def baseStart_260103 : Nat := 118140960795 + 260103 * 2 ^ 59
def prefixEnd_260103 : Nat := 4983230072969 + 3 ^ 40 * 260103 * 2
def baseEnd_260103 : Nat := 89038572451000719677543

theorem tailTrace_260103 : CollatzResearch.WordTrace tailWord_260103 prefixEnd_260103 89038572451000719677543 := by
  unfold tailWord_260103
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486735776698727900888963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6324490517799151933925975 9486735776698727900888963)
  ·
    refine ⟨14230103665048091851333445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9486735776698727900888963 14230103665048091851333445)
    ·
      refine ⟨2668144437196517222125021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14230103665048091851333445 2668144437196517222125021)
      ·
        refine ⟨1000554163948693958296883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2668144437196517222125021 1000554163948693958296883)
        ·
          refine ⟨1500831245923040937445325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000554163948693958296883 1500831245923040937445325)
          ·
            refine ⟨562811717221140351541997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1500831245923040937445325 562811717221140351541997)
            ·
              refine ⟨211054393957927631828249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562811717221140351541997 211054393957927631828249)
              ·
                refine ⟨158290795468445723871187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211054393957927631828249 158290795468445723871187)
                ·
                  refine ⟨237436193202668585806781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158290795468445723871187 237436193202668585806781)
                  ·
                    refine ⟨89038572451000719677543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237436193202668585806781 89038572451000719677543)
                    ·
                      rfl

theorem cell22_260103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_260103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260103 prefixEnd_260103 := by exact prefixLift 260103
  have htrace : WordTrace (prefixWord ++ tailWord_260103) baseStart_260103 baseEnd_260103 := by
    simpa [prefixWord, tailWord_260103, baseEnd_260103] using wordTrace_append hprefix tailTrace_260103
  have hstable : (prefixWord ++ tailWord_260103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260103).length < 2 ^ (prefixWord ++ tailWord_260103).sum := by decide
  have hdescent : baseEnd_260103 < baseStart_260103 := by decide
  rcases family_descends (prefixWord ++ tailWord_260103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260109 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_260109 : Nat := 118140960795 + 260109 * 2 ^ 59
def prefixEnd_260109 : Nat := 4983230072969 + 3 ^ 40 * 260109 * 2
def baseEnd_260109 : Nat := 89040626373618704027525

theorem tailTrace_260109 : CollatzResearch.WordTrace tailWord_260109 prefixEnd_260109 89040626373618704027525 := by
  unfold tailWord_260109
  simp only [CollatzResearch.WordTrace]
  refine ⟨9486954614676990925607381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6324636409784660617071587 9486954614676990925607381)
  ·
    refine ⟨222350498781491974818923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9486954614676990925607381 222350498781491974818923)
    ·
      refine ⟨333525748172237962228385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222350498781491974818923 333525748172237962228385)
      ·
        refine ⟨250144311129178471671289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333525748172237962228385 250144311129178471671289)
        ·
          refine ⟨187608233346883853753467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250144311129178471671289 187608233346883853753467)
          ·
            refine ⟨281412350020325780630201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187608233346883853753467 281412350020325780630201)
            ·
              refine ⟨211059262515244335472651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281412350020325780630201 211059262515244335472651)
              ·
                refine ⟨316588893772866503208977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211059262515244335472651 316588893772866503208977)
                ·
                  refine ⟨237441670329649877406733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316588893772866503208977 237441670329649877406733)
                  ·
                    refine ⟨89040626373618704027525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237441670329649877406733 89040626373618704027525)
                    ·
                      rfl

theorem cell22_260109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_260109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260109 prefixEnd_260109 := by exact prefixLift 260109
  have htrace : WordTrace (prefixWord ++ tailWord_260109) baseStart_260109 baseEnd_260109 := by
    simpa [prefixWord, tailWord_260109, baseEnd_260109] using wordTrace_append hprefix tailTrace_260109
  have hstable : (prefixWord ++ tailWord_260109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260109).length < 2 ^ (prefixWord ++ tailWord_260109).sum := by decide
  have hdescent : baseEnd_260109 < baseStart_260109 := by decide
  rcases family_descends (prefixWord ++ tailWord_260109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260129 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_260129 : Nat := 118140960795 + 260129 * 2 ^ 59
def prefixEnd_260129 : Nat := 4983230072969 + 3 ^ 40 * 260129 * 2
def baseEnd_260129 : Nat := 89047472782345318527463

theorem tailTrace_260129 : CollatzResearch.WordTrace tailWord_260129 prefixEnd_260129 89047472782345318527463 := by
  unfold tailWord_260129
  simp only [CollatzResearch.WordTrace]
  refine ⟨9487684074604534341335441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6325122716403022894223627 9487684074604534341335441)
  ·
    refine ⟨7115763055953400756001581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9487684074604534341335441 7115763055953400756001581)
    ·
      refine ⟨2668411145982525283500593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7115763055953400756001581 2668411145982525283500593)
      ·
        refine ⟨2001308359486893962625445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2668411145982525283500593 2001308359486893962625445)
        ·
          refine ⟨375245317403792617992271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2001308359486893962625445 375245317403792617992271)
          ·
            refine ⟨562867976105688926988407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375245317403792617992271 562867976105688926988407)
            ·
              refine ⟨844301964158533390482611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562867976105688926988407 844301964158533390482611)
              ·
                refine ⟨1266452946237800085723917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844301964158533390482611 1266452946237800085723917)
                ·
                  refine ⟨474919854839175032146469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266452946237800085723917 474919854839175032146469)
                  ·
                    refine ⟨89047472782345318527463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474919854839175032146469 89047472782345318527463)
                    ·
                      rfl

theorem cell22_260129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_260129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260129 prefixEnd_260129 := by exact prefixLift 260129
  have htrace : WordTrace (prefixWord ++ tailWord_260129) baseStart_260129 baseEnd_260129 := by
    simpa [prefixWord, tailWord_260129, baseEnd_260129] using wordTrace_append hprefix tailTrace_260129
  have hstable : (prefixWord ++ tailWord_260129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260129).length < 2 ^ (prefixWord ++ tailWord_260129).sum := by decide
  have hdescent : baseEnd_260129 < baseStart_260129 := by decide
  rcases family_descends (prefixWord ++ tailWord_260129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260146 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_260146 : Nat := 118140960795 + 260146 * 2 ^ 59
def prefixEnd_260146 : Nat := 4983230072969 + 3 ^ 40 * 260146 * 2
def baseEnd_260146 : Nat := 89053292229762940852411

theorem tailTrace_260146 : CollatzResearch.WordTrace tailWord_260146 prefixEnd_260146 89053292229762940852411 := by
  unfold tailWord_260146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372076028885736561176073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6325536077028630829802861 2372076028885736561176073)
  ·
    refine ⟨1779057021664302420882055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2372076028885736561176073 1779057021664302420882055)
    ·
      refine ⟨2668585532496453631323083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1779057021664302420882055 2668585532496453631323083)
      ·
        refine ⟨4002878298744680446984625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668585532496453631323083 4002878298744680446984625)
        ·
          refine ⟨3002158724058510335238469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4002878298744680446984625 3002158724058510335238469)
          ·
            refine ⟨562904760760970687857213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3002158724058510335238469 562904760760970687857213)
            ·
              refine ⟨211089285285364007946455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562904760760970687857213 211089285285364007946455)
              ·
                refine ⟨316633927928046011919683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211089285285364007946455 316633927928046011919683)
                ·
                  refine ⟨474950891892069017879525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316633927928046011919683 474950891892069017879525)
                  ·
                    refine ⟨89053292229762940852411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474950891892069017879525 89053292229762940852411)
                    ·
                      rfl

theorem cell22_260146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_260146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260146 prefixEnd_260146 := by exact prefixLift 260146
  have htrace : WordTrace (prefixWord ++ tailWord_260146) baseStart_260146 baseEnd_260146 := by
    simpa [prefixWord, tailWord_260146, baseEnd_260146] using wordTrace_append hprefix tailTrace_260146
  have hstable : (prefixWord ++ tailWord_260146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260146).length < 2 ^ (prefixWord ++ tailWord_260146).sum := by decide
  have hdescent : baseEnd_260146 < baseStart_260146 := by decide
  rcases family_descends (prefixWord ++ tailWord_260146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260159 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 2, 3]
def baseStart_260159 : Nat := 118140960795 + 260159 * 2 ^ 59
def prefixEnd_260159 : Nat := 4983230072969 + 3 ^ 40 * 260159 * 2
def baseEnd_260159 : Nat := 89057742395435240277371

theorem tailTrace_260159 : CollatzResearch.WordTrace tailWord_260159 prefixEnd_260159 89057742395435240277371 := by
  unfold tailWord_260159
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488778264495849464927531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6325852176330566309951687 9488778264495849464927531)
  ·
    refine ⟨14233167396743774197391297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9488778264495849464927531 14233167396743774197391297)
    ·
      refine ⟨10674875547557830648043473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14233167396743774197391297 10674875547557830648043473)
      ·
        refine ⟨8006156660668372986032605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10674875547557830648043473 8006156660668372986032605)
        ·
          refine ⟨3002308747750639869762227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8006156660668372986032605 3002308747750639869762227)
          ·
            refine ⟨4503463121625959804643341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002308747750639869762227 4503463121625959804643341)
            ·
              refine ⟨1688798670609734926741253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4503463121625959804643341 1688798670609734926741253)
              ·
                refine ⟨316649750739325298763985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1688798670609734926741253 316649750739325298763985)
                ·
                  refine ⟨237487313054493974072989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316649750739325298763985 237487313054493974072989)
                  ·
                    refine ⟨89057742395435240277371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237487313054493974072989 89057742395435240277371)
                    ·
                      rfl

theorem cell22_260159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_260159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260159 prefixEnd_260159 := by exact prefixLift 260159
  have htrace : WordTrace (prefixWord ++ tailWord_260159) baseStart_260159 baseEnd_260159 := by
    simpa [prefixWord, tailWord_260159, baseEnd_260159] using wordTrace_append hprefix tailTrace_260159
  have hstable : (prefixWord ++ tailWord_260159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260159).length < 2 ^ (prefixWord ++ tailWord_260159).sum := by decide
  have hdescent : baseEnd_260159 < baseStart_260159 := by decide
  rcases family_descends (prefixWord ++ tailWord_260159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260161 : List Nat := [1, 2, 5, 1, 2, 2, 1, 4, 4]
def baseStart_260161 : Nat := 118140960795 + 260161 * 2 ^ 59
def prefixEnd_260161 : Nat := 4983230072969 + 3 ^ 40 * 260161 * 2
def baseEnd_260161 : Nat := 29686142345435967242455

theorem tailTrace_260161 : CollatzResearch.WordTrace tailWord_260161 prefixEnd_260161 29686142345435967242455 := by
  unfold tailWord_260161
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488851210488603806500337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6325900806992402537666891 9488851210488603806500337)
  ·
    refine ⟨7116638407866452854875253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9488851210488603806500337 7116638407866452854875253)
    ·
      refine ⟨667184850737479955144555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7116638407866452854875253 667184850737479955144555)
      ·
        refine ⟨1000777276106219932716833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667184850737479955144555 1000777276106219932716833)
        ·
          refine ⟨750582957079664949537625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000777276106219932716833 750582957079664949537625)
          ·
            refine ⟨562937217809748712153219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750582957079664949537625 562937217809748712153219)
            ·
              refine ⟨844405826714623068229829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562937217809748712153219 844405826714623068229829)
              ·
                refine ⟨158326092508991825293093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844405826714623068229829 158326092508991825293093)
                ·
                  refine ⟨29686142345435967242455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158326092508991825293093 29686142345435967242455)
                  ·
                    rfl

theorem cell22_260161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 4].length) (baseStart_260161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260161 prefixEnd_260161 := by exact prefixLift 260161
  have htrace : WordTrace (prefixWord ++ tailWord_260161) baseStart_260161 baseEnd_260161 := by
    simpa [prefixWord, tailWord_260161, baseEnd_260161] using wordTrace_append hprefix tailTrace_260161
  have hstable : (prefixWord ++ tailWord_260161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260161).length < 2 ^ (prefixWord ++ tailWord_260161).sum := by decide
  have hdescent : baseEnd_260161 < baseStart_260161 := by decide
  rcases family_descends (prefixWord ++ tailWord_260161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260172 : List Nat := [2, 2, 1, 3, 1, 1, 5, 7]
def baseStart_260172 : Nat := 118140960795 + 260172 * 2 ^ 59
def prefixEnd_260172 : Nat := 4983230072969 + 3 ^ 40 * 260172 * 2
def baseEnd_260172 : Nat := 9895799173456393300259

theorem tailTrace_260172 : CollatzResearch.WordTrace tailWord_260172 prefixEnd_260172 9895799173456393300259 := by
  unfold tailWord_260172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744626206724376342575385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6326168275632501790100513 4744626206724376342575385)
  ·
    refine ⟨3558469655043282256931539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4744626206724376342575385 3558469655043282256931539)
    ·
      refine ⟨5337704482564923385397309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3558469655043282256931539 5337704482564923385397309)
      ·
        refine ⟨2001639180961846269523991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5337704482564923385397309 2001639180961846269523991)
        ·
          refine ⟨3002458771442769404285987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001639180961846269523991 3002458771442769404285987)
          ·
            refine ⟨4503688157164154106428981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002458771442769404285987 4503688157164154106428981)
            ·
              refine ⟨422220764734139447477717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4503688157164154106428981 422220764734139447477717)
              ·
                refine ⟨9895799173456393300259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 422220764734139447477717 9895799173456393300259)
                ·
                  rfl

theorem cell22_260172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 7].length) (baseStart_260172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260172 prefixEnd_260172 := by exact prefixLift 260172
  have htrace : WordTrace (prefixWord ++ tailWord_260172) baseStart_260172 baseEnd_260172 := by
    simpa [prefixWord, tailWord_260172, baseEnd_260172] using wordTrace_append hprefix tailTrace_260172
  have hstable : (prefixWord ++ tailWord_260172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260172).length < 2 ^ (prefixWord ++ tailWord_260172).sum := by decide
  have hdescent : baseEnd_260172 < baseStart_260172 := by decide
  rcases family_descends (prefixWord ++ tailWord_260172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260221 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_260221 : Nat := 118140960795 + 260221 * 2 ^ 59
def prefixEnd_260221 : Nat := 4983230072969 + 3 ^ 40 * 260221 * 2
def baseEnd_260221 : Nat := 89078966262487745227181

theorem tailTrace_260221 : CollatzResearch.WordTrace tailWord_260221 prefixEnd_260221 89078966262487745227181 := by
  unfold tailWord_260221
  simp only [CollatzResearch.WordTrace]
  refine ⟨9491039590271234053684517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6327359726847489369123011 9491039590271234053684517)
  ·
    refine ⟨1779569923175856385065847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9491039590271234053684517 1779569923175856385065847)
    ·
      refine ⟨2669354884763784577598771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1779569923175856385065847 2669354884763784577598771)
      ·
        refine ⟨4004032327145676866398157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669354884763784577598771 4004032327145676866398157)
        ·
          refine ⟨1501512122679628824899309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4004032327145676866398157 1501512122679628824899309)
          ·
            refine ⟨563067046004860809337241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1501512122679628824899309 563067046004860809337241)
            ·
              refine ⟨422300284503645607002931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563067046004860809337241 422300284503645607002931)
              ·
                refine ⟨633450426755468410504397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422300284503645607002931 633450426755468410504397)
                ·
                  refine ⟨237543910033300653939149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633450426755468410504397 237543910033300653939149)
                  ·
                    refine ⟨89078966262487745227181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237543910033300653939149 89078966262487745227181)
                    ·
                      rfl

theorem cell22_260221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_260221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260221 prefixEnd_260221 := by exact prefixLift 260221
  have htrace : WordTrace (prefixWord ++ tailWord_260221) baseStart_260221 baseEnd_260221 := by
    simpa [prefixWord, tailWord_260221, baseEnd_260221] using wordTrace_append hprefix tailTrace_260221
  have hstable : (prefixWord ++ tailWord_260221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260221).length < 2 ^ (prefixWord ++ tailWord_260221).sum := by decide
  have hdescent : baseEnd_260221 < baseStart_260221 := by decide
  rcases family_descends (prefixWord ++ tailWord_260221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260246 : List Nat := [5, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_260246 : Nat := 118140960795 + 260246 * 2 ^ 59
def prefixEnd_260246 : Nat := 4983230072969 + 3 ^ 40 * 260246 * 2
def baseEnd_260246 : Nat := 29695841424465337784035

theorem tailTrace_260246 : CollatzResearch.WordTrace tailWord_260246 prefixEnd_260246 29695841424465337784035 := by
  unfold tailWord_260246
  simp only [CollatzResearch.WordTrace]
  refine ⟨593246963448791457709037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6327967610120442215563061 593246963448791457709037)
  ·
    refine ⟨222467611293296796640889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 593246963448791457709037 222467611293296796640889)
    ·
      refine ⟨166850708469972597480667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222467611293296796640889 166850708469972597480667)
      ·
        refine ⟨250276062704958896221001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166850708469972597480667 250276062704958896221001)
        ·
          refine ⟨187707047028719172165751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250276062704958896221001 187707047028719172165751)
          ·
            refine ⟨281560570543078758248627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187707047028719172165751 281560570543078758248627)
            ·
              refine ⟨422340855814618137372941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281560570543078758248627 422340855814618137372941)
              ·
                refine ⟨158377820930481801514853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422340855814618137372941 158377820930481801514853)
                ·
                  refine ⟨29695841424465337784035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158377820930481801514853 29695841424465337784035)
                  ·
                    rfl

theorem cell22_260246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_260246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260246 prefixEnd_260246 := by exact prefixLift 260246
  have htrace : WordTrace (prefixWord ++ tailWord_260246) baseStart_260246 baseEnd_260246 := by
    simpa [prefixWord, tailWord_260246, baseEnd_260246] using wordTrace_append hprefix tailTrace_260246
  have hstable : (prefixWord ++ tailWord_260246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260246).length < 2 ^ (prefixWord ++ tailWord_260246).sum := by decide
  have hdescent : baseEnd_260246 < baseStart_260246 := by decide
  rcases family_descends (prefixWord ++ tailWord_260246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260255 : List Nat := [1, 1, 2, 6, 1, 3, 1, 3, 1, 3]
def baseStart_260255 : Nat := 118140960795 + 260255 * 2 ^ 59
def prefixEnd_260255 : Nat := 4983230072969 + 3 ^ 40 * 260255 * 2
def baseEnd_260255 : Nat := 89090605157322989877077

theorem tailTrace_260255 : CollatzResearch.WordTrace tailWord_260255 prefixEnd_260255 89090605157322989877077 := by
  unfold tailWord_260255
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492279672148057860422219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6328186448098705240281479 9492279672148057860422219)
  ·
    refine ⟨14238419508222086790633329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9492279672148057860422219 14238419508222086790633329)
    ·
      refine ⟨10678814631166565092974997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14238419508222086790633329 10678814631166565092974997)
      ·
        refine ⟨500569435835932738733203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10678814631166565092974997 500569435835932738733203)
        ·
          refine ⟨750854153753899108099805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500569435835932738733203 750854153753899108099805)
          ·
            refine ⟨281570307657712165537427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750854153753899108099805 281570307657712165537427)
            ·
              refine ⟨422355461486568248306141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281570307657712165537427 422355461486568248306141)
              ·
                refine ⟨158383298057463093114803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422355461486568248306141 158383298057463093114803)
                ·
                  refine ⟨237574947086194639672205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158383298057463093114803 237574947086194639672205)
                  ·
                    refine ⟨89090605157322989877077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237574947086194639672205 89090605157322989877077)
                    ·
                      rfl

theorem cell22_260255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 3].length) (baseStart_260255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260255 prefixEnd_260255 := by exact prefixLift 260255
  have htrace : WordTrace (prefixWord ++ tailWord_260255) baseStart_260255 baseEnd_260255 := by
    simpa [prefixWord, tailWord_260255, baseEnd_260255] using wordTrace_append hprefix tailTrace_260255
  have hstable : (prefixWord ++ tailWord_260255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260255).length < 2 ^ (prefixWord ++ tailWord_260255).sum := by decide
  have hdescent : baseEnd_260255 < baseStart_260255 := by decide
  rcases family_descends (prefixWord ++ tailWord_260255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260279 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 6]
def baseStart_260279 : Nat := 118140960795 + 260279 * 2 ^ 59
def prefixEnd_260279 : Nat := 4983230072969 + 3 ^ 40 * 260279 * 2
def baseEnd_260279 : Nat := 29699606949264975759001

theorem tailTrace_260279 : CollatzResearch.WordTrace tailWord_260279 prefixEnd_260279 29699606949264975759001 := by
  unfold tailWord_260279
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493155024061109959295891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6328770016040739972863927 9493155024061109959295891)
  ·
    refine ⟨14239732536091664938943837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9493155024061109959295891 14239732536091664938943837)
    ·
      refine ⟨5339899701034374352103939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14239732536091664938943837 5339899701034374352103939)
      ·
        refine ⟨8009849551551561528155909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339899701034374352103939 8009849551551561528155909)
        ·
          refine ⟨1501846790915917786529233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8009849551551561528155909 1501846790915917786529233)
          ·
            refine ⟨1126385093186938339896925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501846790915917786529233 1126385093186938339896925)
            ·
              refine ⟨422394409945101877461347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126385093186938339896925 422394409945101877461347)
              ·
                refine ⟨633591614917652816192021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422394409945101877461347 633591614917652816192021)
                ·
                  refine ⟨29699606949264975759001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 633591614917652816192021 29699606949264975759001)
                  ·
                    rfl

theorem cell22_260279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 6].length) (baseStart_260279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260279 prefixEnd_260279 := by exact prefixLift 260279
  have htrace : WordTrace (prefixWord ++ tailWord_260279) baseStart_260279 baseEnd_260279 := by
    simpa [prefixWord, tailWord_260279, baseEnd_260279] using wordTrace_append hprefix tailTrace_260279
  have hstable : (prefixWord ++ tailWord_260279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260279).length < 2 ^ (prefixWord ++ tailWord_260279).sum := by decide
  have hdescent : baseEnd_260279 < baseStart_260279 := by decide
  rcases family_descends (prefixWord ++ tailWord_260279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260328 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 2, 3]
def baseStart_260328 : Nat := 118140960795 + 260328 * 2 ^ 59
def prefixEnd_260328 : Nat := 4983230072969 + 3 ^ 40 * 260328 * 2
def baseEnd_260328 : Nat := 89115594549175132801853

theorem tailTrace_260328 : CollatzResearch.WordTrace tailWord_260328 prefixEnd_260328 89115594549175132801853 := by
  unfold tailWord_260328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4747471100441795663914819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6329961467255727551886425 4747471100441795663914819)
  ·
    refine ⟨7121206650662693495872229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4747471100441795663914819 7121206650662693495872229)
    ·
      refine ⟨1335226246999255030476043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7121206650662693495872229 1335226246999255030476043)
      ·
        refine ⟨2002839370498882545714065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335226246999255030476043 2002839370498882545714065)
        ·
          refine ⟨1502129527874161909285549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2002839370498882545714065 1502129527874161909285549)
          ·
            refine ⟨563298572952810715982081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1502129527874161909285549 563298572952810715982081)
            ·
              refine ⟨422473929714608036986561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563298572952810715982081 422473929714608036986561)
              ·
                refine ⟨316855447285956027739921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422473929714608036986561 316855447285956027739921)
                ·
                  refine ⟨237641585464467020804941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316855447285956027739921 237641585464467020804941)
                  ·
                    refine ⟨89115594549175132801853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237641585464467020804941 89115594549175132801853)
                    ·
                      rfl

theorem cell22_260328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_260328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260328 prefixEnd_260328 := by exact prefixLift 260328
  have htrace : WordTrace (prefixWord ++ tailWord_260328) baseStart_260328 baseEnd_260328 := by
    simpa [prefixWord, tailWord_260328, baseEnd_260328] using wordTrace_append hprefix tailTrace_260328
  have hstable : (prefixWord ++ tailWord_260328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260328).length < 2 ^ (prefixWord ++ tailWord_260328).sum := by decide
  have hdescent : baseEnd_260328 < baseStart_260328 := by decide
  rcases family_descends (prefixWord ++ tailWord_260328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260373 : List Nat := [1, 3, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_260373 : Nat := 118140960795 + 260373 * 2 ^ 59
def prefixEnd_260373 : Nat := 4983230072969 + 3 ^ 40 * 260373 * 2
def baseEnd_260373 : Nat := 89130998968810015426715

theorem tailTrace_260373 : CollatzResearch.WordTrace tailWord_260373 prefixEnd_260373 89130998968810015426715 := by
  unfold tailWord_260373
  simp only [CollatzResearch.WordTrace]
  refine ⟨9496583485720564013217773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6331055657147042675478515 9496583485720564013217773)
  ·
    refine ⟨3561218807145211504956665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9496583485720564013217773 3561218807145211504956665)
    ·
      refine ⟨2670914105358908628717499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3561218807145211504956665 2670914105358908628717499)
      ·
        refine ⟨4006371158038362943076249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670914105358908628717499 4006371158038362943076249)
        ·
          refine ⟨3004778368528772207307187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4006371158038362943076249 3004778368528772207307187)
          ·
            refine ⟨4507167552793158310960781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004778368528772207307187 4507167552793158310960781)
            ·
              refine ⟨1690187832297434366610293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4507167552793158310960781 1690187832297434366610293)
              ·
                refine ⟨158455109277884471869715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1690187832297434366610293 158455109277884471869715)
                ·
                  refine ⟨237682663916826707804573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158455109277884471869715 237682663916826707804573)
                  ·
                    refine ⟨89130998968810015426715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237682663916826707804573 89130998968810015426715)
                    ·
                      rfl

theorem cell22_260373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_260373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260373 prefixEnd_260373 := by exact prefixLift 260373
  have htrace : WordTrace (prefixWord ++ tailWord_260373) baseStart_260373 baseEnd_260373 := by
    simpa [prefixWord, tailWord_260373, baseEnd_260373] using wordTrace_append hprefix tailTrace_260373
  have hstable : (prefixWord ++ tailWord_260373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260373).length < 2 ^ (prefixWord ++ tailWord_260373).sum := by decide
  have hdescent : baseEnd_260373 < baseStart_260373 := by decide
  rcases family_descends (prefixWord ++ tailWord_260373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260386 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_260386 : Nat := 118140960795 + 260386 * 2 ^ 59
def prefixEnd_260386 : Nat := 4983230072969 + 3 ^ 40 * 260386 * 2
def baseEnd_260386 : Nat := 29711816378160771617225

theorem tailTrace_260386 : CollatzResearch.WordTrace tailWord_260386 prefixEnd_260386 29711816378160771617225 := by
  unfold tailWord_260386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374264408668366808360253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6331371756448978155627341 2374264408668366808360253)
  ·
    refine ⟨890349153250637553135095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2374264408668366808360253 890349153250637553135095)
    ·
      refine ⟨1335523729875956329702643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890349153250637553135095 1335523729875956329702643)
      ·
        refine ⟨2003285594813934494553965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335523729875956329702643 2003285594813934494553965)
        ·
          refine ⟨751232098055225435457737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2003285594813934494553965 751232098055225435457737)
          ·
            refine ⟨563424073541419076593303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751232098055225435457737 563424073541419076593303)
            ·
              refine ⟨845136110312128614889955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563424073541419076593303 845136110312128614889955)
              ·
                refine ⟨1267704165468192922334933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845136110312128614889955 1267704165468192922334933)
                ·
                  refine ⟨29711816378160771617225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1267704165468192922334933 29711816378160771617225)
                  ·
                    rfl

theorem cell22_260386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_260386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260386 prefixEnd_260386 := by exact prefixLift 260386
  have htrace : WordTrace (prefixWord ++ tailWord_260386) baseStart_260386 baseEnd_260386 := by
    simpa [prefixWord, tailWord_260386, baseEnd_260386] using wordTrace_append hprefix tailTrace_260386
  have hstable : (prefixWord ++ tailWord_260386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260386).length < 2 ^ (prefixWord ++ tailWord_260386).sum := by decide
  have hdescent : baseEnd_260386 < baseStart_260386 := by decide
  rcases family_descends (prefixWord ++ tailWord_260386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260399 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 5, 4]
def baseStart_260399 : Nat := 118140960795 + 260399 * 2 ^ 59
def prefixEnd_260399 : Nat := 4983230072969 + 3 ^ 40 * 260399 * 2
def baseEnd_260399 : Nat := 89139899300154614276635

theorem tailTrace_260399 : CollatzResearch.WordTrace tailWord_260399 prefixEnd_260399 89139899300154614276635 := by
  unfold tailWord_260399
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497531783626370453664251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6331687855750913635776167 9497531783626370453664251)
  ·
    refine ⟨14246297675439555680496377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9497531783626370453664251 14246297675439555680496377)
    ·
      refine ⟨10684723256579666760372283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14246297675439555680496377 10684723256579666760372283)
      ·
        refine ⟨16027084884869500140558425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10684723256579666760372283 16027084884869500140558425)
        ·
          refine ⟨12020313663652125105418819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16027084884869500140558425 12020313663652125105418819)
          ·
            refine ⟨18030470495478187658128229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020313663652125105418819 18030470495478187658128229)
            ·
              refine ⟨3380713217902160185899043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18030470495478187658128229 3380713217902160185899043)
              ·
                refine ⟨5071069826853240278848565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380713217902160185899043 5071069826853240278848565)
                ·
                  refine ⟨475412796267491276142053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5071069826853240278848565 475412796267491276142053)
                  ·
                    refine ⟨89139899300154614276635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475412796267491276142053 89139899300154614276635)
                    ·
                      rfl

theorem cell22_260399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_260399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260399 prefixEnd_260399 := by exact prefixLift 260399
  have htrace : WordTrace (prefixWord ++ tailWord_260399) baseStart_260399 baseEnd_260399 := by
    simpa [prefixWord, tailWord_260399, baseEnd_260399] using wordTrace_append hprefix tailTrace_260399
  have hstable : (prefixWord ++ tailWord_260399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260399).length < 2 ^ (prefixWord ++ tailWord_260399).sum := by decide
  have hdescent : baseEnd_260399 < baseStart_260399 := by decide
  rcases family_descends (prefixWord ++ tailWord_260399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260431 : List Nat := [1, 1, 2, 1, 1, 2, 1, 9, 4]
def baseStart_260431 : Nat := 118140960795 + 260431 * 2 ^ 59
def prefixEnd_260431 : Nat := 4983230072969 + 3 ^ 40 * 260431 * 2
def baseEnd_260431 : Nat := 29716951184705732492179

theorem tailTrace_260431 : CollatzResearch.WordTrace tailWord_260431 prefixEnd_260431 29716951184705732492179 := by
  unfold tailWord_260431
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498698919510439918829147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6332465946340293279219431 9498698919510439918829147)
  ·
    refine ⟨14248048379265659878243721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9498698919510439918829147 14248048379265659878243721)
    ·
      refine ⟨10686036284449244908682791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14248048379265659878243721 10686036284449244908682791)
      ·
        refine ⟨16029054426673867363024187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686036284449244908682791 16029054426673867363024187)
        ·
          refine ⟨24043581640010801044536281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16029054426673867363024187 24043581640010801044536281)
          ·
            refine ⟨18032686230008100783402211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24043581640010801044536281 18032686230008100783402211)
            ·
              refine ⟨27049029345012151175103317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18032686230008100783402211 27049029345012151175103317)
              ·
                refine ⟨158490406318430573291621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27049029345012151175103317 158490406318430573291621)
                ·
                  refine ⟨29716951184705732492179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158490406318430573291621 29716951184705732492179)
                  ·
                    rfl

theorem cell22_260431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 4].length) (baseStart_260431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260431 prefixEnd_260431 := by exact prefixLift 260431
  have htrace : WordTrace (prefixWord ++ tailWord_260431) baseStart_260431 baseEnd_260431 := by
    simpa [prefixWord, tailWord_260431, baseEnd_260431] using wordTrace_append hprefix tailTrace_260431
  have hstable : (prefixWord ++ tailWord_260431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260431).length < 2 ^ (prefixWord ++ tailWord_260431).sum := by decide
  have hdescent : baseEnd_260431 < baseStart_260431 := by decide
  rcases family_descends (prefixWord ++ tailWord_260431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260448 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 6]
def baseStart_260448 : Nat := 118140960795 + 260448 * 2 ^ 59
def prefixEnd_260448 : Nat := 4983230072969 + 3 ^ 40 * 260448 * 2
def baseEnd_260448 : Nat := 29718891000511606600495

theorem tailTrace_260448 : CollatzResearch.WordTrace tailWord_260448 prefixEnd_260448 29718891000511606600495 := by
  unfold tailWord_260448
  simp only [CollatzResearch.WordTrace]
  refine ⟨4749659480224425911098999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6332879306965901214798665 4749659480224425911098999)
  ·
    refine ⟨7124489220336638866648499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4749659480224425911098999 7124489220336638866648499)
    ·
      refine ⟨10686733830504958299972749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124489220336638866648499 10686733830504958299972749)
      ·
        refine ⟨4007525186439359362489781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10686733830504958299972749 4007525186439359362489781)
        ·
          refine ⟨375705486228689940233417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4007525186439359362489781 375705486228689940233417)
          ·
            refine ⟨281779114671517455175063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375705486228689940233417 281779114671517455175063)
            ·
              refine ⟨422668672007276182762595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281779114671517455175063 422668672007276182762595)
              ·
                refine ⟨634003008010914274143893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422668672007276182762595 634003008010914274143893)
                ·
                  refine ⟨29718891000511606600495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 634003008010914274143893 29718891000511606600495)
                  ·
                    rfl

theorem cell22_260448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_260448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260448 prefixEnd_260448 := by exact prefixLift 260448
  have htrace : WordTrace (prefixWord ++ tailWord_260448) baseStart_260448 baseEnd_260448 := by
    simpa [prefixWord, tailWord_260448, baseEnd_260448] using wordTrace_append hprefix tailTrace_260448
  have hstable : (prefixWord ++ tailWord_260448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260448).length < 2 ^ (prefixWord ++ tailWord_260448).sum := by decide
  have hdescent : baseEnd_260448 < baseStart_260448 := by decide
  rcases family_descends (prefixWord ++ tailWord_260448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260461 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_260461 : Nat := 118140960795 + 260461 * 2 ^ 59
def prefixEnd_260461 : Nat := 4983230072969 + 3 ^ 40 * 260461 * 2
def baseEnd_260461 : Nat := 89161123167207119226445

theorem tailTrace_260461 : CollatzResearch.WordTrace tailWord_260461 prefixEnd_260461 89161123167207119226445 := by
  unfold tailWord_260461
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499793109401755042421237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6333195406267836694947491 9499793109401755042421237)
  ·
    refine ⟨890605604006414535226991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9499793109401755042421237 890605604006414535226991)
    ·
      refine ⟨1335908406009621802840487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890605604006414535226991 1335908406009621802840487)
      ·
        refine ⟨2003862609014432704260731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335908406009621802840487 2003862609014432704260731)
        ·
          refine ⟨3005793913521649056391097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003862609014432704260731 3005793913521649056391097)
          ·
            refine ⟨2254345435141236792293323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3005793913521649056391097 2254345435141236792293323)
            ·
              refine ⟨3381518152711855188439985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254345435141236792293323 3381518152711855188439985)
              ·
                refine ⟨2536138614533891391329989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381518152711855188439985 2536138614533891391329989)
                ·
                  refine ⟨475525990225104635874373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536138614533891391329989 475525990225104635874373)
                  ·
                    refine ⟨89161123167207119226445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 475525990225104635874373 89161123167207119226445)
                    ·
                      rfl

theorem cell22_260461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_260461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260461 prefixEnd_260461 := by exact prefixLift 260461
  have htrace : WordTrace (prefixWord ++ tailWord_260461) baseStart_260461 baseEnd_260461 := by
    simpa [prefixWord, tailWord_260461, baseEnd_260461] using wordTrace_append hprefix tailTrace_260461
  have hstable : (prefixWord ++ tailWord_260461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260461).length < 2 ^ (prefixWord ++ tailWord_260461).sum := by decide
  have hdescent : baseEnd_260461 < baseStart_260461 := by decide
  rcases family_descends (prefixWord ++ tailWord_260461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260506 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_260506 : Nat := 118140960795 + 260506 * 2 ^ 59
def prefixEnd_260506 : Nat := 4983230072969 + 3 ^ 40 * 260506 * 2
def baseEnd_260506 : Nat := 89176527586842001851307

theorem tailTrace_260506 : CollatzResearch.WordTrace tailWord_260506 prefixEnd_260506 89176527586842001851307 := by
  unfold tailWord_260506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375358598559681931952343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6334289596159151818539581 2375358598559681931952343)
  ·
    refine ⟨3563037897839522897928515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2375358598559681931952343 3563037897839522897928515)
    ·
      refine ⟨5344556846759284346892773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3563037897839522897928515 5344556846759284346892773)
      ·
        refine ⟨1002104408767365815042395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5344556846759284346892773 1002104408767365815042395)
        ·
          refine ⟨1503156613151048722563593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002104408767365815042395 1503156613151048722563593)
          ·
            refine ⟨1127367459863286541922695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503156613151048722563593 1127367459863286541922695)
            ·
              refine ⟨1691051189794929812884043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127367459863286541922695 1691051189794929812884043)
              ·
                refine ⟨2536576784692394719326065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691051189794929812884043 2536576784692394719326065)
                ·
                  refine ⟨1902432588519296039494549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2536576784692394719326065 1902432588519296039494549)
                  ·
                    refine ⟨89176527586842001851307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1902432588519296039494549 89176527586842001851307)
                    ·
                      rfl

theorem cell22_260506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_260506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260506 prefixEnd_260506 := by exact prefixLift 260506
  have htrace : WordTrace (prefixWord ++ tailWord_260506) baseStart_260506 baseEnd_260506 := by
    simpa [prefixWord, tailWord_260506, baseEnd_260506] using wordTrace_append hprefix tailTrace_260506
  have hstable : (prefixWord ++ tailWord_260506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260506).length < 2 ^ (prefixWord ++ tailWord_260506).sum := by decide
  have hdescent : baseEnd_260506 < baseStart_260506 := by decide
  rcases family_descends (prefixWord ++ tailWord_260506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260510 : List Nat := [4, 3, 1, 2, 1, 3, 1, 7]
def baseStart_260510 : Nat := 118140960795 + 260510 * 2 ^ 59
def prefixEnd_260510 : Nat := 4983230072969 + 3 ^ 40 * 260510 * 2
def baseEnd_260510 : Nat := 9908655207620813861255

theorem tailTrace_260510 : CollatzResearch.WordTrace tailWord_260510 prefixEnd_260510 9908655207620813861255 := by
  unfold tailWord_260510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187697535778029551369373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6334386857482824273969989 1187697535778029551369373)
  ·
    refine ⟨445386575916761081763515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1187697535778029551369373 445386575916761081763515)
    ·
      refine ⟨668079863875141622645273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445386575916761081763515 668079863875141622645273)
      ·
        refine ⟨501059897906356216983955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668079863875141622645273 501059897906356216983955)
        ·
          refine ⟨751589846859534325475933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501059897906356216983955 751589846859534325475933)
          ·
            refine ⟨281846192572325372053475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 751589846859534325475933 281846192572325372053475)
            ·
              refine ⟨422769288858488058080213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281846192572325372053475 422769288858488058080213)
              ·
                refine ⟨9908655207620813861255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 422769288858488058080213 9908655207620813861255)
                ·
                  rfl

theorem cell22_260510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_260510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260510 prefixEnd_260510 := by exact prefixLift 260510
  have htrace : WordTrace (prefixWord ++ tailWord_260510) baseStart_260510 baseEnd_260510 := by
    simpa [prefixWord, tailWord_260510, baseEnd_260510] using wordTrace_append hprefix tailTrace_260510
  have hstable : (prefixWord ++ tailWord_260510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260510).length < 2 ^ (prefixWord ++ tailWord_260510).sum := by decide
  have hdescent : baseEnd_260510 < baseStart_260510 := by decide
  rcases family_descends (prefixWord ++ tailWord_260510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260598 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_260598 : Nat := 118140960795 + 260598 * 2 ^ 59
def prefixEnd_260598 : Nat := 4983230072969 + 3 ^ 40 * 260598 * 2
def baseEnd_260598 : Nat := 89208021066984428551025

theorem tailTrace_260598 : CollatzResearch.WordTrace tailWord_260598 prefixEnd_260598 89208021066984428551025 := by
  unfold tailWord_260598
  simp only [CollatzResearch.WordTrace]
  refine ⟨594049369369089215009903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6336526606603618293438965 594049369369089215009903)
  ·
    refine ⟨891074054053633822514855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 594049369369089215009903 891074054053633822514855)
    ·
      refine ⟨1336611081080450733772283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 891074054053633822514855 1336611081080450733772283)
      ·
        refine ⟨2004916621620676100658425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336611081080450733772283 2004916621620676100658425)
        ·
          refine ⟨1503687466215507075493819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2004916621620676100658425 1503687466215507075493819)
          ·
            refine ⟨2255531199323260613240729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503687466215507075493819 2255531199323260613240729)
            ·
              refine ⟨1691648399492445459930547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255531199323260613240729 1691648399492445459930547)
              ·
                refine ⟨2537472599238668189895821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691648399492445459930547 2537472599238668189895821)
                ·
                  refine ⟨951552224714500571210933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2537472599238668189895821 951552224714500571210933)
                  ·
                    refine ⟨89208021066984428551025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 951552224714500571210933 89208021066984428551025)
                    ·
                      rfl

theorem cell22_260598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_260598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260598 prefixEnd_260598 := by exact prefixLift 260598
  have htrace : WordTrace (prefixWord ++ tailWord_260598) baseStart_260598 baseEnd_260598 := by
    simpa [prefixWord, tailWord_260598, baseEnd_260598] using wordTrace_append hprefix tailTrace_260598
  have hstable : (prefixWord ++ tailWord_260598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260598).length < 2 ^ (prefixWord ++ tailWord_260598).sum := by decide
  have hdescent : baseEnd_260598 < baseStart_260598 := by decide
  rcases family_descends (prefixWord ++ tailWord_260598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260632 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 2, 3]
def baseStart_260632 : Nat := 118140960795 + 260632 * 2 ^ 59
def prefixEnd_260632 : Nat := 4983230072969 + 3 ^ 40 * 260632 * 2
def baseEnd_260632 : Nat := 89219659961819673200921

theorem tailTrace_260632 : CollatzResearch.WordTrace tailWord_260632 prefixEnd_260632 89219659961819673200921 := by
  unfold tailWord_260632
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753014995891125623448075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6337353327854834164597433 4753014995891125623448075)
  ·
    refine ⟨7129522493836688435172113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4753014995891125623448075 7129522493836688435172113)
    ·
      refine ⟨5347141870377516326379085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7129522493836688435172113 5347141870377516326379085)
      ·
        refine ⟨2005178201391568622392157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5347141870377516326379085 2005178201391568622392157)
        ·
          refine ⟨751941825521838233397059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2005178201391568622392157 751941825521838233397059)
          ·
            refine ⟨1127912738282757350095589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751941825521838233397059 1127912738282757350095589)
            ·
              refine ⟨211483638428017003142923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1127912738282757350095589 211483638428017003142923)
              ·
                refine ⟨317225457642025504714385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211483638428017003142923 317225457642025504714385)
                ·
                  refine ⟨237919093231519128535789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317225457642025504714385 237919093231519128535789)
                  ·
                    refine ⟨89219659961819673200921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237919093231519128535789 89219659961819673200921)
                    ·
                      rfl

theorem cell22_260632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_260632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260632 prefixEnd_260632 := by exact prefixLift 260632
  have htrace : WordTrace (prefixWord ++ tailWord_260632) baseStart_260632 baseEnd_260632 := by
    simpa [prefixWord, tailWord_260632, baseEnd_260632] using wordTrace_append hprefix tailTrace_260632
  have hstable : (prefixWord ++ tailWord_260632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260632).length < 2 ^ (prefixWord ++ tailWord_260632).sum := by decide
  have hdescent : baseEnd_260632 < baseStart_260632 := by decide
  rcases family_descends (prefixWord ++ tailWord_260632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260656 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 9]
def baseStart_260656 : Nat := 118140960795 + 260656 * 2 ^ 59
def prefixEnd_260656 : Nat := 4983230072969 + 3 ^ 40 * 260656 * 2
def baseEnd_260656 : Nat := 29742625217430536866949

theorem tailTrace_260656 : CollatzResearch.WordTrace tailWord_260656 prefixEnd_260656 29742625217430536866949 := by
  unfold tailWord_260656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4753452671847651672884911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6337936895796868897179881 4753452671847651672884911)
  ·
    refine ⟨7130179007771477509327367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4753452671847651672884911 7130179007771477509327367)
    ·
      refine ⟨10695268511657216263991051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7130179007771477509327367 10695268511657216263991051)
      ·
        refine ⟨16042902767485824395986577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10695268511657216263991051 16042902767485824395986577)
        ·
          refine ⟨12032177075614368296989933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16042902767485824395986577 12032177075614368296989933)
          ·
            refine ⟨4512066403355388111371225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12032177075614368296989933 4512066403355388111371225)
            ·
              refine ⟨3384049802516541083528419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4512066403355388111371225 3384049802516541083528419)
              ·
                refine ⟨5076074703774811625292629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384049802516541083528419 5076074703774811625292629)
                ·
                  refine ⟨29742625217430536866949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5076074703774811625292629 29742625217430536866949)
                  ·
                    rfl

theorem cell22_260656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_260656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260656 prefixEnd_260656 := by exact prefixLift 260656
  have htrace : WordTrace (prefixWord ++ tailWord_260656) baseStart_260656 baseEnd_260656 := by
    simpa [prefixWord, tailWord_260656, baseEnd_260656] using wordTrace_append hprefix tailTrace_260656
  have hstable : (prefixWord ++ tailWord_260656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260656).length < 2 ^ (prefixWord ++ tailWord_260656).sum := by decide
  have hdescent : baseEnd_260656 < baseStart_260656 := by decide
  rcases family_descends (prefixWord ++ tailWord_260656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260677 : List Nat := [1, 3, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_260677 : Nat := 118140960795 + 260677 * 2 ^ 59
def prefixEnd_260677 : Nat := 4983230072969 + 3 ^ 40 * 260677 * 2
def baseEnd_260677 : Nat := 89235064381454555825783

theorem tailTrace_260677 : CollatzResearch.WordTrace tailWord_260677 prefixEnd_260677 89235064381454555825783 := by
  unfold tailWord_260677
  simp only [CollatzResearch.WordTrace]
  refine ⟨9507671276619223932284285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6338447517746149288189523 9507671276619223932284285)
  ·
    refine ⟨3565376728732208974606607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9507671276619223932284285 3565376728732208974606607)
    ·
      refine ⟨5348065093098313461909911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3565376728732208974606607 5348065093098313461909911)
      ·
        refine ⟨8022097639647470192864867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348065093098313461909911 8022097639647470192864867)
        ·
          refine ⟨12033146459471205289297301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022097639647470192864867 12033146459471205289297301)
          ·
            refine ⟨564053740287712747935811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12033146459471205289297301 564053740287712747935811)
            ·
              refine ⟨846080610431569121903717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564053740287712747935811 846080610431569121903717)
              ·
                refine ⟨158640114455919210356947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846080610431569121903717 158640114455919210356947)
                ·
                  refine ⟨237960171683878815535421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158640114455919210356947 237960171683878815535421)
                  ·
                    refine ⟨89235064381454555825783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237960171683878815535421 89235064381454555825783)
                    ·
                      rfl

theorem cell22_260677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_260677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260677 prefixEnd_260677 := by exact prefixLift 260677
  have htrace : WordTrace (prefixWord ++ tailWord_260677) baseStart_260677 baseEnd_260677 := by
    simpa [prefixWord, tailWord_260677, baseEnd_260677] using wordTrace_append hprefix tailTrace_260677
  have hstable : (prefixWord ++ tailWord_260677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260677).length < 2 ^ (prefixWord ++ tailWord_260677).sum := by decide
  have hdescent : baseEnd_260677 < baseStart_260677 := by decide
  rcases family_descends (prefixWord ++ tailWord_260677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260748 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_260748 : Nat := 118140960795 + 260748 * 2 ^ 59
def prefixEnd_260748 : Nat := 4983230072969 + 3 ^ 40 * 260748 * 2
def baseEnd_260748 : Nat := 89259369132434037300565

theorem tailTrace_260748 : CollatzResearch.WordTrace tailWord_260748 prefixEnd_260748 89259369132434037300565 := by
  unfold tailWord_260748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4755130429681001529059449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6340173906241335372079265 4755130429681001529059449)
  ·
    refine ⟨3566347822260751146794587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4755130429681001529059449 3566347822260751146794587)
    ·
      refine ⟨5349521733391126720191881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566347822260751146794587 5349521733391126720191881)
      ·
        refine ⟨4012141300043345040143911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5349521733391126720191881 4012141300043345040143911)
        ·
          refine ⟨6018211950065017560215867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012141300043345040143911 6018211950065017560215867)
          ·
            refine ⟨9027317925097526340323801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018211950065017560215867 9027317925097526340323801)
            ·
              refine ⟨6770488443823144755242851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9027317925097526340323801 6770488443823144755242851)
              ·
                refine ⟨10155732665734717132864277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6770488443823144755242851 10155732665734717132864277)
                ·
                  refine ⟨476049968706314865603013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10155732665734717132864277 476049968706314865603013)
                  ·
                    refine ⟨89259369132434037300565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 476049968706314865603013 89259369132434037300565)
                    ·
                      rfl

theorem cell22_260748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_260748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260748 prefixEnd_260748 := by exact prefixLift 260748
  have htrace : WordTrace (prefixWord ++ tailWord_260748) baseStart_260748 baseEnd_260748 := by
    simpa [prefixWord, tailWord_260748, baseEnd_260748] using wordTrace_append hprefix tailTrace_260748
  have hstable : (prefixWord ++ tailWord_260748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260748).length < 2 ^ (prefixWord ++ tailWord_260748).sum := by decide
  have hdescent : baseEnd_260748 < baseStart_260748 := by decide
  rcases family_descends (prefixWord ++ tailWord_260748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260769 : List Nat := [1, 2, 3, 3, 3, 2, 1, 3, 4]
def baseStart_260769 : Nat := 118140960795 + 260769 * 2 ^ 59
def prefixEnd_260769 : Nat := 4983230072969 + 3 ^ 40 * 260769 * 2
def baseEnd_260769 : Nat := 29755519287198994175167

theorem tailTrace_260769 : CollatzResearch.WordTrace tailWord_260769 prefixEnd_260769 29755519287198994175167 := by
  unfold tailWord_260769
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511026792285923644633361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6340684528190615763088907 9511026792285923644633361)
  ·
    refine ⟨7133270094214442733475021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9511026792285923644633361 7133270094214442733475021)
    ·
      refine ⟨2674976285330416025053133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7133270094214442733475021 2674976285330416025053133)
      ·
        refine ⟨1003116106998906009394925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2674976285330416025053133 1003116106998906009394925)
        ·
          refine ⟨376168540124589753523097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003116106998906009394925 376168540124589753523097)
          ·
            refine ⟨282126405093442315142323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376168540124589753523097 282126405093442315142323)
            ·
              refine ⟨423189607640163472713485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282126405093442315142323 423189607640163472713485)
              ·
                refine ⟨158696102865061302267557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423189607640163472713485 158696102865061302267557)
                ·
                  refine ⟨29755519287198994175167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158696102865061302267557 29755519287198994175167)
                  ·
                    rfl

theorem cell22_260769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 4].length) (baseStart_260769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260769 prefixEnd_260769 := by exact prefixLift 260769
  have htrace : WordTrace (prefixWord ++ tailWord_260769) baseStart_260769 baseEnd_260769 := by
    simpa [prefixWord, tailWord_260769, baseEnd_260769] using wordTrace_append hprefix tailTrace_260769
  have hstable : (prefixWord ++ tailWord_260769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260769).length < 2 ^ (prefixWord ++ tailWord_260769).sum := by decide
  have hdescent : baseEnd_260769 < baseStart_260769 := by decide
  rcases family_descends (prefixWord ++ tailWord_260769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260782 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_260782 : Nat := 118140960795 + 260782 * 2 ^ 59
def prefixEnd_260782 : Nat := 4983230072969 + 3 ^ 40 * 260782 * 2
def baseEnd_260782 : Nat := 89271008027269281950461

theorem tailTrace_260782 : CollatzResearch.WordTrace tailWord_260782 prefixEnd_260782 89271008027269281950461 := by
  unfold tailWord_260782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188937617654853358107075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6341000627492551243237733 1188937617654853358107075)
  ·
    refine ⟨1783406426482280037160613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1188937617654853358107075 1783406426482280037160613)
    ·
      refine ⟨334388704965427506967615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1783406426482280037160613 334388704965427506967615)
      ·
        refine ⟨501583057448141260451423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334388704965427506967615 501583057448141260451423)
        ·
          refine ⟨752374586172211890677135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501583057448141260451423 752374586172211890677135)
          ·
            refine ⟨1128561879258317836015703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752374586172211890677135 1128561879258317836015703)
            ·
              refine ⟨1692842818887476754023555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128561879258317836015703 1692842818887476754023555)
              ·
                refine ⟨2539264228331215131035333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692842818887476754023555 2539264228331215131035333)
                ·
                  refine ⟨476112042812102837069125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539264228331215131035333 476112042812102837069125)
                  ·
                    refine ⟨89271008027269281950461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 476112042812102837069125 89271008027269281950461)
                    ·
                      rfl

theorem cell22_260782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_260782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260782 prefixEnd_260782 := by exact prefixLift 260782
  have htrace : WordTrace (prefixWord ++ tailWord_260782) baseStart_260782 baseEnd_260782 := by
    simpa [prefixWord, tailWord_260782, baseEnd_260782] using wordTrace_append hprefix tailTrace_260782
  have hstable : (prefixWord ++ tailWord_260782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260782).length < 2 ^ (prefixWord ++ tailWord_260782).sum := by decide
  have hdescent : baseEnd_260782 < baseStart_260782 := by decide
  rcases family_descends (prefixWord ++ tailWord_260782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260793 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_260793 : Nat := 118140960795 + 260793 * 2 ^ 59
def prefixEnd_260793 : Nat := 4983230072969 + 3 ^ 40 * 260793 * 2
def baseEnd_260793 : Nat := 89274773552068919925427

theorem tailTrace_260793 : CollatzResearch.WordTrace tailWord_260793 prefixEnd_260793 89274773552068919925427 := by
  unfold tailWord_260793
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511902144198975743507033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6341268096132650495671355 9511902144198975743507033)
  ·
    refine ⟨7133926608149231807630275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9511902144198975743507033 7133926608149231807630275)
    ·
      refine ⟨10700889912223847711445413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7133926608149231807630275 10700889912223847711445413)
      ·
        refine ⟨2006416858541971445896015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10700889912223847711445413 2006416858541971445896015)
        ·
          refine ⟨3009625287812957168844023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006416858541971445896015 3009625287812957168844023)
          ·
            refine ⟨4514437931719435753266035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009625287812957168844023 4514437931719435753266035)
            ·
              refine ⟨6771656897579153629899053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514437931719435753266035 6771656897579153629899053)
              ·
                refine ⟨2539371336592182611212145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6771656897579153629899053 2539371336592182611212145)
                ·
                  refine ⟨1904528502444136958409109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2539371336592182611212145 1904528502444136958409109)
                  ·
                    refine ⟨89274773552068919925427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1904528502444136958409109 89274773552068919925427)
                    ·
                      rfl

theorem cell22_260793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_260793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260793 prefixEnd_260793 := by exact prefixLift 260793
  have htrace : WordTrace (prefixWord ++ tailWord_260793) baseStart_260793 baseEnd_260793 := by
    simpa [prefixWord, tailWord_260793, baseEnd_260793] using wordTrace_append hprefix tailTrace_260793
  have hstable : (prefixWord ++ tailWord_260793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260793).length < 2 ^ (prefixWord ++ tailWord_260793).sum := by decide
  have hdescent : baseEnd_260793 < baseStart_260793 := by decide
  rcases family_descends (prefixWord ++ tailWord_260793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260801 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 2, 3]
def baseStart_260801 : Nat := 118140960795 + 260801 * 2 ^ 59
def prefixEnd_260801 : Nat := 4983230072969 + 3 ^ 40 * 260801 * 2
def baseEnd_260801 : Nat := 89277512115559565725403

theorem tailTrace_260801 : CollatzResearch.WordTrace tailWord_260801 prefixEnd_260801 89277512115559565725403 := by
  unfold tailWord_260801
  simp only [CollatzResearch.WordTrace]
  refine ⟨9512193928169993109798257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6341462618779995406532171 9512193928169993109798257)
  ·
    refine ⟨7134145446127494832348693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9512193928169993109798257 7134145446127494832348693)
    ·
      refine ⟨334413067787226320266345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7134145446127494832348693 334413067787226320266345)
      ·
        refine ⟨250809800840419740199759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334413067787226320266345 250809800840419740199759)
        ·
          refine ⟨376214701260629610299639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250809800840419740199759 376214701260629610299639)
          ·
            refine ⟨564322051890944415449459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376214701260629610299639 564322051890944415449459)
            ·
              refine ⟨846483077836416623174189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564322051890944415449459 846483077836416623174189)
              ·
                refine ⟨317431154188656233690321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 846483077836416623174189 317431154188656233690321)
                ·
                  refine ⟨238073365641492175267741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317431154188656233690321 238073365641492175267741)
                  ·
                    refine ⟨89277512115559565725403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238073365641492175267741 89277512115559565725403)
                    ·
                      rfl

theorem cell22_260801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_260801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260801 prefixEnd_260801 := by exact prefixLift 260801
  have htrace : WordTrace (prefixWord ++ tailWord_260801) baseStart_260801 baseEnd_260801 := by
    simpa [prefixWord, tailWord_260801, baseEnd_260801] using wordTrace_append hprefix tailTrace_260801
  have hstable : (prefixWord ++ tailWord_260801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260801).length < 2 ^ (prefixWord ++ tailWord_260801).sum := by decide
  have hdescent : baseEnd_260801 < baseStart_260801 := by decide
  rcases family_descends (prefixWord ++ tailWord_260801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260846 : List Nat := [4, 1, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_260846 : Nat := 118140960795 + 260846 * 2 ^ 59
def prefixEnd_260846 : Nat := 4983230072969 + 3 ^ 40 * 260846 * 2
def baseEnd_260846 : Nat := 89292916535194448350265

theorem tailTrace_260846 : CollatzResearch.WordTrace tailWord_260846 prefixEnd_260846 89292916535194448350265 := by
  unfold tailWord_260846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189229401625870724398299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6342556808671310530124261 1189229401625870724398299)
  ·
    refine ⟨1783844102438806086597449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1189229401625870724398299 1783844102438806086597449)
    ·
      refine ⟨1337883076829104564948087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1783844102438806086597449 1337883076829104564948087)
      ·
        refine ⟨2006824615243656847422131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337883076829104564948087 2006824615243656847422131)
        ·
          refine ⟨3010236922865485271133197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006824615243656847422131 3010236922865485271133197)
          ·
            refine ⟨1128838846074556976674949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3010236922865485271133197 1128838846074556976674949)
            ·
              refine ⟨211657283638979433126553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1128838846074556976674949 211657283638979433126553)
              ·
                refine ⟨158742962729234574844915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211657283638979433126553 158742962729234574844915)
                ·
                  refine ⟨238114444093851862267373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158742962729234574844915 238114444093851862267373)
                  ·
                    refine ⟨89292916535194448350265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238114444093851862267373 89292916535194448350265)
                    ·
                      rfl

theorem cell22_260846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_260846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260846 prefixEnd_260846 := by exact prefixLift 260846
  have htrace : WordTrace (prefixWord ++ tailWord_260846) baseStart_260846 baseEnd_260846 := by
    simpa [prefixWord, tailWord_260846, baseEnd_260846] using wordTrace_append hprefix tailTrace_260846
  have hstable : (prefixWord ++ tailWord_260846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260846).length < 2 ^ (prefixWord ++ tailWord_260846).sum := by decide
  have hdescent : baseEnd_260846 < baseStart_260846 := by decide
  rcases family_descends (prefixWord ++ tailWord_260846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260885 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_260885 : Nat := 118140960795 + 260885 * 2 ^ 59
def prefixEnd_260885 : Nat := 4983230072969 + 3 ^ 40 * 260885 * 2
def baseEnd_260885 : Nat := 89306267032211346625145

theorem tailTrace_260885 : CollatzResearch.WordTrace tailWord_260885 prefixEnd_260885 89306267032211346625145 := by
  unfold tailWord_260885
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515257659865675455856109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6343505106577116970570739 9515257659865675455856109)
  ·
    refine ⟨3568221622449628295946041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9515257659865675455856109 3568221622449628295946041)
    ·
      refine ⟨2676166216837221221959531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3568221622449628295946041 2676166216837221221959531)
      ·
        refine ⟨4014249325255831832939297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676166216837221221959531 4014249325255831832939297)
        ·
          refine ⟨3010686993941873874704473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4014249325255831832939297 3010686993941873874704473)
          ·
            refine ⟨2258015245456405406028355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3010686993941873874704473 2258015245456405406028355)
            ·
              refine ⟨3387022868184608109042533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258015245456405406028355 3387022868184608109042533)
              ·
                refine ⟨635066787784614020445475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3387022868184608109042533 635066787784614020445475)
                ·
                  refine ⟨952600181676921030668213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635066787784614020445475 952600181676921030668213)
                  ·
                    refine ⟨89306267032211346625145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 952600181676921030668213 89306267032211346625145)
                    ·
                      rfl

theorem cell22_260885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_260885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260885 prefixEnd_260885 := by exact prefixLift 260885
  have htrace : WordTrace (prefixWord ++ tailWord_260885) baseStart_260885 baseEnd_260885 := by
    simpa [prefixWord, tailWord_260885, baseEnd_260885] using wordTrace_append hprefix tailTrace_260885
  have hstable : (prefixWord ++ tailWord_260885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260885).length < 2 ^ (prefixWord ++ tailWord_260885).sum := by decide
  have hdescent : baseEnd_260885 < baseStart_260885 := by decide
  rcases family_descends (prefixWord ++ tailWord_260885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260919 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 2, 3]
def baseStart_260919 : Nat := 118140960795 + 260919 * 2 ^ 59
def prefixEnd_260919 : Nat := 4983230072969 + 3 ^ 40 * 260919 * 2
def baseEnd_260919 : Nat := 89317905927046591275041

theorem tailTrace_260919 : CollatzResearch.WordTrace tailWord_260919 prefixEnd_260919 89317905927046591275041 := by
  unfold tailWord_260919
  simp only [CollatzResearch.WordTrace]
  refine ⟨9516497741742499262593811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6344331827828332841729207 9516497741742499262593811)
  ·
    refine ⟨14274746612613748893890717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9516497741742499262593811 14274746612613748893890717)
    ·
      refine ⟨5353029979730155835209019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14274746612613748893890717 5353029979730155835209019)
      ·
        refine ⟨8029544969595233752813529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5353029979730155835209019 8029544969595233752813529)
        ·
          refine ⟨6022158727196425314610147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8029544969595233752813529 6022158727196425314610147)
          ·
            refine ⟨9033238090794637971915221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022158727196425314610147 9033238090794637971915221)
            ·
              refine ⟨211716517752999327466763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9033238090794637971915221 211716517752999327466763)
              ·
                refine ⟨317574776629498991200145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211716517752999327466763 317574776629498991200145)
                ·
                  refine ⟨238181082472124243400109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317574776629498991200145 238181082472124243400109)
                  ·
                    refine ⟨89317905927046591275041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238181082472124243400109 89317905927046591275041)
                    ·
                      rfl

theorem cell22_260919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_260919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260919 prefixEnd_260919 := by exact prefixLift 260919
  have htrace : WordTrace (prefixWord ++ tailWord_260919) baseStart_260919 baseEnd_260919 := by
    simpa [prefixWord, tailWord_260919, baseEnd_260919] using wordTrace_append hprefix tailTrace_260919
  have hstable : (prefixWord ++ tailWord_260919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260919).length < 2 ^ (prefixWord ++ tailWord_260919).sum := by decide
  have hdescent : baseEnd_260919 < baseStart_260919 := by decide
  rcases family_descends (prefixWord ++ tailWord_260919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260960 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 7]
def baseStart_260960 : Nat := 118140960795 + 260960 * 2 ^ 59
def prefixEnd_260960 : Nat := 4983230072969 + 3 ^ 40 * 260960 * 2
def baseEnd_260960 : Nat := 29777313688312050333305

theorem tailTrace_260960 : CollatzResearch.WordTrace tailWord_260960 prefixEnd_260960 29777313688312050333305 := by
  unfold tailWord_260960
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758996567296981632418167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6345328756395975509890889 4758996567296981632418167)
  ·
    refine ⟨7138494850945472448627251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4758996567296981632418167 7138494850945472448627251)
    ·
      refine ⟨10707742276418208672940877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7138494850945472448627251 10707742276418208672940877)
      ·
        refine ⟨4015403353656828252352829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10707742276418208672940877 4015403353656828252352829)
        ·
          refine ⟨1505776257621310594632311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4015403353656828252352829 1505776257621310594632311)
          ·
            refine ⟨2258664386431965891948467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505776257621310594632311 2258664386431965891948467)
            ·
              refine ⟨3387996579647948837922701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258664386431965891948467 3387996579647948837922701)
              ·
                refine ⟨1270498717367980814221013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3387996579647948837922701 1270498717367980814221013)
                ·
                  refine ⟨29777313688312050333305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1270498717367980814221013 29777313688312050333305)
                  ·
                    rfl

theorem cell22_260960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_260960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260960 prefixEnd_260960 := by exact prefixLift 260960
  have htrace : WordTrace (prefixWord ++ tailWord_260960) baseStart_260960 baseEnd_260960 := by
    simpa [prefixWord, tailWord_260960, baseEnd_260960] using wordTrace_append hprefix tailTrace_260960
  have hstable : (prefixWord ++ tailWord_260960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260960).length < 2 ^ (prefixWord ++ tailWord_260960).sum := by decide
  have hdescent : baseEnd_260960 < baseStart_260960 := by decide
  rcases family_descends (prefixWord ++ tailWord_260960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260964 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_260964 : Nat := 118140960795 + 260964 * 2 ^ 59
def prefixEnd_260964 : Nat := 4983230072969 + 3 ^ 40 * 260964 * 2
def baseEnd_260964 : Nat := 89333310346681473899903

theorem tailTrace_260964 : CollatzResearch.WordTrace tailWord_260964 prefixEnd_260964 89333310346681473899903 := by
  unfold tailWord_260964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4759069513289735973990973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6345426017719647965321297 4759069513289735973990973)
  ·
    refine ⟨1784651067483650990246615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4759069513289735973990973 1784651067483650990246615)
    ·
      refine ⟨2676976601225476485369923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1784651067483650990246615 2676976601225476485369923)
      ·
        refine ⟨4015464901838214728054885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676976601225476485369923 4015464901838214728054885)
        ·
          refine ⟨752899669094665261510291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4015464901838214728054885 752899669094665261510291)
          ·
            refine ⟨1129349503641997892265437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752899669094665261510291 1129349503641997892265437)
            ·
              refine ⟨423506063865749209599539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1129349503641997892265437 423506063865749209599539)
              ·
                refine ⟨635259095798623814399309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423506063865749209599539 635259095798623814399309)
                ·
                  refine ⟨238222160924483930399741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635259095798623814399309 238222160924483930399741)
                  ·
                    refine ⟨89333310346681473899903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238222160924483930399741 89333310346681473899903)
                    ·
                      rfl

theorem cell22_260964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_260964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260964 prefixEnd_260964 := by exact prefixLift 260964
  have htrace : WordTrace (prefixWord ++ tailWord_260964) baseStart_260964 baseEnd_260964 := by
    simpa [prefixWord, tailWord_260964, baseEnd_260964] using wordTrace_append hprefix tailTrace_260964
  have hstable : (prefixWord ++ tailWord_260964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260964).length < 2 ^ (prefixWord ++ tailWord_260964).sum := by decide
  have hdescent : baseEnd_260964 < baseStart_260964 := by decide
  rcases family_descends (prefixWord ++ tailWord_260964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260975 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 2, 5]
def baseStart_260975 : Nat := 118140960795 + 260975 * 2 ^ 59
def prefixEnd_260975 : Nat := 4983230072969 + 3 ^ 40 * 260975 * 2
def baseEnd_260975 : Nat := 89337075871481111874869

theorem tailTrace_260975 : CollatzResearch.WordTrace tailWord_260975 prefixEnd_260975 89337075871481111874869 := by
  unfold tailWord_260975
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518540229539620826632379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6345693486359747217754919 9518540229539620826632379)
  ·
    refine ⟨14277810344309431239948569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9518540229539620826632379 14277810344309431239948569)
    ·
      refine ⟨10708357758232073429961427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14277810344309431239948569 10708357758232073429961427)
      ·
        refine ⟨16062536637348110144942141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10708357758232073429961427 16062536637348110144942141)
        ·
          refine ⟨6023451239005541304353303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16062536637348110144942141 6023451239005541304353303)
          ·
            refine ⟨9035176858508311956529955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6023451239005541304353303 9035176858508311956529955)
            ·
              refine ⟨13552765287762467934794933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035176858508311956529955 13552765287762467934794933)
              ·
                refine ⟨1270571745727731368887025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13552765287762467934794933 1270571745727731368887025)
                ·
                  refine ⟨952928809295798526665269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1270571745727731368887025 952928809295798526665269)
                  ·
                    refine ⟨89337075871481111874869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 952928809295798526665269 89337075871481111874869)
                    ·
                      rfl

theorem cell22_260975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_260975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260975 prefixEnd_260975 := by exact prefixLift 260975
  have htrace : WordTrace (prefixWord ++ tailWord_260975) baseStart_260975 baseEnd_260975 := by
    simpa [prefixWord, tailWord_260975, baseEnd_260975] using wordTrace_append hprefix tailTrace_260975
  have hstable : (prefixWord ++ tailWord_260975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260975).length < 2 ^ (prefixWord ++ tailWord_260975).sum := by decide
  have hdescent : baseEnd_260975 < baseStart_260975 := by decide
  rcases family_descends (prefixWord ++ tailWord_260975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260977 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 5]
def baseStart_260977 : Nat := 118140960795 + 260977 * 2 ^ 59
def prefixEnd_260977 : Nat := 4983230072969 + 3 ^ 40 * 260977 * 2
def baseEnd_260977 : Nat := 29779253504117924441621

theorem tailTrace_260977 : CollatzResearch.WordTrace tailWord_260977 prefixEnd_260977 29779253504117924441621 := by
  unfold tailWord_260977
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518613175532375168205185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6345742117021583445470123 9518613175532375168205185)
  ·
    refine ⟨7138959881649281376153889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9518613175532375168205185 7138959881649281376153889)
    ·
      refine ⟨5354219911236961032115417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7138959881649281376153889 5354219911236961032115417)
      ·
        refine ⟨4015664933427720774086563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5354219911236961032115417 4015664933427720774086563)
        ·
          refine ⟨6023497400141581161129845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015664933427720774086563 6023497400141581161129845)
          ·
            refine ⟨564702881263273233855923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6023497400141581161129845 564702881263273233855923)
            ·
              refine ⟨847054321894909850783885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564702881263273233855923 847054321894909850783885)
              ·
                refine ⟨317645370710591194043957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 847054321894909850783885 317645370710591194043957)
                ·
                  refine ⟨29779253504117924441621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317645370710591194043957 29779253504117924441621)
                  ·
                    rfl

theorem cell22_260977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_260977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_260977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_260977 prefixEnd_260977 := by exact prefixLift 260977
  have htrace : WordTrace (prefixWord ++ tailWord_260977) baseStart_260977 baseEnd_260977 := by
    simpa [prefixWord, tailWord_260977, baseEnd_260977] using wordTrace_append hprefix tailTrace_260977
  have hstable : (prefixWord ++ tailWord_260977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260977).length < 2 ^ (prefixWord ++ tailWord_260977).sum := by decide
  have hdescent : baseEnd_260977 < baseStart_260977 := by decide
  rcases family_descends (prefixWord ++ tailWord_260977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261035 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 3, 6]
def baseStart_261035 : Nat := 118140960795 + 261035 * 2 ^ 59
def prefixEnd_261035 : Nat := 4983230072969 + 3 ^ 40 * 261035 * 2
def baseEnd_261035 : Nat := 89357615097660955374685

theorem tailTrace_261035 : CollatzResearch.WordTrace tailWord_261035 prefixEnd_261035 89357615097660955374685 := by
  unfold tailWord_261035
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520728609322251073816559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6347152406214834049211039 9520728609322251073816559)
  ·
    refine ⟨14281092913983376610724839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9520728609322251073816559 14281092913983376610724839)
    ·
      refine ⟨21421639370975064916087259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14281092913983376610724839 21421639370975064916087259)
      ·
        refine ⟨32132459056462597374130889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21421639370975064916087259 32132459056462597374130889)
        ·
          refine ⟨24099344292346948030598167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32132459056462597374130889 24099344292346948030598167)
          ·
            refine ⟨36149016438520422045897251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24099344292346948030598167 36149016438520422045897251)
            ·
              refine ⟨54223524657780633068845877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36149016438520422045897251 54223524657780633068845877)
              ·
                refine ⟨5083455436666934350204301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54223524657780633068845877 5083455436666934350204301)
                ·
                  refine ⟨1906295788750100381326613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5083455436666934350204301 1906295788750100381326613)
                  ·
                    refine ⟨89357615097660955374685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1906295788750100381326613 89357615097660955374685)
                    ·
                      rfl

theorem cell22_261035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_261035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261035 prefixEnd_261035 := by exact prefixLift 261035
  have htrace : WordTrace (prefixWord ++ tailWord_261035) baseStart_261035 baseEnd_261035 := by
    simpa [prefixWord, tailWord_261035, baseEnd_261035] using wordTrace_append hprefix tailTrace_261035
  have hstable : (prefixWord ++ tailWord_261035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261035).length < 2 ^ (prefixWord ++ tailWord_261035).sum := by decide
  have hdescent : baseEnd_261035 < baseStart_261035 := by decide
  rcases family_descends (prefixWord ++ tailWord_261035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261054 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_261054 : Nat := 118140960795 + 261054 * 2 ^ 59
def prefixEnd_261054 : Nat := 4983230072969 + 3 ^ 40 * 261054 * 2
def baseEnd_261054 : Nat := 89364119185951239149627

theorem tailTrace_261054 : CollatzResearch.WordTrace tailWord_261054 prefixEnd_261054 89364119185951239149627 := by
  unfold tailWord_261054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190177699531677164844777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6347614397502278212505477 1190177699531677164844777)
  ·
    refine ⟨892633274648757873633583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1190177699531677164844777 892633274648757873633583)
    ·
      refine ⟨1338949911973136810450375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892633274648757873633583 1338949911973136810450375)
      ·
        refine ⟨2008424867959705215675563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338949911973136810450375 2008424867959705215675563)
        ·
          refine ⟨3012637301939557823513345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008424867959705215675563 3012637301939557823513345)
          ·
            refine ⟨2259477976454668367635009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012637301939557823513345 2259477976454668367635009)
            ·
              refine ⟨1694608482341001275726257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259477976454668367635009 1694608482341001275726257)
              ·
                refine ⟨1270956361755750956794693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694608482341001275726257 1270956361755750956794693)
                ·
                  refine ⟨238304317829203304399005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270956361755750956794693 238304317829203304399005)
                  ·
                    refine ⟨89364119185951239149627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238304317829203304399005 89364119185951239149627)
                    ·
                      rfl

theorem cell22_261054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_261054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261054 prefixEnd_261054 := by exact prefixLift 261054
  have htrace : WordTrace (prefixWord ++ tailWord_261054) baseStart_261054 baseEnd_261054 := by
    simpa [prefixWord, tailWord_261054, baseEnd_261054] using wordTrace_append hprefix tailTrace_261054
  have hstable : (prefixWord ++ tailWord_261054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261054).length < 2 ^ (prefixWord ++ tailWord_261054).sum := by decide
  have hdescent : baseEnd_261054 < baseStart_261054 := by decide
  rcases family_descends (prefixWord ++ tailWord_261054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261062 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_261062 : Nat := 118140960795 + 261062 * 2 ^ 59
def prefixEnd_261062 : Nat := 4983230072969 + 3 ^ 40 * 261062 * 2
def baseEnd_261062 : Nat := 29788952583147294983201

theorem tailTrace_261062 : CollatzResearch.WordTrace tailWord_261062 prefixEnd_261062 29788952583147294983201 := by
  unfold tailWord_261062
  simp only [CollatzResearch.WordTrace]
  refine ⟨297553543132013583907795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6347808920149623123366293 297553543132013583907795)
  ·
    refine ⟨446330314698020375861693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297553543132013583907795 446330314698020375861693)
    ·
      refine ⟨167373868011757640948135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446330314698020375861693 167373868011757640948135)
      ·
        refine ⟨251060802017636461422203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167373868011757640948135 251060802017636461422203)
        ·
          refine ⟨376591203026454692133305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251060802017636461422203 376591203026454692133305)
          ·
            refine ⟨282443402269841019099979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376591203026454692133305 282443402269841019099979)
            ·
              refine ⟨423665103404761528649969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282443402269841019099979 423665103404761528649969)
              ·
                refine ⟨317748827553571146487477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423665103404761528649969 317748827553571146487477)
                ·
                  refine ⟨29788952583147294983201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317748827553571146487477 29788952583147294983201)
                  ·
                    rfl

theorem cell22_261062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_261062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261062 prefixEnd_261062 := by exact prefixLift 261062
  have htrace : WordTrace (prefixWord ++ tailWord_261062) baseStart_261062 baseEnd_261062 := by
    simpa [prefixWord, tailWord_261062, baseEnd_261062] using wordTrace_append hprefix tailTrace_261062
  have hstable : (prefixWord ++ tailWord_261062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261062).length < 2 ^ (prefixWord ++ tailWord_261062).sum := by decide
  have hdescent : baseEnd_261062 < baseStart_261062 := by decide
  rcases family_descends (prefixWord ++ tailWord_261062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261071 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 2, 3]
def baseStart_261071 : Nat := 118140960795 + 261071 * 2 ^ 59
def prefixEnd_261071 : Nat := 4983230072969 + 3 ^ 40 * 261071 * 2
def baseEnd_261071 : Nat := 89369938633368861474575

theorem tailTrace_261071 : CollatzResearch.WordTrace tailWord_261071 prefixEnd_261071 89369938633368861474575 := by
  unfold tailWord_261071
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522041637191829222127067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6348027758127886148084711 9522041637191829222127067)
  ·
    refine ⟨14283062455787743833190601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9522041637191829222127067 14283062455787743833190601)
    ·
      refine ⟨10712296841840807874892951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14283062455787743833190601 10712296841840807874892951)
      ·
        refine ⟨16068445262761211812339427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10712296841840807874892951 16068445262761211812339427)
        ·
          refine ⟨24102667894141817718509141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16068445262761211812339427 24102667894141817718509141)
          ·
            refine ⟨282453139384474426388779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 24102667894141817718509141 282453139384474426388779)
            ·
              refine ⟨423679709076711639583169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282453139384474426388779 423679709076711639583169)
              ·
                refine ⟨317759781807533729687377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423679709076711639583169 317759781807533729687377)
                ·
                  refine ⟨238319836355650297265533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317759781807533729687377 238319836355650297265533)
                  ·
                    refine ⟨89369938633368861474575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238319836355650297265533 89369938633368861474575)
                    ·
                      rfl

theorem cell22_261071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_261071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261071 prefixEnd_261071 := by exact prefixLift 261071
  have htrace : WordTrace (prefixWord ++ tailWord_261071) baseStart_261071 baseEnd_261071 := by
    simpa [prefixWord, tailWord_261071, baseEnd_261071] using wordTrace_append hprefix tailTrace_261071
  have hstable : (prefixWord ++ tailWord_261071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261071).length < 2 ^ (prefixWord ++ tailWord_261071).sum := by decide
  have hdescent : baseEnd_261071 < baseStart_261071 := by decide
  rcases family_descends (prefixWord ++ tailWord_261071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261157 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 8]
def baseStart_261157 : Nat := 118140960795 + 261157 * 2 ^ 59
def prefixEnd_261157 : Nat := 4983230072969 + 3 ^ 40 * 261157 * 2
def baseEnd_261157 : Nat := 29799792730297767941437

theorem tailTrace_261157 : CollatzResearch.WordTrace tailWord_261157 prefixEnd_261157 29799792730297767941437 := by
  unfold tailWord_261157
  simp only [CollatzResearch.WordTrace]
  refine ⟨9525178314880265909757725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6350118876586843939838483 9525178314880265909757725)
  ·
    refine ⟨3571941868080099716159147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9525178314880265909757725 3571941868080099716159147)
    ·
      refine ⟨5357912802120149574238721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3571941868080099716159147 5357912802120149574238721)
      ·
        refine ⟨4018434601590112180679041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5357912802120149574238721 4018434601590112180679041)
        ·
          refine ⟨3013825951192584135509281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4018434601590112180679041 3013825951192584135509281)
          ·
            refine ⟨2260369463394438101631961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3013825951192584135509281 2260369463394438101631961)
            ·
              refine ⟨1695277097545828576223971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260369463394438101631961 1695277097545828576223971)
              ·
                refine ⟨2542915646318742864335957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695277097545828576223971 2542915646318742864335957)
                ·
                  refine ⟨29799792730297767941437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2542915646318742864335957 29799792730297767941437)
                  ·
                    rfl

theorem cell22_261157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_261157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261157 prefixEnd_261157 := by exact prefixLift 261157
  have htrace : WordTrace (prefixWord ++ tailWord_261157) baseStart_261157 baseEnd_261157 := by
    simpa [prefixWord, tailWord_261157, baseEnd_261157] using wordTrace_append hprefix tailTrace_261157
  have hstable : (prefixWord ++ tailWord_261157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261157).length < 2 ^ (prefixWord ++ tailWord_261157).sum := by decide
  have hdescent : baseEnd_261157 < baseStart_261157 := by decide
  rcases family_descends (prefixWord ++ tailWord_261157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261189 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_261189 : Nat := 118140960795 + 261189 * 2 ^ 59
def prefixEnd_261189 : Nat := 4983230072969 + 3 ^ 40 * 261189 * 2
def baseEnd_261189 : Nat := 89410332444855887024213

theorem tailTrace_261189 : CollatzResearch.WordTrace tailWord_261189 prefixEnd_261189 89410332444855887024213 := by
  unfold tailWord_261189
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526345450764335374922621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6350896967176223583281747 9526345450764335374922621)
  ·
    refine ⟨3572379544036625765595983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9526345450764335374922621 3572379544036625765595983)
    ·
      refine ⟨5358569316054938648393975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3572379544036625765595983 5358569316054938648393975)
      ·
        refine ⟨8037853974082407972590963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358569316054938648393975 8037853974082407972590963)
        ·
          refine ⟨12056780961123611958886445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037853974082407972590963 12056780961123611958886445)
          ·
            refine ⟨4521292860421354484582417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12056780961123611958886445 4521292860421354484582417)
            ·
              refine ⟨3390969645316015863436813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4521292860421354484582417 3390969645316015863436813)
              ·
                refine ⟨1271613616993505948788805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3390969645316015863436813 1271613616993505948788805)
                ·
                  refine ⟨238427553186282365397901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271613616993505948788805 238427553186282365397901)
                  ·
                    refine ⟨89410332444855887024213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238427553186282365397901 89410332444855887024213)
                    ·
                      rfl

theorem cell22_261189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_261189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261189 prefixEnd_261189 := by exact prefixLift 261189
  have htrace : WordTrace (prefixWord ++ tailWord_261189) baseStart_261189 baseEnd_261189 := by
    simpa [prefixWord, tailWord_261189, baseEnd_261189] using wordTrace_append hprefix tailTrace_261189
  have hstable : (prefixWord ++ tailWord_261189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261189).length < 2 ^ (prefixWord ++ tailWord_261189).sum := by decide
  have hdescent : baseEnd_261189 < baseStart_261189 := by decide
  rcases family_descends (prefixWord ++ tailWord_261189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261191 : List Nat := [1, 1, 4, 1, 3, 3, 1, 4, 4]
def baseStart_261191 : Nat := 118140960795 + 261191 * 2 ^ 59
def prefixEnd_261191 : Nat := 4983230072969 + 3 ^ 40 * 261191 * 2
def baseEnd_261191 : Nat := 29803672361909516158069

theorem tailTrace_261191 : CollatzResearch.WordTrace tailWord_261191 prefixEnd_261191 29803672361909516158069 := by
  unfold tailWord_261191
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526418396757089716495427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6350945597838059810996951 9526418396757089716495427)
  ·
    refine ⟨14289627595135634574743141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9526418396757089716495427 14289627595135634574743141)
    ·
      refine ⟨2679305174087931482764339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14289627595135634574743141 2679305174087931482764339)
      ·
        refine ⟨4018957761131897224146509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679305174087931482764339 4018957761131897224146509)
        ·
          refine ⟨1507109160424461459054941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4018957761131897224146509 1507109160424461459054941)
          ·
            refine ⟨565165935159173047145603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1507109160424461459054941 565165935159173047145603)
            ·
              refine ⟨847748902738759570718405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565165935159173047145603 847748902738759570718405)
              ·
                refine ⟨158952919263517419509701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847748902738759570718405 158952919263517419509701)
                ·
                  refine ⟨29803672361909516158069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158952919263517419509701 29803672361909516158069)
                  ·
                    rfl

theorem cell22_261191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 4].length) (baseStart_261191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261191 prefixEnd_261191 := by exact prefixLift 261191
  have htrace : WordTrace (prefixWord ++ tailWord_261191) baseStart_261191 baseEnd_261191 := by
    simpa [prefixWord, tailWord_261191, baseEnd_261191] using wordTrace_append hprefix tailTrace_261191
  have hstable : (prefixWord ++ tailWord_261191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261191).length < 2 ^ (prefixWord ++ tailWord_261191).sum := by decide
  have hdescent : baseEnd_261191 < baseStart_261191 := by decide
  rcases family_descends (prefixWord ++ tailWord_261191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261204 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_261204 : Nat := 118140960795 + 261204 * 2 ^ 59
def prefixEnd_261204 : Nat := 4983230072969 + 3 ^ 40 * 261204 * 2
def baseEnd_261204 : Nat := 89415467251400847899167

theorem tailTrace_261204 : CollatzResearch.WordTrace tailWord_261204 prefixEnd_261204 89415467251400847899167 := by
  unfold tailWord_261204
  simp only [CollatzResearch.WordTrace]
  refine ⟨4763446272854996468359333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6351261697139995291145777 4763446272854996468359333)
  ·
    refine ⟨893146176160311837817375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4763446272854996468359333 893146176160311837817375)
    ·
      refine ⟨1339719264240467756726063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893146176160311837817375 1339719264240467756726063)
      ·
        refine ⟨2009578896360701635089095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339719264240467756726063 2009578896360701635089095)
        ·
          refine ⟨3014368344541052452633643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009578896360701635089095 3014368344541052452633643)
          ·
            refine ⟨4521552516811578678950465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014368344541052452633643 4521552516811578678950465)
            ·
              refine ⟨3391164387608684009212849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4521552516811578678950465 3391164387608684009212849)
              ·
                refine ⟨2543373290706513006909637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391164387608684009212849 2543373290706513006909637)
                ·
                  refine ⟨476882492007471188795557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543373290706513006909637 476882492007471188795557)
                  ·
                    refine ⟨89415467251400847899167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 476882492007471188795557 89415467251400847899167)
                    ·
                      rfl

theorem cell22_261204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_261204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261204 prefixEnd_261204 := by exact prefixLift 261204
  have htrace : WordTrace (prefixWord ++ tailWord_261204) baseStart_261204 baseEnd_261204 := by
    simpa [prefixWord, tailWord_261204, baseEnd_261204] using wordTrace_append hprefix tailTrace_261204
  have hstable : (prefixWord ++ tailWord_261204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261204).length < 2 ^ (prefixWord ++ tailWord_261204).sum := by decide
  have hdescent : baseEnd_261204 < baseStart_261204 := by decide
  rcases family_descends (prefixWord ++ tailWord_261204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261251 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 3, 3]
def baseStart_261251 : Nat := 118140960795 + 261251 * 2 ^ 59
def prefixEnd_261251 : Nat := 4983230072969 + 3 ^ 40 * 261251 * 2
def baseEnd_261251 : Nat := 89431556311908391974023

theorem tailTrace_261251 : CollatzResearch.WordTrace tailWord_261251 prefixEnd_261251 89431556311908391974023 := by
  unfold tailWord_261251
  simp only [CollatzResearch.WordTrace]
  refine ⟨9528606776539719963679607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6352404517693146642453071 9528606776539719963679607)
  ·
    refine ⟨14292910164809579945519411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9528606776539719963679607 14292910164809579945519411)
    ·
      refine ⟨21439365247214369918279117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14292910164809579945519411 21439365247214369918279117)
      ·
        refine ⟨8039761967705388719354669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21439365247214369918279117 8039761967705388719354669)
        ·
          refine ⟨3014910737889520769758001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8039761967705388719354669 3014910737889520769758001)
          ·
            refine ⟨2261183053417140577318501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014910737889520769758001 2261183053417140577318501)
            ·
              refine ⟨423971822515713858247219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2261183053417140577318501 423971822515713858247219)
              ·
                refine ⟨635957733773570787370829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423971822515713858247219 635957733773570787370829)
                ·
                  refine ⟨238484150165089045264061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635957733773570787370829 238484150165089045264061)
                  ·
                    refine ⟨89431556311908391974023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238484150165089045264061 89431556311908391974023)
                    ·
                      rfl

theorem cell22_261251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 3].length) (baseStart_261251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261251 prefixEnd_261251 := by exact prefixLift 261251
  have htrace : WordTrace (prefixWord ++ tailWord_261251) baseStart_261251 baseEnd_261251 := by
    simpa [prefixWord, tailWord_261251, baseEnd_261251] using wordTrace_append hprefix tailTrace_261251
  have hstable : (prefixWord ++ tailWord_261251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261251).length < 2 ^ (prefixWord ++ tailWord_261251).sum := by decide
  have hdescent : baseEnd_261251 < baseStart_261251 := by decide
  rcases family_descends (prefixWord ++ tailWord_261251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261285 : List Nat := [1, 3, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_261285 : Nat := 118140960795 + 261285 * 2 ^ 59
def prefixEnd_261285 : Nat := 4983230072969 + 3 ^ 40 * 261285 * 2
def baseEnd_261285 : Nat := 89443195206743636623919

theorem tailTrace_261285 : CollatzResearch.WordTrace tailWord_261285 prefixEnd_261285 89443195206743636623919 := by
  unfold tailWord_261285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9529846858416543770417309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6353231238944362513611539 9529846858416543770417309)
  ·
    refine ⟨3573692571906203913906491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9529846858416543770417309 3573692571906203913906491)
    ·
      refine ⟨5360538857859305870859737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573692571906203913906491 5360538857859305870859737)
      ·
        refine ⟨4020404143394479403144803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5360538857859305870859737 4020404143394479403144803)
        ·
          refine ⟨6030606215091719104717205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020404143394479403144803 6030606215091719104717205)
          ·
            refine ⟨282684666332424333033619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6030606215091719104717205 282684666332424333033619)
            ·
              refine ⟨424026999498636499550429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282684666332424333033619 424026999498636499550429)
              ·
                refine ⟨159010124811988687331411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424026999498636499550429 159010124811988687331411)
                ·
                  refine ⟨238515187217983030997117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159010124811988687331411 238515187217983030997117)
                  ·
                    refine ⟨89443195206743636623919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238515187217983030997117 89443195206743636623919)
                    ·
                      rfl

theorem cell22_261285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_261285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261285 prefixEnd_261285 := by exact prefixLift 261285
  have htrace : WordTrace (prefixWord ++ tailWord_261285) baseStart_261285 baseEnd_261285 := by
    simpa [prefixWord, tailWord_261285, baseEnd_261285] using wordTrace_append hprefix tailTrace_261285
  have hstable : (prefixWord ++ tailWord_261285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261285).length < 2 ^ (prefixWord ++ tailWord_261285).sum := by decide
  have hdescent : baseEnd_261285 < baseStart_261285 := by decide
  rcases family_descends (prefixWord ++ tailWord_261285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261354 : List Nat := [3, 1, 3, 1, 1, 13]
def baseStart_261354 : Nat := 118140960795 + 261354 * 2 ^ 59
def prefixEnd_261354 : Nat := 4983230072969 + 3 ^ 40 * 261354 * 2
def baseEnd_261354 : Nat := 1104528584158647612947

theorem tailTrace_261354 : CollatzResearch.WordTrace tailWord_261354 prefixEnd_261354 1104528584158647612947 := by
  unfold tailWord_261354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383090873791642138669779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6354908996777712369786077 2383090873791642138669779)
  ·
    refine ⟨3574636310687463208004669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2383090873791642138669779 3574636310687463208004669)
    ·
      refine ⟨1340488616507798703001751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3574636310687463208004669 1340488616507798703001751)
      ·
        refine ⟨2010732924761698054502627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340488616507798703001751 2010732924761698054502627)
        ·
          refine ⟨3016099387142547081753941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010732924761698054502627 3016099387142547081753941)
          ·
            refine ⟨1104528584158647612947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 3016099387142547081753941 1104528584158647612947)
            ·
              rfl

theorem cell22_261354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 13].length) (baseStart_261354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261354 prefixEnd_261354 := by exact prefixLift 261354
  have htrace : WordTrace (prefixWord ++ tailWord_261354) baseStart_261354 baseEnd_261354 := by
    simpa [prefixWord, tailWord_261354, baseEnd_261354] using wordTrace_append hprefix tailTrace_261354
  have hstable : (prefixWord ++ tailWord_261354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261354).length < 2 ^ (prefixWord ++ tailWord_261354).sum := by decide
  have hdescent : baseEnd_261354 < baseStart_261354 := by decide
  rcases family_descends (prefixWord ++ tailWord_261354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261356 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_261356 : Nat := 118140960795 + 261356 * 2 ^ 59
def prefixEnd_261356 : Nat := 4983230072969 + 3 ^ 40 * 261356 * 2
def baseEnd_261356 : Nat := 89467499957723118098701

theorem tailTrace_261356 : CollatzResearch.WordTrace tailWord_261356 prefixEnd_261356 89467499957723118098701 := by
  unfold tailWord_261356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766218220579661448125961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6354957627439548597501281 4766218220579661448125961)
  ·
    refine ⟨3574663665434746086094471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4766218220579661448125961 3574663665434746086094471)
    ·
      refine ⟨5361995498152119129141707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574663665434746086094471 5361995498152119129141707)
      ·
        refine ⟨8042993247228178693712561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361995498152119129141707 8042993247228178693712561)
        ·
          refine ⟨6032244935421134020284421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8042993247228178693712561 6032244935421134020284421)
          ·
            refine ⟨1131045925391462628803329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6032244935421134020284421 1131045925391462628803329)
            ·
              refine ⟨848284444043596971602497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131045925391462628803329 848284444043596971602497)
              ·
                refine ⟨636213333032697728701873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848284444043596971602497 636213333032697728701873)
                ·
                  refine ⟨477159999774523296526405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636213333032697728701873 477159999774523296526405)
                  ·
                    refine ⟨89467499957723118098701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 477159999774523296526405 89467499957723118098701)
                    ·
                      rfl

theorem cell22_261356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_261356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261356 prefixEnd_261356 := by exact prefixLift 261356
  have htrace : WordTrace (prefixWord ++ tailWord_261356) baseStart_261356 baseEnd_261356 := by
    simpa [prefixWord, tailWord_261356, baseEnd_261356] using wordTrace_append hprefix tailTrace_261356
  have hstable : (prefixWord ++ tailWord_261356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261356).length < 2 ^ (prefixWord ++ tailWord_261356).sum := by decide
  have hdescent : baseEnd_261356 < baseStart_261356 := by decide
  rcases family_descends (prefixWord ++ tailWord_261356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261358 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_261358 : Nat := 118140960795 + 261358 * 2 ^ 59
def prefixEnd_261358 : Nat := 4983230072969 + 3 ^ 40 * 261358 * 2
def baseEnd_261358 : Nat := 89468184598595779548695

theorem tailTrace_261358 : CollatzResearch.WordTrace tailWord_261358 prefixEnd_261358 89468184598595779548695 := by
  unfold tailWord_261358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191563673394009654728091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6355006258101384825216485 1191563673394009654728091)
  ·
    refine ⟨1787345510091014482092137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1191563673394009654728091 1787345510091014482092137)
    ·
      refine ⟨1340509132568260861569103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1787345510091014482092137 1340509132568260861569103)
      ·
        refine ⟨2010763698852391292353655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340509132568260861569103 2010763698852391292353655)
        ·
          refine ⟨3016145548278586938530483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010763698852391292353655 3016145548278586938530483)
          ·
            refine ⟨4524218322417880407795725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016145548278586938530483 4524218322417880407795725)
            ·
              refine ⟨1696581870906705152923397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4524218322417880407795725 1696581870906705152923397)
              ·
                refine ⟨318109100795007216173137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1696581870906705152923397 318109100795007216173137)
                ·
                  refine ⟨238581825596255412129853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318109100795007216173137 238581825596255412129853)
                  ·
                    refine ⟨89468184598595779548695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238581825596255412129853 89468184598595779548695)
                    ·
                      rfl

theorem cell22_261358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_261358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261358 prefixEnd_261358 := by exact prefixLift 261358
  have htrace : WordTrace (prefixWord ++ tailWord_261358) baseStart_261358 baseEnd_261358 := by
    simpa [prefixWord, tailWord_261358, baseEnd_261358] using wordTrace_append hprefix tailTrace_261358
  have hstable : (prefixWord ++ tailWord_261358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261358).length < 2 ^ (prefixWord ++ tailWord_261358).sum := by decide
  have hdescent : baseEnd_261358 < baseStart_261358 := by decide
  rcases family_descends (prefixWord ++ tailWord_261358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261463 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 1, 4]
def baseStart_261463 : Nat := 118140960795 + 261463 * 2 ^ 59
def prefixEnd_261463 : Nat := 4983230072969 + 3 ^ 40 * 261463 * 2
def baseEnd_261463 : Nat := 89504128244410505673373

theorem tailTrace_261463 : CollatzResearch.WordTrace tailWord_261463 prefixEnd_261463 89504128244410505673373 := by
  unfold tailWord_261463
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536339051771680170397043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6357559367847786780264695 9536339051771680170397043)
  ·
    refine ⟨14304508577657520255595565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9536339051771680170397043 14304508577657520255595565)
    ·
      refine ⟨5364190716621570095848337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14304508577657520255595565 5364190716621570095848337)
      ·
        refine ⟨4023143037466177571886253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5364190716621570095848337 4023143037466177571886253)
        ·
          refine ⟨1508678639049816589457345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4023143037466177571886253 1508678639049816589457345)
          ·
            refine ⟨1131508979287362442093009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508678639049816589457345 1131508979287362442093009)
            ·
              refine ⟨848631734465521831569757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131508979287362442093009 848631734465521831569757)
              ·
                refine ⟨318236900424570686838659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 848631734465521831569757 318236900424570686838659)
                ·
                  refine ⟨477355350636856030257989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318236900424570686838659 477355350636856030257989)
                  ·
                    refine ⟨89504128244410505673373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 477355350636856030257989 89504128244410505673373)
                    ·
                      rfl

theorem cell22_261463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_261463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261463 prefixEnd_261463 := by exact prefixLift 261463
  have htrace : WordTrace (prefixWord ++ tailWord_261463) baseStart_261463 baseEnd_261463 := by
    simpa [prefixWord, tailWord_261463, baseEnd_261463] using wordTrace_append hprefix tailTrace_261463
  have hstable : (prefixWord ++ tailWord_261463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261463).length < 2 ^ (prefixWord ++ tailWord_261463).sum := by decide
  have hdescent : baseEnd_261463 < baseStart_261463 := by decide
  rcases family_descends (prefixWord ++ tailWord_261463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261508 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_261508 : Nat := 118140960795 + 261508 * 2 ^ 59
def prefixEnd_261508 : Nat := 4983230072969 + 3 ^ 40 * 261508 * 2
def baseEnd_261508 : Nat := 89519532664045388298235

theorem tailTrace_261508 : CollatzResearch.WordTrace tailWord_261508 prefixEnd_261508 89519532664045388298235 := by
  unfold tailWord_261508
  simp only [CollatzResearch.WordTrace]
  refine ⟨4768990168304326427892589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6358653557739101903856785 4768990168304326427892589)
  ·
    refine ⟨1788371313114122410459721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4768990168304326427892589 1788371313114122410459721)
    ·
      refine ⟨1341278484835591807844791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1788371313114122410459721 1341278484835591807844791)
      ·
        refine ⟨2011917727253387711767187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341278484835591807844791 2011917727253387711767187)
        ·
          refine ⟨3017876590880081567650781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011917727253387711767187 3017876590880081567650781)
          ·
            refine ⟨1131703721580030587869043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3017876590880081567650781 1131703721580030587869043)
            ·
              refine ⟨1697555582370045881803565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131703721580030587869043 1697555582370045881803565)
              ·
                refine ⟨636583343388767205676337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1697555582370045881803565 636583343388767205676337)
                ·
                  refine ⟨477437507541575404257253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636583343388767205676337 477437507541575404257253)
                  ·
                    refine ⟨89519532664045388298235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 477437507541575404257253 89519532664045388298235)
                    ·
                      rfl

theorem cell22_261508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_261508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261508 prefixEnd_261508 := by exact prefixLift 261508
  have htrace : WordTrace (prefixWord ++ tailWord_261508) baseStart_261508 baseEnd_261508 := by
    simpa [prefixWord, tailWord_261508, baseEnd_261508] using wordTrace_append hprefix tailTrace_261508
  have hstable : (prefixWord ++ tailWord_261508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261508).length < 2 ^ (prefixWord ++ tailWord_261508).sum := by decide
  have hdescent : baseEnd_261508 < baseStart_261508 := by decide
  rcases family_descends (prefixWord ++ tailWord_261508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261536 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_261536 : Nat := 118140960795 + 261536 * 2 ^ 59
def prefixEnd_261536 : Nat := 4983230072969 + 3 ^ 40 * 261536 * 2
def baseEnd_261536 : Nat := 89529117636262648598149

theorem tailTrace_261536 : CollatzResearch.WordTrace tailWord_261536 prefixEnd_261536 89529117636262648598149 := by
  unfold tailWord_261536
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769500790253606818902231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6359334387004809091869641 4769500790253606818902231)
  ·
    refine ⟨7154251185380410228353347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4769500790253606818902231 7154251185380410228353347)
    ·
      refine ⟨10731376778070615342530021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7154251185380410228353347 10731376778070615342530021)
      ·
        refine ⟨2012133145888240376724379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10731376778070615342530021 2012133145888240376724379)
        ·
          refine ⟨3018199718832360565086569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012133145888240376724379 3018199718832360565086569)
          ·
            refine ⟨2263649789124270423814927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3018199718832360565086569 2263649789124270423814927)
            ·
              refine ⟨3395474683686405635722391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263649789124270423814927 3395474683686405635722391)
              ·
                refine ⟨5093212025529608453583587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395474683686405635722391 5093212025529608453583587)
                ·
                  refine ⟨7639818038294412680375381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093212025529608453583587 7639818038294412680375381)
                  ·
                    refine ⟨89529117636262648598149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7639818038294412680375381 89529117636262648598149)
                    ·
                      rfl

theorem cell22_261536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_261536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261536 prefixEnd_261536 := by exact prefixLift 261536
  have htrace : WordTrace (prefixWord ++ tailWord_261536) baseStart_261536 baseEnd_261536 := by
    simpa [prefixWord, tailWord_261536, baseEnd_261536] using wordTrace_append hprefix tailTrace_261536
  have hstable : (prefixWord ++ tailWord_261536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261536).length < 2 ^ (prefixWord ++ tailWord_261536).sum := by decide
  have hdescent : baseEnd_261536 < baseStart_261536 := by decide
  rcases family_descends (prefixWord ++ tailWord_261536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261628 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_261628 : Nat := 118140960795 + 261628 * 2 ^ 59
def prefixEnd_261628 : Nat := 4983230072969 + 3 ^ 40 * 261628 * 2
def baseEnd_261628 : Nat := 89560611116405075297867

theorem tailTrace_261628 : CollatzResearch.WordTrace tailWord_261628 prefixEnd_261628 89560611116405075297867 := by
  unfold tailWord_261628
  simp only [CollatzResearch.WordTrace]
  refine ⟨4771178548086956675076769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6361571397449275566769025 4771178548086956675076769)
  ·
    refine ⟨3578383911065217506307577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4771178548086956675076769 3578383911065217506307577)
    ·
      refine ⟨2683787933298913129730683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3578383911065217506307577 2683787933298913129730683)
      ·
        refine ⟨4025681899948369694596025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2683787933298913129730683 4025681899948369694596025)
        ·
          refine ⟨3019261424961277270947019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025681899948369694596025 3019261424961277270947019)
          ·
            refine ⟨4528892137441915906420529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019261424961277270947019 4528892137441915906420529)
            ·
              refine ⟨3396669103081436929815397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528892137441915906420529 3396669103081436929815397)
              ·
                refine ⟨636875456827769424340387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3396669103081436929815397 636875456827769424340387)
                ·
                  refine ⟨955313185241654136510581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636875456827769424340387 955313185241654136510581)
                  ·
                    refine ⟨89560611116405075297867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 955313185241654136510581 89560611116405075297867)
                    ·
                      rfl

theorem cell22_261628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_261628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261628 prefixEnd_261628 := by exact prefixLift 261628
  have htrace : WordTrace (prefixWord ++ tailWord_261628) baseStart_261628 baseEnd_261628 := by
    simpa [prefixWord, tailWord_261628, baseEnd_261628] using wordTrace_append hprefix tailTrace_261628
  have hstable : (prefixWord ++ tailWord_261628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261628).length < 2 ^ (prefixWord ++ tailWord_261628).sum := by decide
  have hdescent : baseEnd_261628 < baseStart_261628 := by decide
  rcases family_descends (prefixWord ++ tailWord_261628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261709 : List Nat := [1, 6, 1, 1, 4, 1, 1, 7]
def baseStart_261709 : Nat := 118140960795 + 261709 * 2 ^ 59
def prefixEnd_261709 : Nat := 4983230072969 + 3 ^ 40 * 261709 * 2
def baseEnd_261709 : Nat := 9954259896860873780291

theorem tailTrace_261709 : CollatzResearch.WordTrace tailWord_261709 prefixEnd_261709 9954259896860873780291 := by
  unfold tailWord_261709
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545311408880464183852181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6363540939253642789234787 9545311408880464183852181)
  ·
    refine ⟨447436472291271758618071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9545311408880464183852181 447436472291271758618071)
    ·
      refine ⟨671154708436907637927107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447436472291271758618071 671154708436907637927107)
      ·
        refine ⟨1006732062655361456890661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671154708436907637927107 1006732062655361456890661)
        ·
          refine ⟨188762261747880273166999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1006732062655361456890661 188762261747880273166999)
          ·
            refine ⟨283143392621820409750499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188762261747880273166999 283143392621820409750499)
            ·
              refine ⟨424715088932730614625749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283143392621820409750499 424715088932730614625749)
              ·
                refine ⟨9954259896860873780291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 424715088932730614625749 9954259896860873780291)
                ·
                  rfl

theorem cell22_261709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 7].length) (baseStart_261709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261709 prefixEnd_261709 := by exact prefixLift 261709
  have htrace : WordTrace (prefixWord ++ tailWord_261709) baseStart_261709 baseEnd_261709 := by
    simpa [prefixWord, tailWord_261709, baseEnd_261709] using wordTrace_append hprefix tailTrace_261709
  have hstable : (prefixWord ++ tailWord_261709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261709).length < 2 ^ (prefixWord ++ tailWord_261709).sum := by decide
  have hdescent : baseEnd_261709 < baseStart_261709 := by decide
  rcases family_descends (prefixWord ++ tailWord_261709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261741 : List Nat := [1, 5, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_261741 : Nat := 118140960795 + 261741 * 2 ^ 59
def prefixEnd_261741 : Nat := 4983230072969 + 3 ^ 40 * 261741 * 2
def baseEnd_261741 : Nat := 89599293325710447222521

theorem tailTrace_261741 : CollatzResearch.WordTrace tailWord_261741 prefixEnd_261741 89599293325710447222521 := by
  unfold tailWord_261741
  simp only [CollatzResearch.WordTrace]
  refine ⟨9546478544764533649017077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6364319029843022432678051 9546478544764533649017077)
  ·
    refine ⟨894982363571675029595351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9546478544764533649017077 894982363571675029595351)
    ·
      refine ⟨1342473545357512544393027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894982363571675029595351 1342473545357512544393027)
      ·
        refine ⟨2013710318036268816589541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342473545357512544393027 2013710318036268816589541)
        ·
          refine ⟨377570684631800403110539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2013710318036268816589541 377570684631800403110539)
          ·
            refine ⟨566356026947700604665809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377570684631800403110539 566356026947700604665809)
            ·
              refine ⟨424767020210775453499357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566356026947700604665809 424767020210775453499357)
              ·
                refine ⟨159287632579040795062259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424767020210775453499357 159287632579040795062259)
                ·
                  refine ⟨238931448868561192593389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159287632579040795062259 238931448868561192593389)
                  ·
                    refine ⟨89599293325710447222521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238931448868561192593389 89599293325710447222521)
                    ·
                      rfl

theorem cell22_261741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_261741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261741 prefixEnd_261741 := by exact prefixLift 261741
  have htrace : WordTrace (prefixWord ++ tailWord_261741) baseStart_261741 baseEnd_261741 := by
    simpa [prefixWord, tailWord_261741, baseEnd_261741] using wordTrace_append hprefix tailTrace_261741
  have hstable : (prefixWord ++ tailWord_261741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261741).length < 2 ^ (prefixWord ++ tailWord_261741).sum := by decide
  have hdescent : baseEnd_261741 < baseStart_261741 := by decide
  rcases family_descends (prefixWord ++ tailWord_261741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261765 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 6]
def baseStart_261765 : Nat := 118140960795 + 261765 * 2 ^ 59
def prefixEnd_261765 : Nat := 4983230072969 + 3 ^ 40 * 261765 * 2
def baseEnd_261765 : Nat := 29869169672060794874149

theorem tailTrace_261765 : CollatzResearch.WordTrace tailWord_261765 prefixEnd_261765 29869169672060794874149 := by
  unfold tailWord_261765
  simp only [CollatzResearch.WordTrace]
  refine ⟨9547353896677585747890749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6364902597785057165260499 9547353896677585747890749)
  ·
    refine ⟨3580257711254094655459031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9547353896677585747890749 3580257711254094655459031)
    ·
      refine ⟨5370386566881141983188547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3580257711254094655459031 5370386566881141983188547)
      ·
        refine ⟨8055579850321712974782821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5370386566881141983188547 8055579850321712974782821)
        ·
          refine ⟨1510421221935321182771779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8055579850321712974782821 1510421221935321182771779)
          ·
            refine ⟨2265631832902981774157669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510421221935321182771779 2265631832902981774157669)
            ·
              refine ⟨424805968669309082654563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2265631832902981774157669 424805968669309082654563)
              ·
                refine ⟨637208953003963623981845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424805968669309082654563 637208953003963623981845)
                ·
                  refine ⟨29869169672060794874149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 637208953003963623981845 29869169672060794874149)
                  ·
                    rfl

theorem cell22_261765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_261765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261765 prefixEnd_261765 := by exact prefixLift 261765
  have htrace : WordTrace (prefixWord ++ tailWord_261765) baseStart_261765 baseEnd_261765 := by
    simpa [prefixWord, tailWord_261765, baseEnd_261765] using wordTrace_append hprefix tailTrace_261765
  have hstable : (prefixWord ++ tailWord_261765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261765).length < 2 ^ (prefixWord ++ tailWord_261765).sum := by decide
  have hdescent : baseEnd_261765 < baseStart_261765 := by decide
  rcases family_descends (prefixWord ++ tailWord_261765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261795 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 2, 4]
def baseStart_261795 : Nat := 118140960795 + 261795 * 2 ^ 59
def prefixEnd_261795 : Nat := 4983230072969 + 3 ^ 40 * 261795 * 2
def baseEnd_261795 : Nat := 89617778629272306372355

theorem tailTrace_261795 : CollatzResearch.WordTrace tailWord_261795 prefixEnd_261795 89617778629272306372355 := by
  unfold tailWord_261795
  simp only [CollatzResearch.WordTrace]
  refine ⟨9548448086568900871482839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6365632057712600580988559 9548448086568900871482839)
  ·
    refine ⟨14322672129853351307224259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9548448086568900871482839 14322672129853351307224259)
    ·
      refine ⟨21484008194780026960836389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14322672129853351307224259 21484008194780026960836389)
      ·
        refine ⟨4028251536521255055156823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21484008194780026960836389 4028251536521255055156823)
        ·
          refine ⟨6042377304781882582735235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028251536521255055156823 6042377304781882582735235)
          ·
            refine ⟨9063565957172823874102853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042377304781882582735235 9063565957172823874102853)
            ·
              refine ⟨1699418616969904476394285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9063565957172823874102853 1699418616969904476394285)
              ·
                refine ⟨637281981363714178647857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1699418616969904476394285 637281981363714178647857)
                ·
                  refine ⟨477961486022785633985893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637281981363714178647857 477961486022785633985893)
                  ·
                    refine ⟨89617778629272306372355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 477961486022785633985893 89617778629272306372355)
                    ·
                      rfl

theorem cell22_261795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 4].length) (baseStart_261795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261795 prefixEnd_261795 := by exact prefixLift 261795
  have htrace : WordTrace (prefixWord ++ tailWord_261795) baseStart_261795 baseEnd_261795 := by
    simpa [prefixWord, tailWord_261795, baseEnd_261795] using wordTrace_append hprefix tailTrace_261795
  have hstable : (prefixWord ++ tailWord_261795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261795).length < 2 ^ (prefixWord ++ tailWord_261795).sum := by decide
  have hdescent : baseEnd_261795 < baseStart_261795 := by decide
  rcases family_descends (prefixWord ++ tailWord_261795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261900 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 8]
def baseStart_261900 : Nat := 118140960795 + 261900 * 2 ^ 59
def prefixEnd_261900 : Nat := 4983230072969 + 3 ^ 40 * 261900 * 2
def baseEnd_261900 : Nat := 29884574091695677499011

theorem tailTrace_261900 : CollatzResearch.WordTrace tailWord_261900 prefixEnd_261900 29884574091695677499011 := by
  unfold tailWord_261900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4776138875594251902027577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6368185167459002536036769 4776138875594251902027577)
  ·
    refine ⟨3582104156695688926520683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4776138875594251902027577 3582104156695688926520683)
    ·
      refine ⟨5373156235043533389781025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582104156695688926520683 5373156235043533389781025)
      ·
        refine ⟨4029867176282650042335769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5373156235043533389781025 4029867176282650042335769)
        ·
          refine ⟨3022400382211987531751827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4029867176282650042335769 3022400382211987531751827)
          ·
            refine ⟨4533600573317981297627741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022400382211987531751827 4533600573317981297627741)
            ·
              refine ⟨1700100214994242986610403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4533600573317981297627741 1700100214994242986610403)
              ·
                refine ⟨2550150322491364479915605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700100214994242986610403 2550150322491364479915605)
                ·
                  refine ⟨29884574091695677499011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2550150322491364479915605 29884574091695677499011)
                  ·
                    rfl

theorem cell22_261900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_261900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261900 prefixEnd_261900 := by exact prefixLift 261900
  have htrace : WordTrace (prefixWord ++ tailWord_261900) baseStart_261900 baseEnd_261900 := by
    simpa [prefixWord, tailWord_261900, baseEnd_261900] using wordTrace_append hprefix tailTrace_261900
  have hstable : (prefixWord ++ tailWord_261900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261900).length < 2 ^ (prefixWord ++ tailWord_261900).sum := by decide
  have hdescent : baseEnd_261900 < baseStart_261900 := by decide
  rcases family_descends (prefixWord ++ tailWord_261900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261902 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_261902 : Nat := 118140960795 + 261902 * 2 ^ 59
def prefixEnd_261902 : Nat := 4983230072969 + 3 ^ 40 * 261902 * 2
def baseEnd_261902 : Nat := 89654406915959693947027

theorem tailTrace_261902 : CollatzResearch.WordTrace tailWord_261902 prefixEnd_261902 89654406915959693947027 := by
  unfold tailWord_261902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1194043837147657268203495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6368233798120838763751973 1194043837147657268203495)
  ·
    refine ⟨1791065755721485902305243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1194043837147657268203495 1791065755721485902305243)
    ·
      refine ⟨2686598633582228853457865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1791065755721485902305243 2686598633582228853457865)
      ·
        refine ⟨2014948975186671640093399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2686598633582228853457865 2014948975186671640093399)
        ·
          refine ⟨3022423462780007460140099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014948975186671640093399 3022423462780007460140099)
          ·
            refine ⟨4533635194170011190210149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022423462780007460140099 4533635194170011190210149)
            ·
              refine ⟨850056598906877098164403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4533635194170011190210149 850056598906877098164403)
              ·
                refine ⟨1275084898360315647246605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850056598906877098164403 1275084898360315647246605)
                ·
                  refine ⟨478156836885118367717477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275084898360315647246605 478156836885118367717477)
                  ·
                    refine ⟨89654406915959693947027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 478156836885118367717477 89654406915959693947027)
                    ·
                      rfl

theorem cell22_261902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_261902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261902 prefixEnd_261902 := by exact prefixLift 261902
  have htrace : WordTrace (prefixWord ++ tailWord_261902) baseStart_261902 baseEnd_261902 := by
    simpa [prefixWord, tailWord_261902, baseEnd_261902] using wordTrace_append hprefix tailTrace_261902
  have hstable : (prefixWord ++ tailWord_261902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261902).length < 2 ^ (prefixWord ++ tailWord_261902).sum := by decide
  have hdescent : baseEnd_261902 < baseStart_261902 := by decide
  rcases family_descends (prefixWord ++ tailWord_261902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261949 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_261949 : Nat := 118140960795 + 261949 * 2 ^ 59
def prefixEnd_261949 : Nat := 4983230072969 + 3 ^ 40 * 261949 * 2
def baseEnd_261949 : Nat := 89670495976467238021883

theorem tailTrace_261949 : CollatzResearch.WordTrace tailWord_261949 prefixEnd_261949 89670495976467238021883 := by
  unfold tailWord_261949
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554064928010985172588901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6369376618673990115059267 9554064928010985172588901)
  ·
    refine ⟨1791387174002059719860419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9554064928010985172588901 1791387174002059719860419)
    ·
      refine ⟨2687080761003089579790629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1791387174002059719860419 2687080761003089579790629)
      ·
        refine ⟨503827642688079296210743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2687080761003089579790629 503827642688079296210743)
        ·
          refine ⟨755741464032118944316115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503827642688079296210743 755741464032118944316115)
          ·
            refine ⟨1133612196048178416474173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755741464032118944316115 1133612196048178416474173)
            ·
              refine ⟨425104573518066906177815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1133612196048178416474173 425104573518066906177815)
              ·
                refine ⟨637656860277100359266723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425104573518066906177815 637656860277100359266723)
                ·
                  refine ⟨956485290415650538900085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637656860277100359266723 956485290415650538900085)
                  ·
                    refine ⟨89670495976467238021883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 956485290415650538900085 89670495976467238021883)
                    ·
                      rfl

theorem cell22_261949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_261949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261949 prefixEnd_261949 := by exact prefixLift 261949
  have htrace : WordTrace (prefixWord ++ tailWord_261949) baseStart_261949 baseEnd_261949 := by
    simpa [prefixWord, tailWord_261949, baseEnd_261949] using wordTrace_append hprefix tailTrace_261949
  have hstable : (prefixWord ++ tailWord_261949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261949).length < 2 ^ (prefixWord ++ tailWord_261949).sum := by decide
  have hdescent : baseEnd_261949 < baseStart_261949 := by decide
  rcases family_descends (prefixWord ++ tailWord_261949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261992 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_261992 : Nat := 118140960795 + 261992 * 2 ^ 59
def prefixEnd_261992 : Nat := 4983230072969 + 3 ^ 40 * 261992 * 2
def baseEnd_261992 : Nat := 89685215755229459196751

theorem tailTrace_261992 : CollatzResearch.WordTrace tailWord_261992 prefixEnd_261992 89685215755229459196751 := by
  unfold tailWord_261992
  simp only [CollatzResearch.WordTrace]
  refine ⟨4777816633427601758202115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6370422177903469010936153 4777816633427601758202115)
  ·
    refine ⟨7166724950141402637303173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4777816633427601758202115 7166724950141402637303173)
    ·
      refine ⟨1343760928151512994494345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7166724950141402637303173 1343760928151512994494345)
      ·
        refine ⟨1007820696113634745870759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1343760928151512994494345 1007820696113634745870759)
        ·
          refine ⟨1511731044170452118806139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007820696113634745870759 1511731044170452118806139)
          ·
            refine ⟨2267596566255678178209209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511731044170452118806139 2267596566255678178209209)
            ·
              refine ⟨1700697424691758633656907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2267596566255678178209209 1700697424691758633656907)
              ·
                refine ⟨2551046137037637950485361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700697424691758633656907 2551046137037637950485361)
                ·
                  refine ⟨1913284602778228462864021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2551046137037637950485361 1913284602778228462864021)
                  ·
                    refine ⟨89685215755229459196751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1913284602778228462864021 89685215755229459196751)
                    ·
                      rfl

theorem cell22_261992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_261992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_261992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_261992 prefixEnd_261992 := by exact prefixLift 261992
  have htrace : WordTrace (prefixWord ++ tailWord_261992) baseStart_261992 baseEnd_261992 := by
    simpa [prefixWord, tailWord_261992, baseEnd_261992] using wordTrace_append hprefix tailTrace_261992
  have hstable : (prefixWord ++ tailWord_261992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261992).length < 2 ^ (prefixWord ++ tailWord_261992).sum := by decide
  have hdescent : baseEnd_261992 < baseStart_261992 := by decide
  rcases family_descends (prefixWord ++ tailWord_261992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262045 : List Nat := [1, 4, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_262045 : Nat := 118140960795 + 262045 * 2 ^ 59
def prefixEnd_262045 : Nat := 4983230072969 + 3 ^ 40 * 262045 * 2
def baseEnd_262045 : Nat := 89703358738354987621589

theorem tailTrace_262045 : CollatzResearch.WordTrace tailWord_262045 prefixEnd_262045 89703358738354987621589 := by
  unfold tailWord_262045
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557566335663193568083589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6371710890442129045389059 9557566335663193568083589)
  ·
    refine ⟨1792043687936848794015673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9557566335663193568083589 1792043687936848794015673)
    ·
      refine ⟨1344032765952636595511755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1792043687936848794015673 1344032765952636595511755)
      ·
        refine ⟨2016049148928954893267633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344032765952636595511755 2016049148928954893267633)
        ·
          refine ⟨1512036861696716169950725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2016049148928954893267633 1512036861696716169950725)
          ·
            refine ⟨283506911568134281865761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1512036861696716169950725 283506911568134281865761)
            ·
              refine ⟨212630183676100711399321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283506911568134281865761 212630183676100711399321)
              ·
                refine ⟨159472637757075533549491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212630183676100711399321 159472637757075533549491)
                ·
                  refine ⟨239208956635613300324237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159472637757075533549491 239208956635613300324237)
                  ·
                    refine ⟨89703358738354987621589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239208956635613300324237 89703358738354987621589)
                    ·
                      rfl

theorem cell22_262045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_262045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262045 prefixEnd_262045 := by exact prefixLift 262045
  have htrace : WordTrace (prefixWord ++ tailWord_262045) baseStart_262045 baseEnd_262045 := by
    simpa [prefixWord, tailWord_262045, baseEnd_262045] using wordTrace_append hprefix tailTrace_262045
  have hstable : (prefixWord ++ tailWord_262045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262045).length < 2 ^ (prefixWord ++ tailWord_262045).sum := by decide
  have hdescent : baseEnd_262045 < baseStart_262045 := by decide
  rcases family_descends (prefixWord ++ tailWord_262045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262069 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 6]
def baseStart_262069 : Nat := 118140960795 + 262069 * 2 ^ 59
def prefixEnd_262069 : Nat := 4983230072969 + 3 ^ 40 * 262069 * 2
def baseEnd_262069 : Nat := 29903858142942308340505

theorem tailTrace_262069 : CollatzResearch.WordTrace tailWord_262069 prefixEnd_262069 29903858142942308340505 := by
  unfold tailWord_262069
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558441687576245666957261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6372294458384163777971507 9558441687576245666957261)
  ·
    refine ⟨3584415632841092125108973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9558441687576245666957261 3584415632841092125108973)
    ·
      refine ⟨1344155862315409546915865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3584415632841092125108973 1344155862315409546915865)
      ·
        refine ⟨1008116896736557160186899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1344155862315409546915865 1008116896736557160186899)
        ·
          refine ⟨1512175345104835740280349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008116896736557160186899 1512175345104835740280349)
          ·
            refine ⟨567065754414313402605131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1512175345104835740280349 567065754414313402605131)
            ·
              refine ⟨850598631621470103907697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567065754414313402605131 850598631621470103907697)
              ·
                refine ⟨637948973716102577930773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850598631621470103907697 637948973716102577930773)
                ·
                  refine ⟨29903858142942308340505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 637948973716102577930773 29903858142942308340505)
                  ·
                    rfl

theorem cell22_262069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_262069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262069 prefixEnd_262069 := by exact prefixLift 262069
  have htrace : WordTrace (prefixWord ++ tailWord_262069) baseStart_262069 baseEnd_262069 := by
    simpa [prefixWord, tailWord_262069, baseEnd_262069] using wordTrace_append hprefix tailTrace_262069
  have hstable : (prefixWord ++ tailWord_262069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262069).length < 2 ^ (prefixWord ++ tailWord_262069).sum := by decide
  have hdescent : baseEnd_262069 < baseStart_262069 := by decide
  rcases family_descends (prefixWord ++ tailWord_262069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262088 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 1, 4]
def baseStart_262088 : Nat := 118140960795 + 262088 * 2 ^ 59
def prefixEnd_262088 : Nat := 4983230072969 + 3 ^ 40 * 262088 * 2
def baseEnd_262088 : Nat := 89718078517117208796457

theorem tailTrace_262088 : CollatzResearch.WordTrace tailWord_262088 prefixEnd_262088 89718078517117208796457 := by
  unfold tailWord_262088
  simp only [CollatzResearch.WordTrace]
  refine ⟨4779567337253705955949459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6372756449671607941265945 4779567337253705955949459)
  ·
    refine ⟨7169351005880558933924189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4779567337253705955949459 7169351005880558933924189)
    ·
      refine ⟨2688506627205209600221571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7169351005880558933924189 2688506627205209600221571)
      ·
        refine ⟨4032759940807814400332357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688506627205209600221571 4032759940807814400332357)
        ·
          refine ⟨756142488901465200062317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4032759940807814400332357 756142488901465200062317)
          ·
            refine ⟨283553433338049450023369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 756142488901465200062317 283553433338049450023369)
            ·
              refine ⟨212665075003537087517527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283553433338049450023369 212665075003537087517527)
              ·
                refine ⟨318997612505305631276291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212665075003537087517527 318997612505305631276291)
                ·
                  refine ⟨478496418757958446914437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318997612505305631276291 478496418757958446914437)
                  ·
                    refine ⟨89718078517117208796457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 478496418757958446914437 89718078517117208796457)
                    ·
                      rfl

theorem cell22_262088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_262088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262088 prefixEnd_262088 := by exact prefixLift 262088
  have htrace : WordTrace (prefixWord ++ tailWord_262088) baseStart_262088 baseEnd_262088 := by
    simpa [prefixWord, tailWord_262088, baseEnd_262088] using wordTrace_append hprefix tailTrace_262088
  have hstable : (prefixWord ++ tailWord_262088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262088).length < 2 ^ (prefixWord ++ tailWord_262088).sum := by decide
  have hdescent : baseEnd_262088 < baseStart_262088 := by decide
  rcases family_descends (prefixWord ++ tailWord_262088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262101 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_262101 : Nat := 118140960795 + 262101 * 2 ^ 59
def prefixEnd_262101 : Nat := 4983230072969 + 3 ^ 40 * 262101 * 2
def baseEnd_262101 : Nat := 89722528682789508221417

theorem tailTrace_262101 : CollatzResearch.WordTrace tailWord_262101 prefixEnd_262101 89722528682789508221417 := by
  unfold tailWord_262101
  simp only [CollatzResearch.WordTrace]
  refine ⟨9559608823460315132122157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6373072548973543421414771 9559608823460315132122157)
  ·
    refine ⟨3584853308797618174545809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9559608823460315132122157 3584853308797618174545809)
    ·
      refine ⟨2688639981598213630909357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3584853308797618174545809 2688639981598213630909357)
      ·
        refine ⟨1008239993099330111591009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2688639981598213630909357 1008239993099330111591009)
        ·
          refine ⟨756179994824497583693257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008239993099330111591009 756179994824497583693257)
          ·
            refine ⟨567134996118373187769943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756179994824497583693257 567134996118373187769943)
            ·
              refine ⟨850702494177559781654915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567134996118373187769943 850702494177559781654915)
              ·
                refine ⟨1276053741266339672482373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850702494177559781654915 1276053741266339672482373)
                ·
                  refine ⟨239260076487438688590445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1276053741266339672482373 239260076487438688590445)
                  ·
                    refine ⟨89722528682789508221417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239260076487438688590445 89722528682789508221417)
                    ·
                      rfl

theorem cell22_262101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_262101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262101 prefixEnd_262101 := by exact prefixLift 262101
  have htrace : WordTrace (prefixWord ++ tailWord_262101) baseStart_262101 baseEnd_262101 := by
    simpa [prefixWord, tailWord_262101, baseEnd_262101] using wordTrace_append hprefix tailTrace_262101
  have hstable : (prefixWord ++ tailWord_262101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262101).length < 2 ^ (prefixWord ++ tailWord_262101).sum := by decide
  have hdescent : baseEnd_262101 < baseStart_262101 := by decide
  rcases family_descends (prefixWord ++ tailWord_262101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262148 : List Nat := [2, 3, 2, 4, 2, 1, 8]
def baseStart_262148 : Nat := 118140960795 + 262148 * 2 ^ 59
def prefixEnd_262148 : Nat := 4983230072969 + 3 ^ 40 * 262148 * 2
def baseEnd_262148 : Nat := 3323652509011001936899

theorem tailTrace_262148 : CollatzResearch.WordTrace tailWord_262148 prefixEnd_262148 3323652509011001936899 := by
  unfold tailWord_262148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4780661527145021079541549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6374215369526694772722065 4780661527145021079541549)
  ·
    refine ⟨1792748072679382904828081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4780661527145021079541549 1792748072679382904828081)
    ·
      refine ⟨1344561054509537178621061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1792748072679382904828081 1344561054509537178621061)
      ·
        refine ⟨252105197720538220991449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1344561054509537178621061 252105197720538220991449)
        ·
          refine ⟨189078898290403665743587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252105197720538220991449 189078898290403665743587)
          ·
            refine ⟨283618347435605498615381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189078898290403665743587 283618347435605498615381)
            ·
              refine ⟨3323652509011001936899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 283618347435605498615381 3323652509011001936899)
              ·
                rfl

theorem cell22_262148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 8].length) (baseStart_262148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262148 prefixEnd_262148 := by exact prefixLift 262148
  have htrace : WordTrace (prefixWord ++ tailWord_262148) baseStart_262148 baseEnd_262148 := by
    simpa [prefixWord, tailWord_262148, baseEnd_262148] using wordTrace_append hprefix tailTrace_262148
  have hstable : (prefixWord ++ tailWord_262148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262148).length < 2 ^ (prefixWord ++ tailWord_262148).sum := by decide
  have hdescent : baseEnd_262148 < baseStart_262148 := by decide
  rcases family_descends (prefixWord ++ tailWord_262148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262221 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 6]
def baseStart_262221 : Nat := 118140960795 + 262221 * 2 ^ 59
def prefixEnd_262221 : Nat := 4983230072969 + 3 ^ 40 * 262221 * 2
def baseEnd_262221 : Nat := 29921202378383065073683

theorem tailTrace_262221 : CollatzResearch.WordTrace tailWord_262221 prefixEnd_262221 29921202378383065073683 := by
  unfold tailWord_262221
  simp only [CollatzResearch.WordTrace]
  refine ⟨9563985583025575626490517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6375990388683717084327011 9563985583025575626490517)
  ·
    refine ⟨448311824204323857491743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9563985583025575626490517 448311824204323857491743)
    ·
      refine ⟨672467736306485786237615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448311824204323857491743 672467736306485786237615)
      ·
        refine ⟨1008701604459728679356423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672467736306485786237615 1008701604459728679356423)
        ·
          refine ⟨1513052406689593019034635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008701604459728679356423 1513052406689593019034635)
          ·
            refine ⟨2269578610034389528551953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513052406689593019034635 2269578610034389528551953)
            ·
              refine ⟨1702183957525792146413965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269578610034389528551953 1702183957525792146413965)
              ·
                refine ⟨638318984072172054905237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1702183957525792146413965 638318984072172054905237)
                ·
                  refine ⟨29921202378383065073683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 638318984072172054905237 29921202378383065073683)
                  ·
                    rfl

theorem cell22_262221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_262221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262221 prefixEnd_262221 := by exact prefixLift 262221
  have htrace : WordTrace (prefixWord ++ tailWord_262221) baseStart_262221 baseEnd_262221 := by
    simpa [prefixWord, tailWord_262221, baseEnd_262221] using wordTrace_append hprefix tailTrace_262221
  have hstable : (prefixWord ++ tailWord_262221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262221).length < 2 ^ (prefixWord ++ tailWord_262221).sum := by decide
  have hdescent : baseEnd_262221 < baseStart_262221 := by decide
  rcases family_descends (prefixWord ++ tailWord_262221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262234 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_262234 : Nat := 118140960795 + 262234 * 2 ^ 59
def prefixEnd_262234 : Nat := 4983230072969 + 3 ^ 40 * 262234 * 2
def baseEnd_262234 : Nat := 89768057300821494646009

theorem tailTrace_262234 : CollatzResearch.WordTrace tailWord_262234 prefixEnd_262234 89768057300821494646009 := by
  unfold tailWord_262234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391114932994619711678439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6376306487985652564475837 2391114932994619711678439)
  ·
    refine ⟨3586672399491929567517659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2391114932994619711678439 3586672399491929567517659)
    ·
      refine ⟨5380008599237894351276489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3586672399491929567517659 5380008599237894351276489)
      ·
        refine ⟨4035006449428420763457367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5380008599237894351276489 4035006449428420763457367)
        ·
          refine ⟨6052509674142631145186051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035006449428420763457367 6052509674142631145186051)
          ·
            refine ⟨9078764511213946717779077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052509674142631145186051 9078764511213946717779077)
            ·
              refine ⟨1702268345852615009583577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9078764511213946717779077 1702268345852615009583577)
              ·
                refine ⟨1276701259389461257187683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702268345852615009583577 1276701259389461257187683)
                ·
                  refine ⟨1915051889084191885781525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276701259389461257187683 1915051889084191885781525)
                  ·
                    refine ⟨89768057300821494646009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1915051889084191885781525 89768057300821494646009)
                    ·
                      rfl

theorem cell22_262234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_262234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262234 prefixEnd_262234 := by exact prefixLift 262234
  have htrace : WordTrace (prefixWord ++ tailWord_262234) baseStart_262234 baseEnd_262234 := by
    simpa [prefixWord, tailWord_262234, baseEnd_262234] using wordTrace_append hprefix tailTrace_262234
  have hstable : (prefixWord ++ tailWord_262234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262234).length < 2 ^ (prefixWord ++ tailWord_262234).sum := by decide
  have hdescent : baseEnd_262234 < baseStart_262234 := by decide
  rcases family_descends (prefixWord ++ tailWord_262234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262236 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_262236 : Nat := 118140960795 + 262236 * 2 ^ 59
def prefixEnd_262236 : Nat := 4983230072969 + 3 ^ 40 * 262236 * 2
def baseEnd_262236 : Nat := 89768741941694156096003

theorem tailTrace_262236 : CollatzResearch.WordTrace tailWord_262236 prefixEnd_262236 89768741941694156096003 := by
  unfold tailWord_262236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4782266338985616594143281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6376355118647488792191041 4782266338985616594143281)
  ·
    refine ⟨3586699754239212445607461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4782266338985616594143281 3586699754239212445607461)
    ·
      refine ⟨672506203919852333551399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3586699754239212445607461 672506203919852333551399)
      ·
        refine ⟨1008759305879778500327099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672506203919852333551399 1008759305879778500327099)
        ·
          refine ⟨1513138958819667750490649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008759305879778500327099 1513138958819667750490649)
          ·
            refine ⟨1134854219114750812867987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1513138958819667750490649 1134854219114750812867987)
            ·
              refine ⟨1702281328672126219301981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134854219114750812867987 1702281328672126219301981)
              ·
                refine ⟨638355498252047332238243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1702281328672126219301981 638355498252047332238243)
                ·
                  refine ⟨957533247378070998357365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638355498252047332238243 957533247378070998357365)
                  ·
                    refine ⟨89768741941694156096003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 957533247378070998357365 89768741941694156096003)
                    ·
                      rfl

theorem cell22_262236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_262236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262236 prefixEnd_262236 := by exact prefixLift 262236
  have htrace : WordTrace (prefixWord ++ tailWord_262236) baseStart_262236 baseEnd_262236 := by
    simpa [prefixWord, tailWord_262236, baseEnd_262236] using wordTrace_append hprefix tailTrace_262236
  have hstable : (prefixWord ++ tailWord_262236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262236).length < 2 ^ (prefixWord ++ tailWord_262236).sum := by decide
  have hdescent : baseEnd_262236 < baseStart_262236 := by decide
  rcases family_descends (prefixWord ++ tailWord_262236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262279 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 1, 8]
def baseStart_262279 : Nat := 118140960795 + 262279 * 2 ^ 59
def prefixEnd_262279 : Nat := 4983230072969 + 3 ^ 40 * 262279 * 2
def baseEnd_262279 : Nat := 89783461720456377270871

theorem tailTrace_262279 : CollatzResearch.WordTrace tailWord_262279 prefixEnd_262279 89783461720456377270871 := by
  unfold tailWord_262279
  simp only [CollatzResearch.WordTrace]
  refine ⟨9566101016815451532101891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6377400677876967688067927 9566101016815451532101891)
  ·
    refine ⟨14349151525223177298152837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9566101016815451532101891 14349151525223177298152837)
    ·
      refine ⟨2690465910979345743403657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14349151525223177298152837 2690465910979345743403657)
      ·
        refine ⟨2017849433234509307552743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2690465910979345743403657 2017849433234509307552743)
        ·
          refine ⟨3026774149851763961329115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017849433234509307552743 3026774149851763961329115)
          ·
            refine ⟨4540161224777645941993673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026774149851763961329115 4540161224777645941993673)
            ·
              refine ⟨3405120918583234456495255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4540161224777645941993673 3405120918583234456495255)
              ·
                refine ⟨5107681377874851684742883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405120918583234456495255 5107681377874851684742883)
                ·
                  refine ⟨7661522066812277527114325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5107681377874851684742883 7661522066812277527114325)
                  ·
                    refine ⟨89783461720456377270871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7661522066812277527114325 89783461720456377270871)
                    ·
                      rfl

theorem cell22_262279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_262279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262279 prefixEnd_262279 := by exact prefixLift 262279
  have htrace : WordTrace (prefixWord ++ tailWord_262279) baseStart_262279 baseEnd_262279 := by
    simpa [prefixWord, tailWord_262279, baseEnd_262279] using wordTrace_append hprefix tailTrace_262279
  have hstable : (prefixWord ++ tailWord_262279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262279).length < 2 ^ (prefixWord ++ tailWord_262279).sum := by decide
  have hdescent : baseEnd_262279 < baseStart_262279 := by decide
  rcases family_descends (prefixWord ++ tailWord_262279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262332 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_262332 : Nat := 118140960795 + 262332 * 2 ^ 59
def prefixEnd_262332 : Nat := 4983230072969 + 3 ^ 40 * 262332 * 2
def baseEnd_262332 : Nat := 89801604703581905695709

theorem tailTrace_262332 : CollatzResearch.WordTrace tailWord_262332 prefixEnd_262332 89801604703581905695709 := by
  unfold tailWord_262332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4784017042811720791890625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6378689390415627722520833 4784017042811720791890625)
  ·
    refine ⟨3588012782108790593917969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4784017042811720791890625 3588012782108790593917969)
    ·
      refine ⟨2691009586581592945438477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3588012782108790593917969 2691009586581592945438477)
      ·
        refine ⟨1009128594968097354539429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2691009586581592945438477 1009128594968097354539429)
        ·
          refine ⟨189211611556518253976143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1009128594968097354539429 189211611556518253976143)
          ·
            refine ⟨283817417334777380964215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189211611556518253976143 283817417334777380964215)
            ·
              refine ⟨425726126002166071446323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283817417334777380964215 425726126002166071446323)
              ·
                refine ⟨638589189003249107169485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425726126002166071446323 638589189003249107169485)
                ·
                  refine ⟨239470945876218415188557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638589189003249107169485 239470945876218415188557)
                  ·
                    refine ⟨89801604703581905695709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239470945876218415188557 89801604703581905695709)
                    ·
                      rfl

theorem cell22_262332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_262332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262332 prefixEnd_262332 := by exact prefixLift 262332
  have htrace : WordTrace (prefixWord ++ tailWord_262332) baseStart_262332 baseEnd_262332 := by
    simpa [prefixWord, tailWord_262332, baseEnd_262332] using wordTrace_append hprefix tailTrace_262332
  have hstable : (prefixWord ++ tailWord_262332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262332).length < 2 ^ (prefixWord ++ tailWord_262332).sum := by decide
  have hdescent : baseEnd_262332 < baseStart_262332 := by decide
  rcases family_descends (prefixWord ++ tailWord_262332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262439 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 4, 3]
def baseStart_262439 : Nat := 118140960795 + 262439 * 2 ^ 59
def prefixEnd_262439 : Nat := 4983230072969 + 3 ^ 40 * 262439 * 2
def baseEnd_262439 : Nat := 89838232990269293270381

theorem tailTrace_262439 : CollatzResearch.WordTrace tailWord_262439 prefixEnd_262439 89838232990269293270381 := by
  unfold tailWord_262439
  simp only [CollatzResearch.WordTrace]
  refine ⟨9571936696235798857926371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6381291130823865905284247 9571936696235798857926371)
  ·
    refine ⟨14357905044353698286889557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9571936696235798857926371 14357905044353698286889557)
    ·
      refine ⟨168256699738519901799487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 14357905044353698286889557 168256699738519901799487)
      ·
        refine ⟨252385049607779852699231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168256699738519901799487 252385049607779852699231)
        ·
          refine ⟨378577574411669779048847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252385049607779852699231 378577574411669779048847)
          ·
            refine ⟨567866361617504668573271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378577574411669779048847 567866361617504668573271)
            ·
              refine ⟨851799542426257002859907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567866361617504668573271 851799542426257002859907)
              ·
                refine ⟨1277699313639385504289861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851799542426257002859907 1277699313639385504289861)
                ·
                  refine ⟨239568621307384782054349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277699313639385504289861 239568621307384782054349)
                  ·
                    refine ⟨89838232990269293270381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239568621307384782054349 89838232990269293270381)
                    ·
                      rfl

theorem cell22_262439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_262439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262439 prefixEnd_262439 := by exact prefixLift 262439
  have htrace : WordTrace (prefixWord ++ tailWord_262439) baseStart_262439 baseEnd_262439 := by
    simpa [prefixWord, tailWord_262439, baseEnd_262439] using wordTrace_append hprefix tailTrace_262439
  have hstable : (prefixWord ++ tailWord_262439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262439).length < 2 ^ (prefixWord ++ tailWord_262439).sum := by decide
  have hdescent : baseEnd_262439 < baseStart_262439 := by decide
  rcases family_descends (prefixWord ++ tailWord_262439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262484 : List Nat := [2, 4, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_262484 : Nat := 118140960795 + 262484 * 2 ^ 59
def prefixEnd_262484 : Nat := 4983230072969 + 3 ^ 40 * 262484 * 2
def baseEnd_262484 : Nat := 89853637409904175895243

theorem tailTrace_262484 : CollatzResearch.WordTrace tailWord_262484 prefixEnd_262484 89853637409904175895243 := by
  unfold tailWord_262484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786788990536385771657253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6382385320715181028876337 4786788990536385771657253)
  ·
    refine ⟨897522935725572332185735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4786788990536385771657253 897522935725572332185735)
    ·
      refine ⟨1346284403588358498278603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897522935725572332185735 1346284403588358498278603)
      ·
        refine ⟨2019426605382537747417905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346284403588358498278603 2019426605382537747417905)
        ·
          refine ⟨1514569954036903310563429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2019426605382537747417905 1514569954036903310563429)
          ·
            refine ⟨283981866381919370730643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1514569954036903310563429 283981866381919370730643)
            ·
              refine ⟨425972799572879056095965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283981866381919370730643 425972799572879056095965)
              ·
                refine ⟨159739799839829646035987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425972799572879056095965 159739799839829646035987)
                ·
                  refine ⟨239609699759744469053981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159739799839829646035987 239609699759744469053981)
                  ·
                    refine ⟨89853637409904175895243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239609699759744469053981 89853637409904175895243)
                    ·
                      rfl

theorem cell22_262484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_262484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262484 prefixEnd_262484 := by exact prefixLift 262484
  have htrace : WordTrace (prefixWord ++ tailWord_262484) baseStart_262484 baseEnd_262484 := by
    simpa [prefixWord, tailWord_262484, baseEnd_262484] using wordTrace_append hprefix tailTrace_262484
  have hstable : (prefixWord ++ tailWord_262484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262484).length < 2 ^ (prefixWord ++ tailWord_262484).sum := by decide
  have hdescent : baseEnd_262484 < baseStart_262484 := by decide
  rcases family_descends (prefixWord ++ tailWord_262484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262585 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 5, 3]
def baseStart_262585 : Nat := 118140960795 + 262585 * 2 ^ 59
def prefixEnd_262585 : Nat := 4983230072969 + 3 ^ 40 * 262585 * 2
def baseEnd_262585 : Nat := 89888211773973579119933

theorem tailTrace_262585 : CollatzResearch.WordTrace tailWord_262585 prefixEnd_262585 89888211773973579119933 := by
  unfold tailWord_262585
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577261753706865792741209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6384841169137910528494139 9577261753706865792741209)
  ·
    refine ⟨7182946315280149344555907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9577261753706865792741209 7182946315280149344555907)
    ·
      refine ⟨10774419472920224016833861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7182946315280149344555907 10774419472920224016833861)
      ·
        refine ⟨2020203651172542003156349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10774419472920224016833861 2020203651172542003156349)
        ·
          refine ⟨757576369189703251183631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2020203651172542003156349 757576369189703251183631)
          ·
            refine ⟨1136364553784554876775447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757576369189703251183631 1136364553784554876775447)
            ·
              refine ⟨1704546830676832315163171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136364553784554876775447 1704546830676832315163171)
              ·
                refine ⟨2556820246015248472744757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704546830676832315163171 2556820246015248472744757)
                ·
                  refine ⟨239701898063929544319821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2556820246015248472744757 239701898063929544319821)
                  ·
                    refine ⟨89888211773973579119933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239701898063929544319821 89888211773973579119933)
                    ·
                      rfl

theorem cell22_262585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_262585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262585 prefixEnd_262585 := by exact prefixLift 262585
  have htrace : WordTrace (prefixWord ++ tailWord_262585) baseStart_262585 baseEnd_262585 := by
    simpa [prefixWord, tailWord_262585, baseEnd_262585] using wordTrace_append hprefix tailTrace_262585
  have hstable : (prefixWord ++ tailWord_262585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262585).length < 2 ^ (prefixWord ++ tailWord_262585).sum := by decide
  have hdescent : baseEnd_262585 < baseStart_262585 := by decide
  rcases family_descends (prefixWord ++ tailWord_262585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262632 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 5]
def baseStart_262632 : Nat := 118140960795 + 262632 * 2 ^ 59
def prefixEnd_262632 : Nat := 4983230072969 + 3 ^ 40 * 262632 * 2
def baseEnd_262632 : Nat := 29968100278160374398263

theorem tailTrace_262632 : CollatzResearch.WordTrace tailWord_262632 prefixEnd_262632 29968100278160374398263 := by
  unfold tailWord_262632
  simp only [CollatzResearch.WordTrace]
  refine ⟨4789487992268296409851075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6385983989691061879801433 4789487992268296409851075)
  ·
    refine ⟨7184231988402444614776613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4789487992268296409851075 7184231988402444614776613)
    ·
      refine ⟨1347043497825458365270615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7184231988402444614776613 1347043497825458365270615)
      ·
        refine ⟨2020565246738187547905923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1347043497825458365270615 2020565246738187547905923)
        ·
          refine ⟨3030847870107281321858885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020565246738187547905923 3030847870107281321858885)
          ·
            refine ⟨568283975645115247848541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3030847870107281321858885 568283975645115247848541)
            ·
              refine ⟨213106490866918217943203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568283975645115247848541 213106490866918217943203)
              ·
                refine ⟨319659736300377326914805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213106490866918217943203 319659736300377326914805)
                ·
                  refine ⟨29968100278160374398263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319659736300377326914805 29968100278160374398263)
                  ·
                    rfl

theorem cell22_262632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_262632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262632 prefixEnd_262632 := by exact prefixLift 262632
  have htrace : WordTrace (prefixWord ++ tailWord_262632) baseStart_262632 baseEnd_262632 := by
    simpa [prefixWord, tailWord_262632, baseEnd_262632] using wordTrace_append hprefix tailTrace_262632
  have hstable : (prefixWord ++ tailWord_262632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262632).length < 2 ^ (prefixWord ++ tailWord_262632).sum := by decide
  have hdescent : baseEnd_262632 < baseStart_262632 := by decide
  rcases family_descends (prefixWord ++ tailWord_262632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262643 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 6]
def baseStart_262643 : Nat := 118140960795 + 262643 * 2 ^ 59
def prefixEnd_262643 : Nat := 4983230072969 + 3 ^ 40 * 262643 * 2
def baseEnd_262643 : Nat := 29969355453093587056585

theorem tailTrace_262643 : CollatzResearch.WordTrace tailWord_262643 prefixEnd_262643 29969355453093587056585 := by
  unfold tailWord_262643
  simp only [CollatzResearch.WordTrace]
  refine ⟨9579377187496741698352583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6386251458331161132235055 9579377187496741698352583)
  ·
    refine ⟨14369065781245112547528875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9579377187496741698352583 14369065781245112547528875)
    ·
      refine ⟨21553598671867668821293313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14369065781245112547528875 21553598671867668821293313)
      ·
        refine ⟨16165199003900751615969985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21553598671867668821293313 16165199003900751615969985)
        ·
          refine ⟨12123899252925563711977489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16165199003900751615969985 12123899252925563711977489)
          ·
            refine ⟨9092924439694172783983117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12123899252925563711977489 9092924439694172783983117)
            ·
              refine ⟨3409846664885314793993669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9092924439694172783983117 3409846664885314793993669)
              ·
                refine ⟨639346249665996523873813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3409846664885314793993669 639346249665996523873813)
                ·
                  refine ⟨29969355453093587056585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639346249665996523873813 29969355453093587056585)
                  ·
                    rfl

theorem cell22_262643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 6].length) (baseStart_262643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262643 prefixEnd_262643 := by exact prefixLift 262643
  have htrace : WordTrace (prefixWord ++ tailWord_262643) baseStart_262643 baseEnd_262643 := by
    simpa [prefixWord, tailWord_262643, baseEnd_262643] using wordTrace_append hprefix tailTrace_262643
  have hstable : (prefixWord ++ tailWord_262643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262643).length < 2 ^ (prefixWord ++ tailWord_262643).sum := by decide
  have hdescent : baseEnd_262643 < baseStart_262643 := by decide
  rcases family_descends (prefixWord ++ tailWord_262643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262673 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_262673 : Nat := 118140960795 + 262673 * 2 ^ 59
def prefixEnd_262673 : Nat := 4983230072969 + 3 ^ 40 * 262673 * 2
def baseEnd_262673 : Nat := 89918335972370682919663

theorem tailTrace_262673 : CollatzResearch.WordTrace tailWord_262673 prefixEnd_262673 89918335972370682919663 := by
  unfold tailWord_262673
  simp only [CollatzResearch.WordTrace]
  refine ⟨9580471377388056821944673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6386980918258704547963115 9580471377388056821944673)
  ·
    refine ⟨7185353533041042616458505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9580471377388056821944673 7185353533041042616458505)
    ·
      refine ⟨5389015149780781962343879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7185353533041042616458505 5389015149780781962343879)
      ·
        refine ⟨8083522724671172943515819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5389015149780781962343879 8083522724671172943515819)
        ·
          refine ⟨12125284087006759415273729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8083522724671172943515819 12125284087006759415273729)
          ·
            refine ⟨9093963065255069561455297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12125284087006759415273729 9093963065255069561455297)
            ·
              refine ⟨6820472298941302171091473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9093963065255069561455297 6820472298941302171091473)
              ·
                refine ⟨5115354224205976628318605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6820472298941302171091473 5115354224205976628318605)
                ·
                  refine ⟨1918257834077241235619477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5115354224205976628318605 1918257834077241235619477)
                  ·
                    refine ⟨89918335972370682919663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1918257834077241235619477 89918335972370682919663)
                    ·
                      rfl

theorem cell22_262673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_262673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262673 prefixEnd_262673 := by exact prefixLift 262673
  have htrace : WordTrace (prefixWord ++ tailWord_262673) baseStart_262673 baseEnd_262673 := by
    simpa [prefixWord, tailWord_262673, baseEnd_262673] using wordTrace_append hprefix tailTrace_262673
  have hstable : (prefixWord ++ tailWord_262673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262673).length < 2 ^ (prefixWord ++ tailWord_262673).sum := by decide
  have hdescent : baseEnd_262673 < baseStart_262673 := by decide
  rcases family_descends (prefixWord ++ tailWord_262673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262675 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 4, 3]
def baseStart_262675 : Nat := 118140960795 + 262675 * 2 ^ 59
def prefixEnd_262675 : Nat := 4983230072969 + 3 ^ 40 * 262675 * 2
def baseEnd_262675 : Nat := 89919020613243344369657

theorem tailTrace_262675 : CollatzResearch.WordTrace tailWord_262675 prefixEnd_262675 89919020613243344369657 := by
  unfold tailWord_262675
  simp only [CollatzResearch.WordTrace]
  refine ⟨9580544323380811163517479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6387029548920540775678319 9580544323380811163517479)
  ·
    refine ⟨14370816485071216745276219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9580544323380811163517479 14370816485071216745276219)
    ·
      refine ⟨21556224727606825117914329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14370816485071216745276219 21556224727606825117914329)
      ·
        refine ⟨16167168545705118838435747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21556224727606825117914329 16167168545705118838435747)
        ·
          refine ⟨24250752818557678257653621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16167168545705118838435747 24250752818557678257653621)
          ·
            refine ⟨2273508076739782336655027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24250752818557678257653621 2273508076739782336655027)
            ·
              refine ⟨3410262115109673504982541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273508076739782336655027 3410262115109673504982541)
              ·
                refine ⟨1278848293166127564368453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3410262115109673504982541 1278848293166127564368453)
                ·
                  refine ⟨239784054968648918319085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278848293166127564368453 239784054968648918319085)
                  ·
                    refine ⟨89919020613243344369657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239784054968648918319085 89919020613243344369657)
                    ·
                      rfl

theorem cell22_262675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 3].length) (baseStart_262675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262675 prefixEnd_262675 := by exact prefixLift 262675
  have htrace : WordTrace (prefixWord ++ tailWord_262675) baseStart_262675 baseEnd_262675 := by
    simpa [prefixWord, tailWord_262675, baseEnd_262675] using wordTrace_append hprefix tailTrace_262675
  have hstable : (prefixWord ++ tailWord_262675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262675).length < 2 ^ (prefixWord ++ tailWord_262675).sum := by decide
  have hdescent : baseEnd_262675 < baseStart_262675 := by decide
  rcases family_descends (prefixWord ++ tailWord_262675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262690 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_262690 : Nat := 118140960795 + 262690 * 2 ^ 59
def prefixEnd_262690 : Nat := 4983230072969 + 3 ^ 40 * 262690 * 2
def baseEnd_262690 : Nat := 89924155419788305244611

theorem tailTrace_262690 : CollatzResearch.WordTrace tailWord_262690 prefixEnd_262690 89924155419788305244611 := by
  unfold tailWord_262690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2395272854581617181328381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6387394278884312483542349 2395272854581617181328381)
  ·
    refine ⟨898227320468106442998143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2395272854581617181328381 898227320468106442998143)
    ·
      refine ⟨1347340980702159664497215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 898227320468106442998143 1347340980702159664497215)
      ·
        refine ⟨2021011471053239496745823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1347340980702159664497215 2021011471053239496745823)
        ·
          refine ⟨3031517206579859245118735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2021011471053239496745823 3031517206579859245118735)
          ·
            refine ⟨4547275809869788867678103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031517206579859245118735 4547275809869788867678103)
            ·
              refine ⟨6820913714804683301517155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4547275809869788867678103 6820913714804683301517155)
              ·
                refine ⟨10231370572207024952275733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6820913714804683301517155 10231370572207024952275733)
                ·
                  refine ⟨479595495572204294637925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10231370572207024952275733 479595495572204294637925)
                  ·
                    refine ⟨89924155419788305244611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 479595495572204294637925 89924155419788305244611)
                    ·
                      rfl

theorem cell22_262690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_262690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262690 prefixEnd_262690 := by exact prefixLift 262690
  have htrace : WordTrace (prefixWord ++ tailWord_262690) baseStart_262690 baseEnd_262690 := by
    simpa [prefixWord, tailWord_262690, baseEnd_262690] using wordTrace_append hprefix tailTrace_262690
  have hstable : (prefixWord ++ tailWord_262690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262690).length < 2 ^ (prefixWord ++ tailWord_262690).sum := by decide
  have hdescent : baseEnd_262690 < baseStart_262690 := by decide
  rcases family_descends (prefixWord ++ tailWord_262690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262726 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_262726 : Nat := 118140960795 + 262726 * 2 ^ 59
def prefixEnd_262726 : Nat := 4983230072969 + 3 ^ 40 * 262726 * 2
def baseEnd_262726 : Nat := 89936478955496211344501

theorem tailTrace_262726 : CollatzResearch.WordTrace tailWord_262726 prefixEnd_262726 89936478955496211344501 := by
  unfold tailWord_262726
  simp only [CollatzResearch.WordTrace]
  refine ⟨299450138943626464800751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6388269630797364582416021 299450138943626464800751)
  ·
    refine ⟨449175208415439697201127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299450138943626464800751 449175208415439697201127)
    ·
      refine ⟨673762812623159545801691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449175208415439697201127 673762812623159545801691)
      ·
        refine ⟨1010644218934739318702537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673762812623159545801691 1010644218934739318702537)
        ·
          refine ⟨757983164201054489026903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1010644218934739318702537 757983164201054489026903)
          ·
            refine ⟨1136974746301581733540355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757983164201054489026903 1136974746301581733540355)
            ·
              refine ⟨1705462119452372600310533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136974746301581733540355 1705462119452372600310533)
              ·
                refine ⟨319774147397319862558225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1705462119452372600310533 319774147397319862558225)
                ·
                  refine ⟨239830610547989896918669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319774147397319862558225 239830610547989896918669)
                  ·
                    refine ⟨89936478955496211344501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239830610547989896918669 89936478955496211344501)
                    ·
                      rfl

theorem cell22_262726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_262726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262726 prefixEnd_262726 := by exact prefixLift 262726
  have htrace : WordTrace (prefixWord ++ tailWord_262726) baseStart_262726 baseEnd_262726 := by
    simpa [prefixWord, tailWord_262726, baseEnd_262726] using wordTrace_append hprefix tailTrace_262726
  have hstable : (prefixWord ++ tailWord_262726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262726).length < 2 ^ (prefixWord ++ tailWord_262726).sum := by decide
  have hdescent : baseEnd_262726 < baseStart_262726 := by decide
  rcases family_descends (prefixWord ++ tailWord_262726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262812 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 6]
def baseStart_262812 : Nat := 118140960795 + 262812 * 2 ^ 59
def prefixEnd_262812 : Nat := 4983230072969 + 3 ^ 40 * 262812 * 2
def baseEnd_262812 : Nat := 29988639504340217898079

theorem tailTrace_262812 : CollatzResearch.WordTrace tailWord_262812 prefixEnd_262812 29988639504340217898079 := by
  unfold tailWord_262812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4792770561942241780627345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6390360749256322374169793 4792770561942241780627345)
  ·
    refine ⟨3594577921456681335470509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4792770561942241780627345 3594577921456681335470509)
    ·
      refine ⟨1347966720546255500801441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3594577921456681335470509 1347966720546255500801441)
      ·
        refine ⟨1010975040409691625601081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1347966720546255500801441 1010975040409691625601081)
        ·
          refine ⟨758231280307268719200811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1010975040409691625601081 758231280307268719200811)
          ·
            refine ⟨1137346920460903078801217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758231280307268719200811 1137346920460903078801217)
            ·
              refine ⟨853010190345677309100913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1137346920460903078801217 853010190345677309100913)
              ·
                refine ⟨639757642759257981825685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853010190345677309100913 639757642759257981825685)
                ·
                  refine ⟨29988639504340217898079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639757642759257981825685 29988639504340217898079)
                  ·
                    rfl

theorem cell22_262812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_262812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262812 prefixEnd_262812 := by exact prefixLift 262812
  have htrace : WordTrace (prefixWord ++ tailWord_262812) baseStart_262812 baseEnd_262812 := by
    simpa [prefixWord, tailWord_262812, baseEnd_262812] using wordTrace_append hprefix tailTrace_262812
  have hstable : (prefixWord ++ tailWord_262812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262812).length < 2 ^ (prefixWord ++ tailWord_262812).sum := by decide
  have hdescent : baseEnd_262812 < baseStart_262812 := by decide
  rcases family_descends (prefixWord ++ tailWord_262812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262842 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_262842 : Nat := 118140960795 + 262842 * 2 ^ 59
def prefixEnd_262842 : Nat := 4983230072969 + 3 ^ 40 * 262842 * 2
def baseEnd_262842 : Nat := 89976188126110575444145

theorem tailTrace_262842 : CollatzResearch.WordTrace tailWord_262842 prefixEnd_262842 89976188126110575444145 := by
  unfold tailWord_262842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396658828443949671211695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6391090209183865789897853 2396658828443949671211695)
  ·
    refine ⟨3594988242665924506817543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2396658828443949671211695 3594988242665924506817543)
    ·
      refine ⟨5392482363998886760226315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3594988242665924506817543 5392482363998886760226315)
      ·
        refine ⟨8088723545998330140339473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5392482363998886760226315 8088723545998330140339473)
        ·
          refine ⟨6066542659498747605254605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8088723545998330140339473 6066542659498747605254605)
          ·
            refine ⟨2274953497312030351970477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6066542659498747605254605 2274953497312030351970477)
            ·
              refine ⟨853107561492011381988929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2274953497312030351970477 853107561492011381988929)
              ·
                refine ⟨639830671119008536491697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853107561492011381988929 639830671119008536491697)
                ·
                  refine ⟨479873003339256402368773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639830671119008536491697 479873003339256402368773)
                  ·
                    refine ⟨89976188126110575444145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 479873003339256402368773 89976188126110575444145)
                    ·
                      rfl

theorem cell22_262842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_262842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262842 prefixEnd_262842 := by exact prefixLift 262842
  have htrace : WordTrace (prefixWord ++ tailWord_262842) baseStart_262842 baseEnd_262842 := by
    simpa [prefixWord, tailWord_262842, baseEnd_262842] using wordTrace_append hprefix tailTrace_262842
  have hstable : (prefixWord ++ tailWord_262842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262842).length < 2 ^ (prefixWord ++ tailWord_262842).sum := by decide
  have hdescent : baseEnd_262842 < baseStart_262842 := by decide
  rcases family_descends (prefixWord ++ tailWord_262842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262844 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_262844 : Nat := 118140960795 + 262844 * 2 ^ 59
def prefixEnd_262844 : Nat := 4983230072969 + 3 ^ 40 * 262844 * 2
def baseEnd_262844 : Nat := 89976872766983236894139

theorem tailTrace_262844 : CollatzResearch.WordTrace tailWord_262844 prefixEnd_262844 89976872766983236894139 := by
  unfold tailWord_262844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4793354129884276513209793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6391138839845702017613057 4793354129884276513209793)
  ·
    refine ⟨3595015597413207384907345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4793354129884276513209793 3595015597413207384907345)
    ·
      refine ⟨2696261698059905538680509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3595015597413207384907345 2696261698059905538680509)
      ·
        refine ⟨1011098136772464577005191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2696261698059905538680509 1011098136772464577005191)
        ·
          refine ⟨1516647205158696865507787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011098136772464577005191 1516647205158696865507787)
          ·
            refine ⟨2274970807738045298261681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516647205158696865507787 2274970807738045298261681)
            ·
              refine ⟨1706228105803533973696261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2274970807738045298261681 1706228105803533973696261)
              ·
                refine ⟨319917769838162620068049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1706228105803533973696261 319917769838162620068049)
                ·
                  refine ⟨239938327378621965051037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319917769838162620068049 239938327378621965051037)
                  ·
                    refine ⟨89976872766983236894139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239938327378621965051037 89976872766983236894139)
                    ·
                      rfl

theorem cell22_262844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_262844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262844 prefixEnd_262844 := by exact prefixLift 262844
  have htrace : WordTrace (prefixWord ++ tailWord_262844) baseStart_262844 baseEnd_262844 := by
    simpa [prefixWord, tailWord_262844, baseEnd_262844] using wordTrace_append hprefix tailTrace_262844
  have hstable : (prefixWord ++ tailWord_262844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262844).length < 2 ^ (prefixWord ++ tailWord_262844).sum := by decide
  have hdescent : baseEnd_262844 < baseStart_262844 := by decide
  rcases family_descends (prefixWord ++ tailWord_262844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262846 : List Nat := [4, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_262846 : Nat := 118140960795 + 262846 * 2 ^ 59
def prefixEnd_262846 : Nat := 4983230072969 + 3 ^ 40 * 262846 * 2
def baseEnd_262846 : Nat := 29992519135951966114711

theorem tailTrace_262846 : CollatzResearch.WordTrace tailWord_262846 prefixEnd_262846 29992519135951966114711 := by
  unfold tailWord_262846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198347650720163420999049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6391187470507538245328261 1198347650720163420999049)
  ·
    refine ⟨898760738040122565749287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1198347650720163420999049 898760738040122565749287)
    ·
      refine ⟨1348141107060183848623931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 898760738040122565749287 1348141107060183848623931)
      ·
        refine ⟨2022211660590275772935897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348141107060183848623931 2022211660590275772935897)
        ·
          refine ⟨1516658745442706829701923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022211660590275772935897 1516658745442706829701923)
          ·
            refine ⟨2274988118164060244552885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516658745442706829701923 2274988118164060244552885)
            ·
              refine ⟨213280136077880647926833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2274988118164060244552885 213280136077880647926833)
              ·
                refine ⟨159960102058410485945125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213280136077880647926833 159960102058410485945125)
                ·
                  refine ⟨29992519135951966114711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159960102058410485945125 29992519135951966114711)
                  ·
                    rfl

theorem cell22_262846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_262846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262846 prefixEnd_262846 := by exact prefixLift 262846
  have htrace : WordTrace (prefixWord ++ tailWord_262846) baseStart_262846 baseEnd_262846 := by
    simpa [prefixWord, tailWord_262846, baseEnd_262846] using wordTrace_append hprefix tailTrace_262846
  have hstable : (prefixWord ++ tailWord_262846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262846).length < 2 ^ (prefixWord ++ tailWord_262846).sum := by decide
  have hdescent : baseEnd_262846 < baseStart_262846 := by decide
  rcases family_descends (prefixWord ++ tailWord_262846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262855 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 2, 7]
def baseStart_262855 : Nat := 118140960795 + 262855 * 2 ^ 59
def prefixEnd_262855 : Nat := 4983230072969 + 3 ^ 40 * 262855 * 2
def baseEnd_262855 : Nat := 89980638291782874869105

theorem tailTrace_262855 : CollatzResearch.WordTrace tailWord_262855 prefixEnd_262855 89980638291782874869105 := by
  unfold tailWord_262855
  simp only [CollatzResearch.WordTrace]
  refine ⟨9587109462728701905070019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6391406308485801270046679 9587109462728701905070019)
  ·
    refine ⟨14380664194093052857605029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9587109462728701905070019 14380664194093052857605029)
    ·
      refine ⟨2696374536392447410800943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14380664194093052857605029 2696374536392447410800943)
      ·
        refine ⟨4044561804588671116201415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2696374536392447410800943 4044561804588671116201415)
        ·
          refine ⟨6066842706883006674302123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4044561804588671116201415 6066842706883006674302123)
          ·
            refine ⟨9100264060324510011453185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6066842706883006674302123 9100264060324510011453185)
            ·
              refine ⟨6825198045243382508589889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9100264060324510011453185 6825198045243382508589889)
              ·
                refine ⟨5118898533932536881442417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6825198045243382508589889 5118898533932536881442417)
                ·
                  refine ⟨3839173900449402661081813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5118898533932536881442417 3839173900449402661081813)
                  ·
                    refine ⟨89980638291782874869105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3839173900449402661081813 89980638291782874869105)
                    ·
                      rfl

theorem cell22_262855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_262855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262855 prefixEnd_262855 := by exact prefixLift 262855
  have htrace : WordTrace (prefixWord ++ tailWord_262855) baseStart_262855 baseEnd_262855 := by
    simpa [prefixWord, tailWord_262855, baseEnd_262855] using wordTrace_append hprefix tailTrace_262855
  have hstable : (prefixWord ++ tailWord_262855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262855).length < 2 ^ (prefixWord ++ tailWord_262855).sum := by decide
  have hdescent : baseEnd_262855 < baseStart_262855 := by decide
  rcases family_descends (prefixWord ++ tailWord_262855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262876 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_262876 : Nat := 118140960795 + 262876 * 2 ^ 59
def prefixEnd_262876 : Nat := 4983230072969 + 3 ^ 40 * 262876 * 2
def baseEnd_262876 : Nat := 89987827020945820094041

theorem tailTrace_262876 : CollatzResearch.WordTrace tailWord_262876 prefixEnd_262876 89987827020945820094041 := by
  unfold tailWord_262876
  simp only [CollatzResearch.WordTrace]
  refine ⟨4793937697826311245792241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6391916930435081661056321 4793937697826311245792241)
  ·
    refine ⟨3595453273369733434344181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4793937697826311245792241 3595453273369733434344181)
    ·
      refine ⟨337073744378412509469767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3595453273369733434344181 337073744378412509469767)
      ·
        refine ⟨505610616567618764204651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337073744378412509469767 505610616567618764204651)
        ·
          refine ⟨758415924851428146306977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505610616567618764204651 758415924851428146306977)
          ·
            refine ⟨568811943638571109730233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758415924851428146306977 568811943638571109730233)
            ·
              refine ⟨426608957728928332297675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568811943638571109730233 426608957728928332297675)
              ·
                refine ⟨639913436593392498446513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426608957728928332297675 639913436593392498446513)
                ·
                  refine ⟨479935077445044373834885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639913436593392498446513 479935077445044373834885)
                  ·
                    refine ⟨89987827020945820094041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 479935077445044373834885 89987827020945820094041)
                    ·
                      rfl

theorem cell22_262876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_262876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262876 prefixEnd_262876 := by exact prefixLift 262876
  have htrace : WordTrace (prefixWord ++ tailWord_262876) baseStart_262876 baseEnd_262876 := by
    simpa [prefixWord, tailWord_262876, baseEnd_262876] using wordTrace_append hprefix tailTrace_262876
  have hstable : (prefixWord ++ tailWord_262876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262876).length < 2 ^ (prefixWord ++ tailWord_262876).sum := by decide
  have hdescent : baseEnd_262876 < baseStart_262876 := by decide
  rcases family_descends (prefixWord ++ tailWord_262876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262919 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 5]
def baseStart_262919 : Nat := 118140960795 + 262919 * 2 ^ 59
def prefixEnd_262919 : Nat := 4983230072969 + 3 ^ 40 * 262919 * 2
def baseEnd_262919 : Nat := 30000848933236013756303

theorem tailTrace_262919 : CollatzResearch.WordTrace tailWord_262919 prefixEnd_262919 30000848933236013756303 := by
  unfold tailWord_262919
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589443734496840835399811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6392962489664560556933207 9589443734496840835399811)
  ·
    refine ⟨14384165601745261253099717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9589443734496840835399811 14384165601745261253099717)
    ·
      refine ⟨2697031050327236484956197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14384165601745261253099717 2697031050327236484956197)
      ·
        refine ⟨505693321936356840929287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2697031050327236484956197 505693321936356840929287)
        ·
          refine ⟨758539982904535261393931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505693321936356840929287 758539982904535261393931)
          ·
            refine ⟨1137809974356802892090897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758539982904535261393931 1137809974356802892090897)
            ·
              refine ⟨853357480767602169068173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1137809974356802892090897 853357480767602169068173)
              ·
                refine ⟨320009055287850813400565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853357480767602169068173 320009055287850813400565)
                ·
                  refine ⟨30000848933236013756303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320009055287850813400565 30000848933236013756303)
                  ·
                    rfl

theorem cell22_262919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 5].length) (baseStart_262919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262919 prefixEnd_262919 := by exact prefixLift 262919
  have htrace : WordTrace (prefixWord ++ tailWord_262919) baseStart_262919 baseEnd_262919 := by
    simpa [prefixWord, tailWord_262919, baseEnd_262919] using wordTrace_append hprefix tailTrace_262919
  have hstable : (prefixWord ++ tailWord_262919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262919).length < 2 ^ (prefixWord ++ tailWord_262919).sum := by decide
  have hdescent : baseEnd_262919 < baseStart_262919 := by decide
  rcases family_descends (prefixWord ++ tailWord_262919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262949 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_262949 : Nat := 118140960795 + 262949 * 2 ^ 59
def prefixEnd_262949 : Nat := 4983230072969 + 3 ^ 40 * 262949 * 2
def baseEnd_262949 : Nat := 90012816412797963018817

theorem tailTrace_262949 : CollatzResearch.WordTrace tailWord_262949 prefixEnd_262949 90012816412797963018817 := by
  unfold tailWord_262949
  simp only [CollatzResearch.WordTrace]
  refine ⟨9590537924388155958991901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6393691949592103972661267 9590537924388155958991901)
  ·
    refine ⟨3596451721645558484621963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9590537924388155958991901 3596451721645558484621963)
    ·
      refine ⟨5394677582468337726932945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3596451721645558484621963 5394677582468337726932945)
      ·
        refine ⟨4046008186851253295199709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5394677582468337726932945 4046008186851253295199709)
        ·
          refine ⟨1517253070069219985699891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4046008186851253295199709 1517253070069219985699891)
          ·
            refine ⟨2275879605103829978549837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517253070069219985699891 2275879605103829978549837)
            ·
              refine ⟨853454851913936241956189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2275879605103829978549837 853454851913936241956189)
              ·
                refine ⟨320045569467726090733571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853454851913936241956189 320045569467726090733571)
                ·
                  refine ⟨480068354201589136100357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320045569467726090733571 480068354201589136100357)
                  ·
                    refine ⟨90012816412797963018817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 480068354201589136100357 90012816412797963018817)
                    ·
                      rfl

theorem cell22_262949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_262949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262949 prefixEnd_262949 := by exact prefixLift 262949
  have htrace : WordTrace (prefixWord ++ tailWord_262949) baseStart_262949 baseEnd_262949 := by
    simpa [prefixWord, tailWord_262949, baseEnd_262949] using wordTrace_append hprefix tailTrace_262949
  have hstable : (prefixWord ++ tailWord_262949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262949).length < 2 ^ (prefixWord ++ tailWord_262949).sum := by decide
  have hdescent : baseEnd_262949 < baseStart_262949 := by decide
  rcases family_descends (prefixWord ++ tailWord_262949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262994 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_262994 : Nat := 118140960795 + 262994 * 2 ^ 59
def prefixEnd_262994 : Nat := 4983230072969 + 3 ^ 40 * 262994 * 2
def baseEnd_262994 : Nat := 90028220832432845643679

theorem tailTrace_262994 : CollatzResearch.WordTrace tailWord_262994 prefixEnd_262994 90028220832432845643679 := by
  unfold tailWord_262994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398044802306282161095009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6394786139483419096253357 2398044802306282161095009)
  ·
    refine ⟨1798533601729711620821257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2398044802306282161095009 1798533601729711620821257)
    ·
      refine ⟨1348900201297283715615943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1798533601729711620821257 1348900201297283715615943)
      ·
        refine ⟨2023350301945925573423915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348900201297283715615943 2023350301945925573423915)
        ·
          refine ⟨3035025452918888360135873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023350301945925573423915 3035025452918888360135873)
          ·
            refine ⟨2276269089689166270101905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035025452918888360135873 2276269089689166270101905)
            ·
              refine ⟨1707201817266874702576429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276269089689166270101905 1707201817266874702576429)
              ·
                refine ⟨640200681475078013466161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1707201817266874702576429 640200681475078013466161)
                ·
                  refine ⟨480150511106308510099621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 640200681475078013466161 480150511106308510099621)
                  ·
                    refine ⟨90028220832432845643679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 480150511106308510099621 90028220832432845643679)
                    ·
                      rfl

theorem cell22_262994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_262994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_262994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_262994 prefixEnd_262994 := by exact prefixLift 262994
  have htrace : WordTrace (prefixWord ++ tailWord_262994) baseStart_262994 baseEnd_262994 := by
    simpa [prefixWord, tailWord_262994, baseEnd_262994] using wordTrace_append hprefix tailTrace_262994
  have hstable : (prefixWord ++ tailWord_262994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262994).length < 2 ^ (prefixWord ++ tailWord_262994).sum := by decide
  have hdescent : baseEnd_262994 < baseStart_262994 := by decide
  rcases family_descends (prefixWord ++ tailWord_262994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263030 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_263030 : Nat := 118140960795 + 263030 * 2 ^ 59
def prefixEnd_263030 : Nat := 4983230072969 + 3 ^ 40 * 263030 * 2
def baseEnd_263030 : Nat := 90040544368140751743569

theorem tailTrace_263030 : CollatzResearch.WordTrace tailWord_263030 prefixEnd_263030 90040544368140751743569 := by
  unfold tailWord_263030
  simp only [CollatzResearch.WordTrace]
  refine ⟨599593264818419174543159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6395661491396471195127029 599593264818419174543159)
  ·
    refine ⟨899389897227628761814739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 599593264818419174543159 899389897227628761814739)
    ·
      refine ⟨1349084845841443142722109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899389897227628761814739 1349084845841443142722109)
      ·
        refine ⟨505906817190541178520791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1349084845841443142722109 505906817190541178520791)
        ·
          refine ⟨758860225785811767781187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505906817190541178520791 758860225785811767781187)
          ·
            refine ⟨1138290338678717651671781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758860225785811767781187 1138290338678717651671781)
            ·
              refine ⟨213429438502259559688459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1138290338678717651671781 213429438502259559688459)
              ·
                refine ⟨320144157753389339532689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213429438502259559688459 320144157753389339532689)
                ·
                  refine ⟨240108118315042004649517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320144157753389339532689 240108118315042004649517)
                  ·
                    refine ⟨90040544368140751743569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240108118315042004649517 90040544368140751743569)
                    ·
                      rfl

theorem cell22_263030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_263030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263030 prefixEnd_263030 := by exact prefixLift 263030
  have htrace : WordTrace (prefixWord ++ tailWord_263030) baseStart_263030 baseEnd_263030 := by
    simpa [prefixWord, tailWord_263030, baseEnd_263030] using wordTrace_append hprefix tailTrace_263030
  have hstable : (prefixWord ++ tailWord_263030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263030).length < 2 ^ (prefixWord ++ tailWord_263030).sum := by decide
  have hdescent : baseEnd_263030 < baseStart_263030 := by decide
  rcases family_descends (prefixWord ++ tailWord_263030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263069 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_263069 : Nat := 118140960795 + 263069 * 2 ^ 59
def prefixEnd_263069 : Nat := 4983230072969 + 3 ^ 40 * 263069 * 2
def baseEnd_263069 : Nat := 90053894865157650018449

theorem tailTrace_263069 : CollatzResearch.WordTrace tailWord_263069 prefixEnd_263069 90053894865157650018449 := by
  unfold tailWord_263069
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594914683953416453360261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6396609789302277635573507 9594914683953416453360261)
  ·
    refine ⟨1799046503241265585005049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9594914683953416453360261 1799046503241265585005049)
    ·
      refine ⟨1349284877430949188753787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1799046503241265585005049 1349284877430949188753787)
      ·
        refine ⟨2023927316146423783130681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349284877430949188753787 2023927316146423783130681)
        ·
          refine ⟨1517945487109817837348011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2023927316146423783130681 1517945487109817837348011)
          ·
            refine ⟨2276918230664726756022017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517945487109817837348011 2276918230664726756022017)
            ·
              refine ⟨1707688672998545067016513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276918230664726756022017 1707688672998545067016513)
              ·
                refine ⟨1280766504748908800262385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1707688672998545067016513 1280766504748908800262385)
                ·
                  refine ⟨960574878561681600196789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280766504748908800262385 960574878561681600196789)
                  ·
                    refine ⟨90053894865157650018449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 960574878561681600196789 90053894865157650018449)
                    ·
                      rfl

theorem cell22_263069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_263069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263069 prefixEnd_263069 := by exact prefixLift 263069
  have htrace : WordTrace (prefixWord ++ tailWord_263069) baseStart_263069 baseEnd_263069 := by
    simpa [prefixWord, tailWord_263069, baseEnd_263069] using wordTrace_append hprefix tailTrace_263069
  have hstable : (prefixWord ++ tailWord_263069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263069).length < 2 ^ (prefixWord ++ tailWord_263069).sum := by decide
  have hdescent : baseEnd_263069 < baseStart_263069 := by decide
  rcases family_descends (prefixWord ++ tailWord_263069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263071 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 5]
def baseStart_263071 : Nat := 118140960795 + 263071 * 2 ^ 59
def prefixEnd_263071 : Nat := 4983230072969 + 3 ^ 40 * 263071 * 2
def baseEnd_263071 : Nat := 30018193168676770489481

theorem tailTrace_263071 : CollatzResearch.WordTrace tailWord_263071 prefixEnd_263071 30018193168676770489481 := by
  unfold tailWord_263071
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594987629946170794933067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6396658419964113863288711 9594987629946170794933067)
  ·
    refine ⟨14392481444919256192399601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9594987629946170794933067 14392481444919256192399601)
    ·
      refine ⟨10794361083689442144299701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14392481444919256192399601 10794361083689442144299701)
      ·
        refine ⟨1011971351595885201028097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10794361083689442144299701 1011971351595885201028097)
        ·
          refine ⟨758978513696913900771073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011971351595885201028097 758978513696913900771073)
          ·
            refine ⟨569233885272685425578305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758978513696913900771073 569233885272685425578305)
            ·
              refine ⟨426925413954514069183729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569233885272685425578305 426925413954514069183729)
              ·
                refine ⟨320194060465885551887797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426925413954514069183729 320194060465885551887797)
                ·
                  refine ⟨30018193168676770489481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320194060465885551887797 30018193168676770489481)
                  ·
                    rfl

theorem cell22_263071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 5].length) (baseStart_263071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263071 prefixEnd_263071 := by exact prefixLift 263071
  have htrace : WordTrace (prefixWord ++ tailWord_263071) baseStart_263071 baseEnd_263071 := by
    simpa [prefixWord, tailWord_263071, baseEnd_263071] using wordTrace_append hprefix tailTrace_263071
  have hstable : (prefixWord ++ tailWord_263071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263071).length < 2 ^ (prefixWord ++ tailWord_263071).sum := by decide
  have hdescent : baseEnd_263071 < baseStart_263071 := by decide
  rcases family_descends (prefixWord ++ tailWord_263071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263118 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_263118 : Nat := 118140960795 + 263118 * 2 ^ 59
def prefixEnd_263118 : Nat := 4983230072969 + 3 ^ 40 * 263118 * 2
def baseEnd_263118 : Nat := 90070668566537855543299

theorem tailTrace_263118 : CollatzResearch.WordTrace tailWord_263118 prefixEnd_263118 90070668566537855543299 := by
  unfold tailWord_263118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1199587732596987227736751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6397801240517265214596005 1199587732596987227736751)
  ·
    refine ⟨1799381598895480841605127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1199587732596987227736751 1799381598895480841605127)
    ·
      refine ⟨2699072398343221262407691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1799381598895480841605127 2699072398343221262407691)
      ·
        refine ⟨4048608597514831893611537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699072398343221262407691 4048608597514831893611537)
        ·
          refine ⟨3036456448136123920208653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4048608597514831893611537 3036456448136123920208653)
          ·
            refine ⟨1138671168051046470078245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3036456448136123920208653 1138671168051046470078245)
            ·
              refine ⟨213500844009571213139671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1138671168051046470078245 213500844009571213139671)
              ·
                refine ⟨320251266014356819709507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213500844009571213139671 320251266014356819709507)
                ·
                  refine ⟨480376899021535229564261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320251266014356819709507 480376899021535229564261)
                  ·
                    refine ⟨90070668566537855543299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 480376899021535229564261 90070668566537855543299)
                    ·
                      rfl

theorem cell22_263118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_263118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263118 prefixEnd_263118 := by exact prefixLift 263118
  have htrace : WordTrace (prefixWord ++ tailWord_263118) baseStart_263118 baseEnd_263118 := by
    simpa [prefixWord, tailWord_263118, baseEnd_263118] using wordTrace_append hprefix tailTrace_263118
  have hstable : (prefixWord ++ tailWord_263118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263118).length < 2 ^ (prefixWord ++ tailWord_263118).sum := by decide
  have hdescent : baseEnd_263118 < baseStart_263118 := by decide
  rcases family_descends (prefixWord ++ tailWord_263118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263133 : List Nat := [1, 4, 3, 1, 2, 1, 2, 4, 4]
def baseStart_263133 : Nat := 118140960795 + 263133 * 2 ^ 59
def prefixEnd_263133 : Nat := 4983230072969 + 3 ^ 40 * 263133 * 2
def baseEnd_263133 : Nat := 30025267791027605472751

theorem tailTrace_263133 : CollatzResearch.WordTrace tailWord_263133 prefixEnd_263133 30025267791027605472751 := by
  unfold tailWord_263133
  simp only [CollatzResearch.WordTrace]
  refine ⟨9597248955721555383690053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6398165970481036922460035 9597248955721555383690053)
  ·
    refine ⟨1799484179197791634441885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9597248955721555383690053 1799484179197791634441885)
    ·
      refine ⟨674806567199171862915707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1799484179197791634441885 674806567199171862915707)
      ·
        refine ⟨1012209850798757794373561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674806567199171862915707 1012209850798757794373561)
        ·
          refine ⟨759157388099068345780171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012209850798757794373561 759157388099068345780171)
          ·
            refine ⟨1138736082148602518670257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759157388099068345780171 1138736082148602518670257)
            ·
              refine ⟨854052061611451889002693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138736082148602518670257 854052061611451889002693)
              ·
                refine ⟨160134761552147229188005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 854052061611451889002693 160134761552147229188005)
                ·
                  refine ⟨30025267791027605472751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160134761552147229188005 30025267791027605472751)
                  ·
                    rfl

theorem cell22_263133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_263133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263133 prefixEnd_263133 := by exact prefixLift 263133
  have htrace : WordTrace (prefixWord ++ tailWord_263133) baseStart_263133 baseEnd_263133 := by
    simpa [prefixWord, tailWord_263133, baseEnd_263133] using wordTrace_append hprefix tailTrace_263133
  have hstable : (prefixWord ++ tailWord_263133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263133).length < 2 ^ (prefixWord ++ tailWord_263133).sum := by decide
  have hdescent : baseEnd_263133 < baseStart_263133 := by decide
  rcases family_descends (prefixWord ++ tailWord_263133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263193 : List Nat := [1, 2, 1, 2, 1, 1, 4, 6, 1, 3]
def baseStart_263193 : Nat := 118140960795 + 263193 * 2 ^ 59
def prefixEnd_263193 : Nat := 4983230072969 + 3 ^ 40 * 263193 * 2
def baseEnd_263193 : Nat := 90096342599262659918069

theorem tailTrace_263193 : CollatzResearch.WordTrace tailWord_263193 prefixEnd_263193 90096342599262659918069 := by
  unfold tailWord_263193
  simp only [CollatzResearch.WordTrace]
  refine ⟨9599437335504185630874233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6399624890336123753916155 9599437335504185630874233)
  ·
    refine ⟨7199578001628139223155675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9599437335504185630874233 7199578001628139223155675)
    ·
      refine ⟨10799367002442208834733513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7199578001628139223155675 10799367002442208834733513)
      ·
        refine ⟨8099525251831656626050135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10799367002442208834733513 8099525251831656626050135)
        ·
          refine ⟨12149287877747484939075203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8099525251831656626050135 12149287877747484939075203)
          ·
            refine ⟨18223931816621227408612805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12149287877747484939075203 18223931816621227408612805)
            ·
              refine ⟨3416987215616480139114901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18223931816621227408612805 3416987215616480139114901)
              ·
                refine ⟨160171275732022506521011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3416987215616480139114901 160171275732022506521011)
                ·
                  refine ⟨240256913598033759781517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160171275732022506521011 240256913598033759781517)
                  ·
                    refine ⟨90096342599262659918069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240256913598033759781517 90096342599262659918069)
                    ·
                      rfl

theorem cell22_263193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 3].length) (baseStart_263193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263193 prefixEnd_263193 := by exact prefixLift 263193
  have htrace : WordTrace (prefixWord ++ tailWord_263193) baseStart_263193 baseEnd_263193 := by
    simpa [prefixWord, tailWord_263193, baseEnd_263193] using wordTrace_append hprefix tailTrace_263193
  have hstable : (prefixWord ++ tailWord_263193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263193).length < 2 ^ (prefixWord ++ tailWord_263193).sum := by decide
  have hdescent : baseEnd_263193 < baseStart_263193 := by decide
  rcases family_descends (prefixWord ++ tailWord_263193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263281 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_263281 : Nat := 118140960795 + 263281 * 2 ^ 59
def prefixEnd_263281 : Nat := 4983230072969 + 3 ^ 40 * 263281 * 2
def baseEnd_263281 : Nat := 90126466797659763717799

theorem tailTrace_263281 : CollatzResearch.WordTrace tailWord_263281 prefixEnd_263281 90126466797659763717799 := by
  unfold tailWord_263281
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602646959185376660077697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6401764639456917773385131 9602646959185376660077697)
  ·
    refine ⟨7201985219389032495058273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9602646959185376660077697 7201985219389032495058273)
    ·
      refine ⟨5401488914541774371293705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7201985219389032495058273 5401488914541774371293705)
      ·
        refine ⟨4051116685906330778470279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5401488914541774371293705 4051116685906330778470279)
        ·
          refine ⟨6076675028859496167705419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051116685906330778470279 6076675028859496167705419)
          ·
            refine ⟨9115012543289244251558129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076675028859496167705419 9115012543289244251558129)
            ·
              refine ⟨6836259407466933188668597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9115012543289244251558129 6836259407466933188668597)
              ·
                refine ⟨640899319450024986437681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6836259407466933188668597 640899319450024986437681)
                ·
                  refine ⟨480674489587518739828261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 640899319450024986437681 480674489587518739828261)
                  ·
                    refine ⟨90126466797659763717799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 480674489587518739828261 90126466797659763717799)
                    ·
                      rfl

theorem cell22_263281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_263281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263281 prefixEnd_263281 := by exact prefixLift 263281
  have htrace : WordTrace (prefixWord ++ tailWord_263281) baseStart_263281 baseEnd_263281 := by
    simpa [prefixWord, tailWord_263281, baseEnd_263281] using wordTrace_append hprefix tailTrace_263281
  have hstable : (prefixWord ++ tailWord_263281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263281).length < 2 ^ (prefixWord ++ tailWord_263281).sum := by decide
  have hdescent : baseEnd_263281 < baseStart_263281 := by decide
  rcases family_descends (prefixWord ++ tailWord_263281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263300 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_263300 : Nat := 118140960795 + 263300 * 2 ^ 59
def prefixEnd_263300 : Nat := 4983230072969 + 3 ^ 40 * 263300 * 2
def baseEnd_263300 : Nat := 90132970885950047492741

theorem tailTrace_263300 : CollatzResearch.WordTrace tailWord_263300 prefixEnd_263300 90132970885950047492741 := by
  unfold tailWord_263300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4801669973058271452509677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6402226630744361936679569 4801669973058271452509677)
  ·
    refine ⟨1800626239896851794691129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4801669973058271452509677 1800626239896851794691129)
    ·
      refine ⟨1350469679922638846018347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1800626239896851794691129 1350469679922638846018347)
      ·
        refine ⟨2025704519883958269027521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350469679922638846018347 2025704519883958269027521)
        ·
          refine ⟨1519278389912968701770641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2025704519883958269027521 1519278389912968701770641)
          ·
            refine ⟨1139458792434726526327981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1519278389912968701770641 1139458792434726526327981)
            ·
              refine ⟨427297047163022447372993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1139458792434726526327981 427297047163022447372993)
              ·
                refine ⟨320472785372266835529745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427297047163022447372993 320472785372266835529745)
                ·
                  refine ⟨240354589029200126647309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320472785372266835529745 240354589029200126647309)
                  ·
                    refine ⟨90132970885950047492741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240354589029200126647309 90132970885950047492741)
                    ·
                      rfl

theorem cell22_263300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_263300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263300 prefixEnd_263300 := by exact prefixLift 263300
  have htrace : WordTrace (prefixWord ++ tailWord_263300) baseStart_263300 baseEnd_263300 := by
    simpa [prefixWord, tailWord_263300, baseEnd_263300] using wordTrace_append hprefix tailTrace_263300
  have hstable : (prefixWord ++ tailWord_263300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263300).length < 2 ^ (prefixWord ++ tailWord_263300).sum := by decide
  have hdescent : baseEnd_263300 < baseStart_263300 := by decide
  rcases family_descends (prefixWord ++ tailWord_263300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263328 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 3, 3]
def baseStart_263328 : Nat := 118140960795 + 263328 * 2 ^ 59
def prefixEnd_263328 : Nat := 4983230072969 + 3 ^ 40 * 263328 * 2
def baseEnd_263328 : Nat := 90142555858167307792655

theorem tailTrace_263328 : CollatzResearch.WordTrace tailWord_263328 prefixEnd_263328 90142555858167307792655 := by
  unfold tailWord_263328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4802180595007551843519319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6402907460010069124692425 4802180595007551843519319)
  ·
    refine ⟨7203270892511327765278979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4802180595007551843519319 7203270892511327765278979)
    ·
      refine ⟨10804906338766991647918469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7203270892511327765278979 10804906338766991647918469)
      ·
        refine ⟨2025919938518810933984713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10804906338766991647918469 2025919938518810933984713)
        ·
          refine ⟨1519439953889108200488535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2025919938518810933984713 1519439953889108200488535)
          ·
            refine ⟨2279159930833662300732803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519439953889108200488535 2279159930833662300732803)
            ·
              refine ⟨3418739896250493451099205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279159930833662300732803 3418739896250493451099205)
              ·
                refine ⟨641013730546967522081101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3418739896250493451099205 641013730546967522081101)
                ·
                  refine ⟨240380148955112820780413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641013730546967522081101 240380148955112820780413)
                  ·
                    refine ⟨90142555858167307792655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240380148955112820780413 90142555858167307792655)
                    ·
                      rfl

theorem cell22_263328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_263328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263328 prefixEnd_263328 := by exact prefixLift 263328
  have htrace : WordTrace (prefixWord ++ tailWord_263328) baseStart_263328 baseEnd_263328 := by
    simpa [prefixWord, tailWord_263328, baseEnd_263328] using wordTrace_append hprefix tailTrace_263328
  have hstable : (prefixWord ++ tailWord_263328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263328).length < 2 ^ (prefixWord ++ tailWord_263328).sum := by decide
  have hdescent : baseEnd_263328 < baseStart_263328 := by decide
  rcases family_descends (prefixWord ++ tailWord_263328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263358 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_263358 : Nat := 118140960795 + 263358 * 2 ^ 59
def prefixEnd_263358 : Nat := 4983230072969 + 3 ^ 40 * 263358 * 2
def baseEnd_263358 : Nat := 30050941823752409847521

theorem tailTrace_263358 : CollatzResearch.WordTrace tailWord_263358 prefixEnd_263358 30050941823752409847521 := by
  unfold tailWord_263358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200681922488302351328841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6403636919937612540420485 1200681922488302351328841)
  ·
    refine ⟨900511441866226763496631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1200681922488302351328841 900511441866226763496631)
    ·
      refine ⟨1350767162799340145244947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900511441866226763496631 1350767162799340145244947)
      ·
        refine ⟨2026150744199010217867421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350767162799340145244947 2026150744199010217867421)
        ·
          refine ⟨759806529074628831700283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2026150744199010217867421 759806529074628831700283)
          ·
            refine ⟨1139709793611943247550425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759806529074628831700283 1139709793611943247550425)
            ·
              refine ⟨854782345208957435662819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139709793611943247550425 854782345208957435662819)
              ·
                refine ⟨1282173517813436153494229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854782345208957435662819 1282173517813436153494229)
                ·
                  refine ⟨30050941823752409847521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1282173517813436153494229 30050941823752409847521)
                  ·
                    rfl

theorem cell22_263358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_263358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263358 prefixEnd_263358 := by exact prefixLift 263358
  have htrace : WordTrace (prefixWord ++ tailWord_263358) baseStart_263358 baseEnd_263358 := by
    simpa [prefixWord, tailWord_263358, baseEnd_263358] using wordTrace_append hprefix tailTrace_263358
  have hstable : (prefixWord ++ tailWord_263358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263358).length < 2 ^ (prefixWord ++ tailWord_263358).sum := by decide
  have hdescent : baseEnd_263358 < baseStart_263358 := by decide
  rcases family_descends (prefixWord ++ tailWord_263358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263386 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_263386 : Nat := 118140960795 + 263386 * 2 ^ 59
def prefixEnd_263386 : Nat := 4983230072969 + 3 ^ 40 * 263386 * 2
def baseEnd_263386 : Nat := 30054136814491496614159

theorem tailTrace_263386 : CollatzResearch.WordTrace tailWord_263386 prefixEnd_263386 30054136814491496614159 := by
  unfold tailWord_263386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2401619155951244898162503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6404317749203319728433341 2401619155951244898162503)
  ·
    refine ⟨3602428733926867347243755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2401619155951244898162503 3602428733926867347243755)
    ·
      refine ⟨5403643100890301020865633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3602428733926867347243755 5403643100890301020865633)
      ·
        refine ⟨4052732325667725765649225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5403643100890301020865633 4052732325667725765649225)
        ·
          refine ⟨3039549244250794324236919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4052732325667725765649225 3039549244250794324236919)
          ·
            refine ⟨4559323866376191486355379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039549244250794324236919 4559323866376191486355379)
            ·
              refine ⟨6838985799564287229533069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559323866376191486355379 6838985799564287229533069)
              ·
                refine ⟨2564619674836607711074901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6838985799564287229533069 2564619674836607711074901)
                ·
                  refine ⟨30054136814491496614159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2564619674836607711074901 30054136814491496614159)
                  ·
                    rfl

theorem cell22_263386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_263386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263386 prefixEnd_263386 := by exact prefixLift 263386
  have htrace : WordTrace (prefixWord ++ tailWord_263386) baseStart_263386 baseEnd_263386 := by
    simpa [prefixWord, tailWord_263386, baseEnd_263386] using wordTrace_append hprefix tailTrace_263386
  have hstable : (prefixWord ++ tailWord_263386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263386).length < 2 ^ (prefixWord ++ tailWord_263386).sum := by decide
  have hdescent : baseEnd_263386 < baseStart_263386 := by decide
  rcases family_descends (prefixWord ++ tailWord_263386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263416 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_263416 : Nat := 118140960795 + 263416 * 2 ^ 59
def prefixEnd_263416 : Nat := 4983230072969 + 3 ^ 40 * 263416 * 2
def baseEnd_263416 : Nat := 90172680056564411592385

theorem tailTrace_263416 : CollatzResearch.WordTrace tailWord_263416 prefixEnd_263416 90172680056564411592385 := by
  unfold tailWord_263416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4803785406848147358121051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6405047209130863144161401 4803785406848147358121051)
  ·
    refine ⟨7205678110272221037181577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4803785406848147358121051 7205678110272221037181577)
    ·
      refine ⟨5404258582704165777886183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7205678110272221037181577 5404258582704165777886183)
      ·
        refine ⟨8106387874056248666829275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5404258582704165777886183 8106387874056248666829275)
        ·
          refine ⟨12159581811084373000243913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8106387874056248666829275 12159581811084373000243913)
          ·
            refine ⟨9119686358313279750182935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12159581811084373000243913 9119686358313279750182935)
            ·
              refine ⟨13679529537469919625274403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9119686358313279750182935 13679529537469919625274403)
              ·
                refine ⟨20519294306204879437911605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13679529537469919625274403 20519294306204879437911605)
                ·
                  refine ⟨1923683841206707447304213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20519294306204879437911605 1923683841206707447304213)
                  ·
                    refine ⟨90172680056564411592385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1923683841206707447304213 90172680056564411592385)
                    ·
                      rfl

theorem cell22_263416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_263416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263416 prefixEnd_263416 := by exact prefixLift 263416
  have htrace : WordTrace (prefixWord ++ tailWord_263416) baseStart_263416 baseEnd_263416 := by
    simpa [prefixWord, tailWord_263416, baseEnd_263416] using wordTrace_append hprefix tailTrace_263416
  have hstable : (prefixWord ++ tailWord_263416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263416).length < 2 ^ (prefixWord ++ tailWord_263416).sum := by decide
  have hdescent : baseEnd_263416 < baseStart_263416 := by decide
  rcases family_descends (prefixWord ++ tailWord_263416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263435 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 2, 3]
def baseStart_263435 : Nat := 118140960795 + 263435 * 2 ^ 59
def prefixEnd_263435 : Nat := 4983230072969 + 3 ^ 40 * 263435 * 2
def baseEnd_263435 : Nat := 90179184144854695367327

theorem tailTrace_263435 : CollatzResearch.WordTrace tailWord_263435 prefixEnd_263435 90179184144854695367327 := by
  unfold tailWord_263435
  simp only [CollatzResearch.WordTrace]
  refine ⟨9608263800627460961183759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6405509200418307307455839 9608263800627460961183759)
  ·
    refine ⟨14412395700941191441775639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9608263800627460961183759 14412395700941191441775639)
    ·
      refine ⟨21618593551411787162663459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14412395700941191441775639 21618593551411787162663459)
      ·
        refine ⟨32427890327117680743995189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21618593551411787162663459 32427890327117680743995189)
        ·
          refine ⟨3040114718167282569749549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32427890327117680743995189 3040114718167282569749549)
          ·
            refine ⟨1140043019312730963656081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3040114718167282569749549 1140043019312730963656081)
            ·
              refine ⟨855032264484548222742061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140043019312730963656081 855032264484548222742061)
              ·
                refine ⟨320637099181705583528273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855032264484548222742061 320637099181705583528273)
                ·
                  refine ⟨240477824386279187646205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320637099181705583528273 240477824386279187646205)
                  ·
                    refine ⟨90179184144854695367327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240477824386279187646205 90179184144854695367327)
                    ·
                      rfl

theorem cell22_263435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 3].length) (baseStart_263435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263435 prefixEnd_263435 := by exact prefixLift 263435
  have htrace : WordTrace (prefixWord ++ tailWord_263435) baseStart_263435 baseEnd_263435 := by
    simpa [prefixWord, tailWord_263435, baseEnd_263435] using wordTrace_append hprefix tailTrace_263435
  have hstable : (prefixWord ++ tailWord_263435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263435).length < 2 ^ (prefixWord ++ tailWord_263435).sum := by decide
  have hdescent : baseEnd_263435 < baseStart_263435 := by decide
  rcases family_descends (prefixWord ++ tailWord_263435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263450 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_263450 : Nat := 118140960795 + 263450 * 2 ^ 59
def prefixEnd_263450 : Nat := 4983230072969 + 3 ^ 40 * 263450 * 2
def baseEnd_263450 : Nat := 90184318951399656242281

theorem tailTrace_263450 : CollatzResearch.WordTrace tailWord_263450 prefixEnd_263450 90184318951399656242281 := by
  unfold tailWord_263450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2402202723893279630744951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6405873930382079015319869 2402202723893279630744951)
  ·
    refine ⟨3603304085839919446117427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2402202723893279630744951 3603304085839919446117427)
    ·
      refine ⟨5404956128759879169176141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3603304085839919446117427 5404956128759879169176141)
      ·
        refine ⟨2026858548284954688441053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5404956128759879169176141 2026858548284954688441053)
        ·
          refine ⟨760071955606858008165395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2026858548284954688441053 760071955606858008165395)
          ·
            refine ⟨1140107933410287012248093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760071955606858008165395 1140107933410287012248093)
            ·
              refine ⟨427540475028857629593035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140107933410287012248093 427540475028857629593035)
              ·
                refine ⟨641310712543286444389553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427540475028857629593035 641310712543286444389553)
                ·
                  refine ⟨480983034407464833292165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 641310712543286444389553 480983034407464833292165)
                  ·
                    refine ⟨90184318951399656242281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 480983034407464833292165 90184318951399656242281)
                    ·
                      rfl

theorem cell22_263450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_263450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263450 prefixEnd_263450 := by exact prefixLift 263450
  have htrace : WordTrace (prefixWord ++ tailWord_263450) baseStart_263450 baseEnd_263450 := by
    simpa [prefixWord, tailWord_263450, baseEnd_263450] using wordTrace_append hprefix tailTrace_263450
  have hstable : (prefixWord ++ tailWord_263450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263450).length < 2 ^ (prefixWord ++ tailWord_263450).sum := by decide
  have hdescent : baseEnd_263450 < baseStart_263450 := by decide
  rcases family_descends (prefixWord ++ tailWord_263450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263469 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_263469 : Nat := 118140960795 + 263469 * 2 ^ 59
def prefixEnd_263469 : Nat := 4983230072969 + 3 ^ 40 * 263469 * 2
def baseEnd_263469 : Nat := 90190823039689940017223

theorem tailTrace_263469 : CollatzResearch.WordTrace tailWord_263469 prefixEnd_263469 90190823039689940017223 := by
  unfold tailWord_263469
  simp only [CollatzResearch.WordTrace]
  refine ⟨9609503882504284767921461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6406335921669523178614307 9609503882504284767921461)
  ·
    refine ⟨900890988984776696992637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9609503882504284767921461 900890988984776696992637)
    ·
      refine ⟨337834120869291261372239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 900890988984776696992637 337834120869291261372239)
      ·
        refine ⟨506751181303936892058359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337834120869291261372239 506751181303936892058359)
        ·
          refine ⟨760126771955905338087539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506751181303936892058359 760126771955905338087539)
          ·
            refine ⟨1140190157933858007131309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760126771955905338087539 1140190157933858007131309)
            ·
              refine ⟨427571309225196752674241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140190157933858007131309 427571309225196752674241)
              ·
                refine ⟨320678481918897564505681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427571309225196752674241 320678481918897564505681)
                ·
                  refine ⟨240508861439173173379261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320678481918897564505681 240508861439173173379261)
                  ·
                    refine ⟨90190823039689940017223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240508861439173173379261 90190823039689940017223)
                    ·
                      rfl

theorem cell22_263469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_263469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263469 prefixEnd_263469 := by exact prefixLift 263469
  have htrace : WordTrace (prefixWord ++ tailWord_263469) baseStart_263469 baseEnd_263469 := by
    simpa [prefixWord, tailWord_263469, baseEnd_263469] using wordTrace_append hprefix tailTrace_263469
  have hstable : (prefixWord ++ tailWord_263469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263469).length < 2 ^ (prefixWord ++ tailWord_263469).sum := by decide
  have hdescent : baseEnd_263469 < baseStart_263469 := by decide
  rcases family_descends (prefixWord ++ tailWord_263469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263493 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 5]
def baseStart_263493 : Nat := 118140960795 + 263493 * 2 ^ 59
def prefixEnd_263493 : Nat := 4983230072969 + 3 ^ 40 * 263493 * 2
def baseEnd_263493 : Nat := 30066346243387292472383

theorem tailTrace_263493 : CollatzResearch.WordTrace tailWord_263493 prefixEnd_263493 30066346243387292472383 := by
  unfold tailWord_263493
  simp only [CollatzResearch.WordTrace]
  refine ⟨9610379234417336866795133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6406919489611557911196755 9610379234417336866795133)
  ·
    refine ⟨3603892212906501325048175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9610379234417336866795133 3603892212906501325048175)
    ·
      refine ⟨5405838319359751987572263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3603892212906501325048175 5405838319359751987572263)
      ·
        refine ⟨8108757479039627981358395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5405838319359751987572263 8108757479039627981358395)
        ·
          refine ⟨12163136218559441972037593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8108757479039627981358395 12163136218559441972037593)
          ·
            refine ⟨9122352163919581479028195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12163136218559441972037593 9122352163919581479028195)
            ·
              refine ⟨13683528245879372218542293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9122352163919581479028195 13683528245879372218542293)
              ·
                refine ⟨320707693262797786372085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13683528245879372218542293 320707693262797786372085)
                ·
                  refine ⟨30066346243387292472383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320707693262797786372085 30066346243387292472383)
                  ·
                    rfl

theorem cell22_263493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_263493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263493 prefixEnd_263493 := by exact prefixLift 263493
  have htrace : WordTrace (prefixWord ++ tailWord_263493) baseStart_263493 baseEnd_263493 := by
    simpa [prefixWord, tailWord_263493, baseEnd_263493] using wordTrace_append hprefix tailTrace_263493
  have hstable : (prefixWord ++ tailWord_263493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263493).length < 2 ^ (prefixWord ++ tailWord_263493).sum := by decide
  have hdescent : baseEnd_263493 < baseStart_263493 := by decide
  rcases family_descends (prefixWord ++ tailWord_263493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263583 : List Nat := [1, 1, 2, 5, 1, 12]
def baseStart_263583 : Nat := 118140960795 + 263583 * 2 ^ 59
def prefixEnd_263583 : Nat := 4983230072969 + 3 ^ 40 * 263583 * 2
def baseEnd_263583 : Nat := 1113948735425082008233

theorem tailTrace_263583 : CollatzResearch.WordTrace tailWord_263583 prefixEnd_263583 1113948735425082008233 := by
  unfold tailWord_263583
  simp only [CollatzResearch.WordTrace]
  refine ⟨9613661804091282237571403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6409107869394188158380935 9613661804091282237571403)
  ·
    refine ⟨14420492706136923356357105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9613661804091282237571403 14420492706136923356357105)
    ·
      refine ⟨10815369529602692517267829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14420492706136923356357105 10815369529602692517267829)
      ·
        refine ⟨1013940893400252423493859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10815369529602692517267829 1013940893400252423493859)
        ·
          refine ⟨1520911340100378635240789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013940893400252423493859 1520911340100378635240789)
          ·
            refine ⟨1113948735425082008233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1520911340100378635240789 1113948735425082008233)
            ·
              rfl

theorem cell22_263583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 12].length) (baseStart_263583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263583 prefixEnd_263583 := by exact prefixLift 263583
  have htrace : WordTrace (prefixWord ++ tailWord_263583) baseStart_263583 baseEnd_263583 := by
    simpa [prefixWord, tailWord_263583, baseEnd_263583] using wordTrace_append hprefix tailTrace_263583
  have hstable : (prefixWord ++ tailWord_263583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263583).length < 2 ^ (prefixWord ++ tailWord_263583).sum := by decide
  have hdescent : baseEnd_263583 < baseStart_263583 := by decide
  rcases family_descends (prefixWord ++ tailWord_263583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263587 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 2, 3]
def baseStart_263587 : Nat := 118140960795 + 263587 * 2 ^ 59
def prefixEnd_263587 : Nat := 4983230072969 + 3 ^ 40 * 263587 * 2
def baseEnd_263587 : Nat := 90231216851176965566861

theorem tailTrace_263587 : CollatzResearch.WordTrace tailWord_263587 prefixEnd_263587 90231216851176965566861 := by
  unfold tailWord_263587
  simp only [CollatzResearch.WordTrace]
  refine ⟨9613807696076790920717015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6409205130717860613811343 9613807696076790920717015)
  ·
    refine ⟨14420711544115186381075523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9613807696076790920717015 14420711544115186381075523)
    ·
      refine ⟨21631067316172779571613285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14420711544115186381075523 21631067316172779571613285)
      ·
        refine ⟨4055825121782396169677491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21631067316172779571613285 4055825121782396169677491)
        ·
          refine ⟨6083737682673594254516237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055825121782396169677491 6083737682673594254516237)
          ·
            refine ⟨2281401631002597845443589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6083737682673594254516237 2281401631002597845443589)
            ·
              refine ⟨427762805812987096020673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2281401631002597845443589 427762805812987096020673)
              ·
                refine ⟨320822104359740322015505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427762805812987096020673 320822104359740322015505)
                ·
                  refine ⟨240616578269805241511629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320822104359740322015505 240616578269805241511629)
                  ·
                    refine ⟨90231216851176965566861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240616578269805241511629 90231216851176965566861)
                    ·
                      rfl

theorem cell22_263587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 3].length) (baseStart_263587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263587 prefixEnd_263587 := by exact prefixLift 263587
  have htrace : WordTrace (prefixWord ++ tailWord_263587) baseStart_263587 baseEnd_263587 := by
    simpa [prefixWord, tailWord_263587, baseEnd_263587] using wordTrace_append hprefix tailTrace_263587
  have hstable : (prefixWord ++ tailWord_263587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263587).length < 2 ^ (prefixWord ++ tailWord_263587).sum := by decide
  have hdescent : baseEnd_263587 < baseStart_263587 := by decide
  rcases family_descends (prefixWord ++ tailWord_263587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263649 : List Nat := [1, 2, 3, 1, 2, 3, 2, 4, 1, 3]
def baseStart_263649 : Nat := 118140960795 + 263649 * 2 ^ 59
def prefixEnd_263649 : Nat := 4983230072969 + 3 ^ 40 * 263649 * 2
def baseEnd_263649 : Nat := 90252440718229470516671

theorem tailTrace_263649 : CollatzResearch.WordTrace tailWord_263649 prefixEnd_263649 90252440718229470516671 := by
  unfold tailWord_263649
  simp only [CollatzResearch.WordTrace]
  refine ⟨9616069021852175509474001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6410712681234783672982667 9616069021852175509474001)
  ·
    refine ⟨7212051766389131632105501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9616069021852175509474001 7212051766389131632105501)
    ·
      refine ⟨2704519412395924362039563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7212051766389131632105501 2704519412395924362039563)
      ·
        refine ⟨4056779118593886543059345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704519412395924362039563 4056779118593886543059345)
        ·
          refine ⟨3042584338945414907294509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4056779118593886543059345 3042584338945414907294509)
          ·
            refine ⟨1140969127104530590235441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3042584338945414907294509 1140969127104530590235441)
            ·
              refine ⟨855726845328397942676581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140969127104530590235441 855726845328397942676581)
              ·
                refine ⟨160448783499074614251859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 855726845328397942676581 160448783499074614251859)
                ·
                  refine ⟨240673175248611921377789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160448783499074614251859 240673175248611921377789)
                  ·
                    refine ⟨90252440718229470516671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240673175248611921377789 90252440718229470516671)
                    ·
                      rfl

theorem cell22_263649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_263649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263649 prefixEnd_263649 := by exact prefixLift 263649
  have htrace : WordTrace (prefixWord ++ tailWord_263649) baseStart_263649 baseEnd_263649 := by
    simpa [prefixWord, tailWord_263649, baseEnd_263649] using wordTrace_append hprefix tailTrace_263649
  have hstable : (prefixWord ++ tailWord_263649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263649).length < 2 ^ (prefixWord ++ tailWord_263649).sum := by decide
  have hdescent : baseEnd_263649 < baseStart_263649 := by decide
  rcases family_descends (prefixWord ++ tailWord_263649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263700 : List Nat := [2, 4, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_263700 : Nat := 118140960795 + 263700 * 2 ^ 59
def prefixEnd_263700 : Nat := 4983230072969 + 3 ^ 40 * 263700 * 2
def baseEnd_263700 : Nat := 90269899060482337491515

theorem tailTrace_263700 : CollatzResearch.WordTrace tailWord_263700 prefixEnd_263700 90269899060482337491515 := by
  unfold tailWord_263700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808964572333705609790277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6411952763111607479720369 4808964572333705609790277)
  ·
    refine ⟨901680857312569801835677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4808964572333705609790277 901680857312569801835677)
    ·
      refine ⟨338130321492213675688379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 901680857312569801835677 338130321492213675688379)
      ·
        refine ⟨507195482238320513532569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338130321492213675688379 507195482238320513532569)
        ·
          refine ⟨380396611678740385149427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507195482238320513532569 380396611678740385149427)
          ·
            refine ⟨570594917518110577724141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380396611678740385149427 570594917518110577724141)
            ·
              refine ⟨213973094069291466646553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570594917518110577724141 213973094069291466646553)
              ·
                refine ⟨160479820551968599984915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213973094069291466646553 160479820551968599984915)
                ·
                  refine ⟨240719730827952899977373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160479820551968599984915 240719730827952899977373)
                  ·
                    refine ⟨90269899060482337491515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240719730827952899977373 90269899060482337491515)
                    ·
                      rfl

theorem cell22_263700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_263700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263700 prefixEnd_263700 := by exact prefixLift 263700
  have htrace : WordTrace (prefixWord ++ tailWord_263700) baseStart_263700 baseEnd_263700 := by
    simpa [prefixWord, tailWord_263700, baseEnd_263700] using wordTrace_append hprefix tailTrace_263700
  have hstable : (prefixWord ++ tailWord_263700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263700).length < 2 ^ (prefixWord ++ tailWord_263700).sum := by decide
  have hdescent : baseEnd_263700 < baseStart_263700 := by decide
  rcases family_descends (prefixWord ++ tailWord_263700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263722 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_263722 : Nat := 118140960795 + 263722 * 2 ^ 59
def prefixEnd_263722 : Nat := 4983230072969 + 3 ^ 40 * 263722 * 2
def baseEnd_263722 : Nat := 90277430110081613441447

theorem tailTrace_263722 : CollatzResearch.WordTrace tailWord_263722 prefixEnd_263722 90277430110081613441447 := by
  unfold tailWord_263722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404682887646927244220355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6412487700391805984587613 2404682887646927244220355)
  ·
    refine ⟨3607024331470390866330533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2404682887646927244220355 3607024331470390866330533)
    ·
      refine ⟨676317062150698287436975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3607024331470390866330533 676317062150698287436975)
      ·
        refine ⟨1014475593226047431155463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676317062150698287436975 1014475593226047431155463)
        ·
          refine ⟨1521713389839071146733195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014475593226047431155463 1521713389839071146733195)
          ·
            refine ⟨2282570084758606720099793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521713389839071146733195 2282570084758606720099793)
            ·
              refine ⟨1711927563568955040074845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2282570084758606720099793 1711927563568955040074845)
              ·
                refine ⟨641972836338358140028067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711927563568955040074845 641972836338358140028067)
                ·
                  refine ⟨962959254507537210042101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641972836338358140028067 962959254507537210042101)
                  ·
                    refine ⟨90277430110081613441447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 962959254507537210042101 90277430110081613441447)
                    ·
                      rfl

theorem cell22_263722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_263722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263722 prefixEnd_263722 := by exact prefixLift 263722
  have htrace : WordTrace (prefixWord ++ tailWord_263722) baseStart_263722 baseEnd_263722 := by
    simpa [prefixWord, tailWord_263722, baseEnd_263722] using wordTrace_append hprefix tailTrace_263722
  have hstable : (prefixWord ++ tailWord_263722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263722).length < 2 ^ (prefixWord ++ tailWord_263722).sum := by decide
  have hdescent : baseEnd_263722 < baseStart_263722 := by decide
  rcases family_descends (prefixWord ++ tailWord_263722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263726 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_263726 : Nat := 118140960795 + 263726 * 2 ^ 59
def prefixEnd_263726 : Nat := 4983230072969 + 3 ^ 40 * 263726 * 2
def baseEnd_263726 : Nat := 90278799391826936341435

theorem tailTrace_263726 : CollatzResearch.WordTrace tailWord_263726 prefixEnd_263726 90278799391826936341435 := by
  unfold tailWord_263726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202359680321652207503379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6412584961715478440018021 1202359680321652207503379)
  ·
    refine ⟨1803539520482478311255069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1202359680321652207503379 1803539520482478311255069)
    ·
      refine ⟨676327320180929366720651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1803539520482478311255069 676327320180929366720651)
      ·
        refine ⟨1014490980271394050080977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676327320180929366720651 1014490980271394050080977)
        ·
          refine ⟨760868235203545537560733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014490980271394050080977 760868235203545537560733)
          ·
            refine ⟨285325588201329576585275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 760868235203545537560733 285325588201329576585275)
            ·
              refine ⟨427988382301994364877913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285325588201329576585275 427988382301994364877913)
              ·
                refine ⟨320991286726495773658435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427988382301994364877913 320991286726495773658435)
                ·
                  refine ⟨481486930089743660487653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320991286726495773658435 481486930089743660487653)
                  ·
                    refine ⟨90278799391826936341435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 481486930089743660487653 90278799391826936341435)
                    ·
                      rfl

theorem cell22_263726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_263726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263726 prefixEnd_263726 := by exact prefixLift 263726
  have htrace : WordTrace (prefixWord ++ tailWord_263726) baseStart_263726 baseEnd_263726 := by
    simpa [prefixWord, tailWord_263726, baseEnd_263726] using wordTrace_append hprefix tailTrace_263726
  have hstable : (prefixWord ++ tailWord_263726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263726).length < 2 ^ (prefixWord ++ tailWord_263726).sum := by decide
  have hdescent : baseEnd_263726 < baseStart_263726 := by decide
  rcases family_descends (prefixWord ++ tailWord_263726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263735 : List Nat := [1, 1, 3, 1, 2, 4, 2, 8]
def baseStart_263735 : Nat := 118140960795 + 263735 * 2 ^ 59
def prefixEnd_263735 : Nat := 4983230072969 + 3 ^ 40 * 263735 * 2
def baseEnd_263735 : Nat := 10031320030639323651823

theorem tailTrace_263735 : CollatzResearch.WordTrace tailWord_263735 prefixEnd_263735 10031320030639323651823 := by
  unfold tailWord_263735
  simp only [CollatzResearch.WordTrace]
  refine ⟨9619205699540612197104659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6412803799693741464736439 9619205699540612197104659)
  ·
    refine ⟨14428808549310918295656989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9619205699540612197104659 14428808549310918295656989)
    ·
      refine ⟨5410803205991594360871371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14428808549310918295656989 5410803205991594360871371)
      ·
        refine ⟨8116204808987391541307057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5410803205991594360871371 8116204808987391541307057)
        ·
          refine ⟨6087153606740543655980293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8116204808987391541307057 6087153606740543655980293)
          ·
            refine ⟨1141341301263851935496305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6087153606740543655980293 1141341301263851935496305)
            ·
              refine ⟨856005975947888951622229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141341301263851935496305 856005975947888951622229)
              ·
                refine ⟨10031320030639323651823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 856005975947888951622229 10031320030639323651823)
                ·
                  rfl

theorem cell22_263735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 8].length) (baseStart_263735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263735 prefixEnd_263735 := by exact prefixLift 263735
  have htrace : WordTrace (prefixWord ++ tailWord_263735) baseStart_263735 baseEnd_263735 := by
    simpa [prefixWord, tailWord_263735, baseEnd_263735] using wordTrace_append hprefix tailTrace_263735
  have hstable : (prefixWord ++ tailWord_263735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263735).length < 2 ^ (prefixWord ++ tailWord_263735).sum := by decide
  have hdescent : baseEnd_263735 < baseStart_263735 := by decide
  rcases family_descends (prefixWord ++ tailWord_263735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263737 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_263737 : Nat := 118140960795 + 263737 * 2 ^ 59
def prefixEnd_263737 : Nat := 4983230072969 + 3 ^ 40 * 263737 * 2
def baseEnd_263737 : Nat := 90282564916626574316401

theorem tailTrace_263737 : CollatzResearch.WordTrace tailWord_263737 prefixEnd_263737 90282564916626574316401 := by
  unfold tailWord_263737
  simp only [CollatzResearch.WordTrace]
  refine ⟨9619278645533366538677465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6412852430355577692451643 9619278645533366538677465)
  ·
    refine ⟨7214458984150024904008099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9619278645533366538677465 7214458984150024904008099)
    ·
      refine ⟨10821688476225037356012149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7214458984150024904008099 10821688476225037356012149)
      ·
        refine ⟨1014533294646097252126139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10821688476225037356012149 1014533294646097252126139)
        ·
          refine ⟨1521799941969145878189209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014533294646097252126139 1521799941969145878189209)
          ·
            refine ⟨1141349956476859408641907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521799941969145878189209 1141349956476859408641907)
            ·
              refine ⟨1712024934715289112962861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141349956476859408641907 1712024934715289112962861)
              ·
                refine ⟨642009350518233417361073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712024934715289112962861 642009350518233417361073)
                ·
                  refine ⟨481507012888675063020805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642009350518233417361073 481507012888675063020805)
                  ·
                    refine ⟨90282564916626574316401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 481507012888675063020805 90282564916626574316401)
                    ·
                      rfl

theorem cell22_263737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_263737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263737 prefixEnd_263737 := by exact prefixLift 263737
  have htrace : WordTrace (prefixWord ++ tailWord_263737) baseStart_263737 baseEnd_263737 := by
    simpa [prefixWord, tailWord_263737, baseEnd_263737] using wordTrace_append hprefix tailTrace_263737
  have hstable : (prefixWord ++ tailWord_263737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263737).length < 2 ^ (prefixWord ++ tailWord_263737).sum := by decide
  have hdescent : baseEnd_263737 < baseStart_263737 := by decide
  rcases family_descends (prefixWord ++ tailWord_263737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263784 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 5, 3]
def baseStart_263784 : Nat := 118140960795 + 263784 * 2 ^ 59
def prefixEnd_263784 : Nat := 4983230072969 + 3 ^ 40 * 263784 * 2
def baseEnd_263784 : Nat := 90298653977134118391257

theorem tailTrace_263784 : CollatzResearch.WordTrace tailWord_263784 prefixEnd_263784 90298653977134118391257 := by
  unfold tailWord_263784
  simp only [CollatzResearch.WordTrace]
  refine ⟨4810496438181546782819203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6413995250908729043758937 4810496438181546782819203)
  ·
    refine ⟨7215744657272320174228805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4810496438181546782819203 7215744657272320174228805)
    ·
      refine ⟨1352952123238560032667901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7215744657272320174228805 1352952123238560032667901)
      ·
        refine ⟨507357046214460012250463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1352952123238560032667901 507357046214460012250463)
        ·
          refine ⟨761035569321690018375695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507357046214460012250463 761035569321690018375695)
          ·
            refine ⟨1141553353982535027563543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761035569321690018375695 1141553353982535027563543)
            ·
              refine ⟨1712330030973802541345315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141553353982535027563543 1712330030973802541345315)
              ·
                refine ⟨2568495046460703812017973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712330030973802541345315 2568495046460703812017973)
                ·
                  refine ⟨240796410605690982376685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2568495046460703812017973 240796410605690982376685)
                  ·
                    refine ⟨90298653977134118391257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240796410605690982376685 90298653977134118391257)
                    ·
                      rfl

theorem cell22_263784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_263784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263784 prefixEnd_263784 := by exact prefixLift 263784
  have htrace : WordTrace (prefixWord ++ tailWord_263784) baseStart_263784 baseEnd_263784 := by
    simpa [prefixWord, tailWord_263784, baseEnd_263784] using wordTrace_append hprefix tailTrace_263784
  have hstable : (prefixWord ++ tailWord_263784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263784).length < 2 ^ (prefixWord ++ tailWord_263784).sum := by decide
  have hdescent : baseEnd_263784 < baseStart_263784 := by decide
  rcases family_descends (prefixWord ++ tailWord_263784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263801 : List Nat := [1, 2, 1, 3, 3, 1, 4, 3, 1, 3]
def baseStart_263801 : Nat := 118140960795 + 263801 * 2 ^ 59
def prefixEnd_263801 : Nat := 4983230072969 + 3 ^ 40 * 263801 * 2
def baseEnd_263801 : Nat := 90304473424551740716205

theorem tailTrace_263801 : CollatzResearch.WordTrace tailWord_263801 prefixEnd_263801 90304473424551740716205 := by
  unfold tailWord_263801
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621612917301505469007257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6414408611534336979338171 9621612917301505469007257)
  ·
    refine ⟨7216209687976129101755443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9621612917301505469007257 7216209687976129101755443)
    ·
      refine ⟨10824314531964193652633165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7216209687976129101755443 10824314531964193652633165)
      ·
        refine ⟨4059117949486572619737437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10824314531964193652633165 4059117949486572619737437)
        ·
          refine ⟨1522169231057464732401539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4059117949486572619737437 1522169231057464732401539)
          ·
            refine ⟨2283253846586197098602309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522169231057464732401539 2283253846586197098602309)
            ·
              refine ⟨428110096234911955987933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2283253846586197098602309 428110096234911955987933)
              ·
                refine ⟨160541286088091983495475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428110096234911955987933 160541286088091983495475)
                ·
                  refine ⟨240811929132137975243213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160541286088091983495475 240811929132137975243213)
                  ·
                    refine ⟨90304473424551740716205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240811929132137975243213 90304473424551740716205)
                    ·
                      rfl

theorem cell22_263801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 3].length) (baseStart_263801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263801 prefixEnd_263801 := by exact prefixLift 263801
  have htrace : WordTrace (prefixWord ++ tailWord_263801) baseStart_263801 baseEnd_263801 := by
    simpa [prefixWord, tailWord_263801, baseEnd_263801] using wordTrace_append hprefix tailTrace_263801
  have hstable : (prefixWord ++ tailWord_263801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263801).length < 2 ^ (prefixWord ++ tailWord_263801).sum := by decide
  have hdescent : baseEnd_263801 < baseStart_263801 := by decide
  rcases family_descends (prefixWord ++ tailWord_263801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263844 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_263844 : Nat := 118140960795 + 263844 * 2 ^ 59
def prefixEnd_263844 : Nat := 4983230072969 + 3 ^ 40 * 263844 * 2
def baseEnd_263844 : Nat := 90319193203313961891073

theorem tailTrace_263844 : CollatzResearch.WordTrace tailWord_263844 prefixEnd_263844 90319193203313961891073 := by
  unfold tailWord_263844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811590628072861906411293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6415454170763815875215057 4811590628072861906411293)
  ·
    refine ⟨1804346485527323214904235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4811590628072861906411293 1804346485527323214904235)
    ·
      refine ⟨2706519728290984822356353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804346485527323214904235 2706519728290984822356353)
      ·
        refine ⟨2029889796218238616767265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2706519728290984822356353 2029889796218238616767265)
        ·
          refine ⟨1522417347163678962575449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2029889796218238616767265 1522417347163678962575449)
          ·
            refine ⟨1141813010372759221931587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522417347163678962575449 1141813010372759221931587)
            ·
              refine ⟨1712719515559138832897381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141813010372759221931587 1712719515559138832897381)
              ·
                refine ⟨321134909167338531168259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1712719515559138832897381 321134909167338531168259)
                ·
                  refine ⟨481702363751007796752389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321134909167338531168259 481702363751007796752389)
                  ·
                    refine ⟨90319193203313961891073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 481702363751007796752389 90319193203313961891073)
                    ·
                      rfl

theorem cell22_263844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_263844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263844 prefixEnd_263844 := by exact prefixLift 263844
  have htrace : WordTrace (prefixWord ++ tailWord_263844) baseStart_263844 baseEnd_263844 := by
    simpa [prefixWord, tailWord_263844, baseEnd_263844] using wordTrace_append hprefix tailTrace_263844
  have hstable : (prefixWord ++ tailWord_263844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263844).length < 2 ^ (prefixWord ++ tailWord_263844).sum := by decide
  have hdescent : baseEnd_263844 < baseStart_263844 := by decide
  rcases family_descends (prefixWord ++ tailWord_263844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263936 : List Nat := [2, 1, 1, 2, 1, 1, 2, 8, 1, 3]
def baseStart_263936 : Nat := 118140960795 + 263936 * 2 ^ 59
def prefixEnd_263936 : Nat := 4983230072969 + 3 ^ 40 * 263936 * 2
def baseEnd_263936 : Nat := 90350686683456388590791

theorem tailTrace_263936 : CollatzResearch.WordTrace tailWord_263936 prefixEnd_263936 90350686683456388590791 := by
  unfold tailWord_263936
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813268385906211762585831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6417691181208282350114441 4813268385906211762585831)
  ·
    refine ⟨7219902578859317643878747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4813268385906211762585831 7219902578859317643878747)
    ·
      refine ⟨10829853868288976465818121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7219902578859317643878747 10829853868288976465818121)
      ·
        refine ⟨8122390401216732349363591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10829853868288976465818121 8122390401216732349363591)
        ·
          refine ⟨12183585601825098524045387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8122390401216732349363591 12183585601825098524045387)
          ·
            refine ⟨18275378402737647786068081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12183585601825098524045387 18275378402737647786068081)
            ·
              refine ⟨13706533802053235839551061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18275378402737647786068081 13706533802053235839551061)
              ·
                refine ⟨160623442992811357494739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13706533802053235839551061 160623442992811357494739)
                ·
                  refine ⟨240935164489217036242109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160623442992811357494739 240935164489217036242109)
                  ·
                    refine ⟨90350686683456388590791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240935164489217036242109 90350686683456388590791)
                    ·
                      rfl

theorem cell22_263936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 3].length) (baseStart_263936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263936 prefixEnd_263936 := by exact prefixLift 263936
  have htrace : WordTrace (prefixWord ++ tailWord_263936) baseStart_263936 baseEnd_263936 := by
    simpa [prefixWord, tailWord_263936, baseEnd_263936] using wordTrace_append hprefix tailTrace_263936
  have hstable : (prefixWord ++ tailWord_263936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263936).length < 2 ^ (prefixWord ++ tailWord_263936).sum := by decide
  have hdescent : baseEnd_263936 < baseStart_263936 := by decide
  rcases family_descends (prefixWord ++ tailWord_263936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263947 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 1, 7]
def baseStart_263947 : Nat := 118140960795 + 263947 * 2 ^ 59
def prefixEnd_263947 : Nat := 4983230072969 + 3 ^ 40 * 263947 * 2
def baseEnd_263947 : Nat := 90354452208256026565757

theorem tailTrace_263947 : CollatzResearch.WordTrace tailWord_263947 prefixEnd_263947 90354452208256026565757 := by
  unfold tailWord_263947
  simp only [CollatzResearch.WordTrace]
  refine ⟨9626937974772572403822095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6417958649848381602548063 9626937974772572403822095)
  ·
    refine ⟨14440406962158858605733143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9626937974772572403822095 14440406962158858605733143)
    ·
      refine ⟨21660610443238287908599715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14440406962158858605733143 21660610443238287908599715)
      ·
        refine ⟨32490915664857431862899573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21660610443238287908599715 32490915664857431862899573)
        ·
          refine ⟨3046023343580384237146835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32490915664857431862899573 3046023343580384237146835)
          ·
            refine ⟨4569035015370576355720253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046023343580384237146835 4569035015370576355720253)
            ·
              refine ⟨1713388130763966133395095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4569035015370576355720253 1713388130763966133395095)
              ·
                refine ⟨2570082196145949200092643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713388130763966133395095 2570082196145949200092643)
                ·
                  refine ⟨3855123294218923800138965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570082196145949200092643 3855123294218923800138965)
                  ·
                    refine ⟨90354452208256026565757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3855123294218923800138965 90354452208256026565757)
                    ·
                      rfl

theorem cell22_263947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_263947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263947 prefixEnd_263947 := by exact prefixLift 263947
  have htrace : WordTrace (prefixWord ++ tailWord_263947) baseStart_263947 baseEnd_263947 := by
    simpa [prefixWord, tailWord_263947, baseEnd_263947] using wordTrace_append hprefix tailTrace_263947
  have hstable : (prefixWord ++ tailWord_263947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263947).length < 2 ^ (prefixWord ++ tailWord_263947).sum := by decide
  have hdescent : baseEnd_263947 < baseStart_263947 := by decide
  rcases family_descends (prefixWord ++ tailWord_263947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263994 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_263994 : Nat := 118140960795 + 263994 * 2 ^ 59
def prefixEnd_263994 : Nat := 4983230072969 + 3 ^ 40 * 263994 * 2
def baseEnd_263994 : Nat := 30123513756254523546871

theorem tailTrace_263994 : CollatzResearch.WordTrace tailWord_263994 prefixEnd_263994 30123513756254523546871 := by
  unfold tailWord_263994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2407163051400574857695759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6419101470401532953855357 2407163051400574857695759)
  ·
    refine ⟨3610744577100862286543639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2407163051400574857695759 3610744577100862286543639)
    ·
      refine ⟨5416116865651293429815459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610744577100862286543639 5416116865651293429815459)
      ·
        refine ⟨8124175298476940144723189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416116865651293429815459 8124175298476940144723189)
        ·
          refine ⟨761641434232213138567799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8124175298476940144723189 761641434232213138567799)
          ·
            refine ⟨1142462151348319707851699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761641434232213138567799 1142462151348319707851699)
            ·
              refine ⟨1713693227022479561777549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142462151348319707851699 1713693227022479561777549)
              ·
                refine ⟨642634960133429835666581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1713693227022479561777549 642634960133429835666581)
                ·
                  refine ⟨30123513756254523546871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 642634960133429835666581 30123513756254523546871)
                  ·
                    rfl

theorem cell22_263994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_263994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_263994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_263994 prefixEnd_263994 := by exact prefixLift 263994
  have htrace : WordTrace (prefixWord ++ tailWord_263994) baseStart_263994 baseEnd_263994 := by
    simpa [prefixWord, tailWord_263994, baseEnd_263994] using wordTrace_append hprefix tailTrace_263994
  have hstable : (prefixWord ++ tailWord_263994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263994).length < 2 ^ (prefixWord ++ tailWord_263994).sum := by decide
  have hdescent : baseEnd_263994 < baseStart_263994 := by decide
  rcases family_descends (prefixWord ++ tailWord_263994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264013 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_264013 : Nat := 118140960795 + 264013 * 2 ^ 59
def prefixEnd_264013 : Nat := 4983230072969 + 3 ^ 40 * 264013 * 2
def baseEnd_264013 : Nat := 90377045357053854415555

theorem tailTrace_264013 : CollatzResearch.WordTrace tailWord_264013 prefixEnd_264013 90377045357053854415555 := by
  unfold tailWord_264013
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629345192533465675724693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6419563461688977117149795 9629345192533465675724693)
  ·
    refine ⟨451375555900006203549595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9629345192533465675724693 451375555900006203549595)
    ·
      refine ⟨677063333850009305324393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451375555900006203549595 677063333850009305324393)
      ·
        refine ⟨507797500387506978993295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677063333850009305324393 507797500387506978993295)
        ·
          refine ⟨761696250581260468489943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507797500387506978993295 761696250581260468489943)
          ·
            refine ⟨1142544375871890702734915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761696250581260468489943 1142544375871890702734915)
            ·
              refine ⟨1713816563807836054102373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142544375871890702734915 1713816563807836054102373)
              ·
                refine ⟨321340605713969260144195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1713816563807836054102373 321340605713969260144195)
                ·
                  refine ⟨482010908570953890216293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321340605713969260144195 482010908570953890216293)
                  ·
                    refine ⟨90377045357053854415555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482010908570953890216293 90377045357053854415555)
                    ·
                      rfl

theorem cell22_264013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_264013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264013 prefixEnd_264013 := by exact prefixLift 264013
  have htrace : WordTrace (prefixWord ++ tailWord_264013) baseStart_264013 baseEnd_264013 := by
    simpa [prefixWord, tailWord_264013, baseEnd_264013] using wordTrace_append hprefix tailTrace_264013
  have hstable : (prefixWord ++ tailWord_264013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264013).length < 2 ^ (prefixWord ++ tailWord_264013).sum := by decide
  have hdescent : baseEnd_264013 < baseStart_264013 := by decide
  rcases family_descends (prefixWord ++ tailWord_264013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264099 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 2, 5]
def baseStart_264099 : Nat := 118140960795 + 264099 * 2 ^ 59
def prefixEnd_264099 : Nat := 4983230072969 + 3 ^ 40 * 264099 * 2
def baseEnd_264099 : Nat := 90406484914578296765291

theorem tailTrace_264099 : CollatzResearch.WordTrace tailWord_264099 prefixEnd_264099 90406484914578296765291 := by
  unfold tailWord_264099
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632481870221902363355351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6421654580147934908903567 9632481870221902363355351)
  ·
    refine ⟨14448722805332853545033027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9632481870221902363355351 14448722805332853545033027)
    ·
      refine ⟨21673084207999280317549541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14448722805332853545033027 21673084207999280317549541)
      ·
        refine ⟨4063703288999865059540539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21673084207999280317549541 4063703288999865059540539)
        ·
          refine ⟨6095554933499797589310809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063703288999865059540539 6095554933499797589310809)
          ·
            refine ⟨4571666200124848191983107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6095554933499797589310809 4571666200124848191983107)
            ·
              refine ⟨6857499300187272287974661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4571666200124848191983107 6857499300187272287974661)
              ·
                refine ⟨1285781118785113553995249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6857499300187272287974661 1285781118785113553995249)
                ·
                  refine ⟨964335839088835165496437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1285781118785113553995249 964335839088835165496437)
                  ·
                    refine ⟨90406484914578296765291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 964335839088835165496437 90406484914578296765291)
                    ·
                      rfl

theorem cell22_264099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_264099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264099 prefixEnd_264099 := by exact prefixLift 264099
  have htrace : WordTrace (prefixWord ++ tailWord_264099) baseStart_264099 baseEnd_264099 := by
    simpa [prefixWord, tailWord_264099, baseEnd_264099] using wordTrace_append hprefix tailTrace_264099
  have hstable : (prefixWord ++ tailWord_264099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264099).length < 2 ^ (prefixWord ++ tailWord_264099).sum := by decide
  have hdescent : baseEnd_264099 < baseStart_264099 := by decide
  rcases family_descends (prefixWord ++ tailWord_264099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264148 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_264148 : Nat := 118140960795 + 264148 * 2 ^ 59
def prefixEnd_264148 : Nat := 4983230072969 + 3 ^ 40 * 264148 * 2
def baseEnd_264148 : Nat := 90423258615958502290141

theorem tailTrace_264148 : CollatzResearch.WordTrace tailWord_264148 prefixEnd_264148 90423258615958502290141 := by
  unfold tailWord_264148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4817134523522191865944549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6422846031362922487926065 4817134523522191865944549)
  ·
    refine ⟨903212723160410974864603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4817134523522191865944549 903212723160410974864603)
    ·
      refine ⟨1354819084740616462296905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 903212723160410974864603 1354819084740616462296905)
      ·
        refine ⟨1016114313555462346722679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1354819084740616462296905 1016114313555462346722679)
        ·
          refine ⟨1524171470333193520084019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016114313555462346722679 1524171470333193520084019)
          ·
            refine ⟨2286257205499790280126029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524171470333193520084019 2286257205499790280126029)
            ·
              refine ⟨857346452062421355047261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2286257205499790280126029 857346452062421355047261)
              ·
                refine ⟨321504919523408008142723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857346452062421355047261 321504919523408008142723)
                ·
                  refine ⟨482257379285112012214085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321504919523408008142723 482257379285112012214085)
                  ·
                    refine ⟨90423258615958502290141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482257379285112012214085 90423258615958502290141)
                    ·
                      rfl

theorem cell22_264148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_264148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264148 prefixEnd_264148 := by exact prefixLift 264148
  have htrace : WordTrace (prefixWord ++ tailWord_264148) baseStart_264148 baseEnd_264148 := by
    simpa [prefixWord, tailWord_264148, baseEnd_264148] using wordTrace_append hprefix tailTrace_264148
  have hstable : (prefixWord ++ tailWord_264148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264148).length < 2 ^ (prefixWord ++ tailWord_264148).sum := by decide
  have hdescent : baseEnd_264148 < baseStart_264148 := by decide
  rcases family_descends (prefixWord ++ tailWord_264148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264163 : List Nat := [1, 1, 1, 6, 1, 2, 2, 4, 4]
def baseStart_264163 : Nat := 118140960795 + 264163 * 2 ^ 59
def prefixEnd_264163 : Nat := 4983230072969 + 3 ^ 40 * 264163 * 2
def baseEnd_264163 : Nat := 30142797807501154388365

theorem tailTrace_264163 : CollatzResearch.WordTrace tailWord_264163 prefixEnd_264163 30142797807501154388365 := by
  unfold tailWord_264163
  simp only [CollatzResearch.WordTrace]
  refine ⟨9634816141990041293685143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6423210761326694195790095 9634816141990041293685143)
  ·
    refine ⟨14452224212985061940527715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9634816141990041293685143 14452224212985061940527715)
    ·
      refine ⟨21678336319477592910791573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14452224212985061940527715 21678336319477592910791573)
      ·
        refine ⟨1016172014975512167693355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21678336319477592910791573 1016172014975512167693355)
        ·
          refine ⟨1524258022463268251540033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016172014975512167693355 1524258022463268251540033)
          ·
            refine ⟨1143193516847451188655025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1524258022463268251540033 1143193516847451188655025)
            ·
              refine ⟨857395137635588391491269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1143193516847451188655025 857395137635588391491269)
              ·
                refine ⟨160761588306672823404613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 857395137635588391491269 160761588306672823404613)
                ·
                  refine ⟨30142797807501154388365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160761588306672823404613 30142797807501154388365)
                  ·
                    rfl

theorem cell22_264163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 4].length) (baseStart_264163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264163 prefixEnd_264163 := by exact prefixLift 264163
  have htrace : WordTrace (prefixWord ++ tailWord_264163) baseStart_264163 baseEnd_264163 := by
    simpa [prefixWord, tailWord_264163, baseEnd_264163] using wordTrace_append hprefix tailTrace_264163
  have hstable : (prefixWord ++ tailWord_264163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264163).length < 2 ^ (prefixWord ++ tailWord_264163).sum := by decide
  have hdescent : baseEnd_264163 < baseStart_264163 := by decide
  rcases family_descends (prefixWord ++ tailWord_264163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264281 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 6]
def baseStart_264281 : Nat := 118140960795 + 264281 * 2 ^ 59
def prefixEnd_264281 : Nat := 4983230072969 + 3 ^ 40 * 264281 * 2
def baseEnd_264281 : Nat := 30156262411330162904911

theorem tailTrace_264281 : CollatzResearch.WordTrace tailWord_264281 prefixEnd_264281 30156262411330162904911 := by
  unfold tailWord_264281
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639119955562547446480697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6426079970375031630987131 9639119955562547446480697)
  ·
    refine ⟨7229339966671910584860523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9639119955562547446480697 7229339966671910584860523)
    ·
      refine ⟨10844009950007865877290785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229339966671910584860523 10844009950007865877290785)
      ·
        refine ⟨8133007462505899407968089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10844009950007865877290785 8133007462505899407968089)
        ·
          refine ⟨6099755596879424555976067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8133007462505899407968089 6099755596879424555976067)
          ·
            refine ⟨9149633395319136833964101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099755596879424555976067 9149633395319136833964101)
            ·
              refine ⟨1715556261622338156368269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9149633395319136833964101 1715556261622338156368269)
              ·
                refine ⟨643333598108376808638101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1715556261622338156368269 643333598108376808638101)
                ·
                  refine ⟨30156262411330162904911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 643333598108376808638101 30156262411330162904911)
                  ·
                    rfl

theorem cell22_264281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_264281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264281 prefixEnd_264281 := by exact prefixLift 264281
  have htrace : WordTrace (prefixWord ++ tailWord_264281) baseStart_264281 baseEnd_264281 := by
    simpa [prefixWord, tailWord_264281, baseEnd_264281] using wordTrace_append hprefix tailTrace_264281
  have hstable : (prefixWord ++ tailWord_264281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264281).length < 2 ^ (prefixWord ++ tailWord_264281).sum := by decide
  have hdescent : baseEnd_264281 < baseStart_264281 := by decide
  rcases family_descends (prefixWord ++ tailWord_264281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264285 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_264285 : Nat := 118140960795 + 264285 * 2 ^ 59
def prefixEnd_264285 : Nat := 4983230072969 + 3 ^ 40 * 264285 * 2
def baseEnd_264285 : Nat := 90470156515735811614721

theorem tailTrace_264285 : CollatzResearch.WordTrace tailWord_264285 prefixEnd_264285 90470156515735811614721 := by
  unfold tailWord_264285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639265847548056129626309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6426177231698704086417539 9639265847548056129626309)
  ·
    refine ⟨1807362346415260524304933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9639265847548056129626309 1807362346415260524304933)
    ·
      refine ⟨338880439952861348307175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1807362346415260524304933 338880439952861348307175)
      ·
        refine ⟨508320659929292022460763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338880439952861348307175 508320659929292022460763)
        ·
          refine ⟨762480989893938033691145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508320659929292022460763 762480989893938033691145)
          ·
            refine ⟨571860742420453525268359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762480989893938033691145 571860742420453525268359)
            ·
              refine ⟨857791113630680287902539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571860742420453525268359 857791113630680287902539)
              ·
                refine ⟨1286686670446020431853809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857791113630680287902539 1286686670446020431853809)
                ·
                  refine ⟨965015002834515323890357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286686670446020431853809 965015002834515323890357)
                  ·
                    refine ⟨90470156515735811614721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 965015002834515323890357 90470156515735811614721)
                    ·
                      rfl

theorem cell22_264285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_264285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264285 prefixEnd_264285 := by exact prefixLift 264285
  have htrace : WordTrace (prefixWord ++ tailWord_264285) baseStart_264285 baseEnd_264285 := by
    simpa [prefixWord, tailWord_264285, baseEnd_264285] using wordTrace_append hprefix tailTrace_264285
  have hstable : (prefixWord ++ tailWord_264285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264285).length < 2 ^ (prefixWord ++ tailWord_264285).sum := by decide
  have hdescent : baseEnd_264285 < baseStart_264285 := by decide
  rcases family_descends (prefixWord ++ tailWord_264285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264313 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_264313 : Nat := 118140960795 + 264313 * 2 ^ 59
def prefixEnd_264313 : Nat := 4983230072969 + 3 ^ 40 * 264313 * 2
def baseEnd_264313 : Nat := 90479741487953071914635

theorem tailTrace_264313 : CollatzResearch.WordTrace tailWord_264313 prefixEnd_264313 90479741487953071914635 := by
  unfold tailWord_264313
  simp only [CollatzResearch.WordTrace]
  refine ⟨9640287091446616911645593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6426858060964411274430395 9640287091446616911645593)
  ·
    refine ⟨7230215318584962683734195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9640287091446616911645593 7230215318584962683734195)
    ·
      refine ⟨10845322977877444025601293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7230215318584962683734195 10845322977877444025601293)
      ·
        refine ⟨4066996116704041509600485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10845322977877444025601293 4066996116704041509600485)
        ·
          refine ⟨762561771882007783050091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4066996116704041509600485 762561771882007783050091)
          ·
            refine ⟨1143842657823011674575137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762561771882007783050091 1143842657823011674575137)
            ·
              refine ⟨857881993367258755931353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1143842657823011674575137 857881993367258755931353)
              ·
                refine ⟨643411495025444066948515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857881993367258755931353 643411495025444066948515)
                ·
                  refine ⟨965117242538166100422773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643411495025444066948515 965117242538166100422773)
                  ·
                    refine ⟨90479741487953071914635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 965117242538166100422773 90479741487953071914635)
                    ·
                      rfl

theorem cell22_264313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_264313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264313 prefixEnd_264313 := by exact prefixLift 264313
  have htrace : WordTrace (prefixWord ++ tailWord_264313) baseStart_264313 baseEnd_264313 := by
    simpa [prefixWord, tailWord_264313, baseEnd_264313] using wordTrace_append hprefix tailTrace_264313
  have hstable : (prefixWord ++ tailWord_264313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264313).length < 2 ^ (prefixWord ++ tailWord_264313).sum := by decide
  have hdescent : baseEnd_264313 < baseStart_264313 := by decide
  rcases family_descends (prefixWord ++ tailWord_264313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264317 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_264317 : Nat := 118140960795 + 264317 * 2 ^ 59
def prefixEnd_264317 : Nat := 4983230072969 + 3 ^ 40 * 264317 * 2
def baseEnd_264317 : Nat := 90481110769698394814623

theorem tailTrace_264317 : CollatzResearch.WordTrace tailWord_264317 prefixEnd_264317 90481110769698394814623 := by
  unfold tailWord_264317
  simp only [CollatzResearch.WordTrace]
  refine ⟨9640432983432125594791205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6426955322288083729860803 9640432983432125594791205)
  ·
    refine ⟨1807581184393523549023351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9640432983432125594791205 1807581184393523549023351)
    ·
      refine ⟨2711371776590285323535027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1807581184393523549023351 2711371776590285323535027)
      ·
        refine ⟨4067057664885427985302541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2711371776590285323535027 4067057664885427985302541)
        ·
          refine ⟨1525146624332035494488453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4067057664885427985302541 1525146624332035494488453)
          ·
            refine ⟨285964992062256655216585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1525146624332035494488453 285964992062256655216585)
            ·
              refine ⟨214473744046692491412439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285964992062256655216585 214473744046692491412439)
              ·
                refine ⟨321710616070038737118659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214473744046692491412439 321710616070038737118659)
                ·
                  refine ⟨482565924105058105677989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321710616070038737118659 482565924105058105677989)
                  ·
                    refine ⟨90481110769698394814623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482565924105058105677989 90481110769698394814623)
                    ·
                      rfl

theorem cell22_264317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_264317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264317 prefixEnd_264317 := by exact prefixLift 264317
  have htrace : WordTrace (prefixWord ++ tailWord_264317) baseStart_264317 baseEnd_264317 := by
    simpa [prefixWord, tailWord_264317, baseEnd_264317] using wordTrace_append hprefix tailTrace_264317
  have hstable : (prefixWord ++ tailWord_264317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264317).length < 2 ^ (prefixWord ++ tailWord_264317).sum := by decide
  have hdescent : baseEnd_264317 < baseStart_264317 := by decide
  rcases family_descends (prefixWord ++ tailWord_264317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264330 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_264330 : Nat := 118140960795 + 264330 * 2 ^ 59
def prefixEnd_264330 : Nat := 4983230072969 + 3 ^ 40 * 264330 * 2
def baseEnd_264330 : Nat := 90485560935370694239583

theorem tailTrace_264330 : CollatzResearch.WordTrace tailWord_264330 prefixEnd_264330 90485560935370694239583 := by
  unfold tailWord_264330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2410226783096257203753611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6427271421590019210009629 2410226783096257203753611)
  ·
    refine ⟨3615340174644385805630417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2410226783096257203753611 3615340174644385805630417)
    ·
      refine ⟨2711505130983289354222813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3615340174644385805630417 2711505130983289354222813)
      ·
        refine ⟨1016814424118733507833555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2711505130983289354222813 1016814424118733507833555)
        ·
          refine ⟨1525221636178100261750333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016814424118733507833555 1525221636178100261750333)
          ·
            refine ⟨571958113566787598156375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1525221636178100261750333 571958113566787598156375)
            ·
              refine ⟨857937170350181397234563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571958113566787598156375 857937170350181397234563)
              ·
                refine ⟨1286905755525272095851845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857937170350181397234563 1286905755525272095851845)
                ·
                  refine ⟨241294829160988517972221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286905755525272095851845 241294829160988517972221)
                  ·
                    refine ⟨90485560935370694239583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241294829160988517972221 90485560935370694239583)
                    ·
                      rfl

theorem cell22_264330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_264330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264330 prefixEnd_264330 := by exact prefixLift 264330
  have htrace : WordTrace (prefixWord ++ tailWord_264330) baseStart_264330 baseEnd_264330 := by
    simpa [prefixWord, tailWord_264330, baseEnd_264330] using wordTrace_append hprefix tailTrace_264330
  have hstable : (prefixWord ++ tailWord_264330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264330).length < 2 ^ (prefixWord ++ tailWord_264330).sum := by decide
  have hdescent : baseEnd_264330 < baseStart_264330 := by decide
  rcases family_descends (prefixWord ++ tailWord_264330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264366 : List Nat := [4, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_264366 : Nat := 118140960795 + 264366 * 2 ^ 59
def prefixEnd_264366 : Nat := 4983230072969 + 3 ^ 40 * 264366 * 2
def baseEnd_264366 : Nat := 30165961490359533446491

theorem tailTrace_264366 : CollatzResearch.WordTrace tailWord_264366 prefixEnd_264366 30165961490359533446491 := by
  unfold tailWord_264366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205277520031825870415619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6428146773503071308883301 1205277520031825870415619)
  ·
    refine ⟨1807916280047738805623429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205277520031825870415619 1807916280047738805623429)
    ·
      refine ⟨338984302508951026054393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1807916280047738805623429 338984302508951026054393)
      ·
        refine ⟨254238226881713269540795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338984302508951026054393 254238226881713269540795)
        ·
          refine ⟨381357340322569904311193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254238226881713269540795 381357340322569904311193)
          ·
            refine ⟨286018005241927428233395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381357340322569904311193 286018005241927428233395)
            ·
              refine ⟨429027007862891142350093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286018005241927428233395 429027007862891142350093)
              ·
                refine ⟨160885127948584178381285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429027007862891142350093 160885127948584178381285)
                ·
                  refine ⟨30165961490359533446491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160885127948584178381285 30165961490359533446491)
                  ·
                    rfl

theorem cell22_264366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_264366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264366 prefixEnd_264366 := by exact prefixLift 264366
  have htrace : WordTrace (prefixWord ++ tailWord_264366) baseStart_264366 baseEnd_264366 := by
    simpa [prefixWord, tailWord_264366, baseEnd_264366] using wordTrace_append hprefix tailTrace_264366
  have hstable : (prefixWord ++ tailWord_264366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264366).length < 2 ^ (prefixWord ++ tailWord_264366).sum := by decide
  have hdescent : baseEnd_264366 < baseStart_264366 := by decide
  rcases family_descends (prefixWord ++ tailWord_264366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264463 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 4, 4]
def baseStart_264463 : Nat := 118140960795 + 264463 * 2 ^ 59
def prefixEnd_264463 : Nat := 4983230072969 + 3 ^ 40 * 264463 * 2
def baseEnd_264463 : Nat := 90531089553402680664175

theorem tailTrace_264463 : CollatzResearch.WordTrace tailWord_264463 prefixEnd_264463 90531089553402680664175 := by
  unfold tailWord_264463
  simp only [CollatzResearch.WordTrace]
  refine ⟨9645758040903192529606043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6430505360602128353070695 9645758040903192529606043)
  ·
    refine ⟨14468637061354788794409065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9645758040903192529606043 14468637061354788794409065)
    ·
      refine ⟨10851477796016091595806799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14468637061354788794409065 10851477796016091595806799)
      ·
        refine ⟨16277216694024137393710199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10851477796016091595806799 16277216694024137393710199)
        ·
          refine ⟨24415825041036206090565299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16277216694024137393710199 24415825041036206090565299)
          ·
            refine ⟨36623737561554309135847949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24415825041036206090565299 36623737561554309135847949)
            ·
              refine ⟨13733901585582865925942981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36623737561554309135847949 13733901585582865925942981)
              ·
                refine ⟨2575106547296787361114309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13733901585582865925942981 2575106547296787361114309)
                ·
                  refine ⟨482832477618147630208933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2575106547296787361114309 482832477618147630208933)
                  ·
                    refine ⟨90531089553402680664175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482832477618147630208933 90531089553402680664175)
                    ·
                      rfl

theorem cell22_264463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_264463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264463 prefixEnd_264463 := by exact prefixLift 264463
  have htrace : WordTrace (prefixWord ++ tailWord_264463) baseStart_264463 baseEnd_264463 := by
    simpa [prefixWord, tailWord_264463, baseEnd_264463] using wordTrace_append hprefix tailTrace_264463
  have hstable : (prefixWord ++ tailWord_264463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264463).length < 2 ^ (prefixWord ++ tailWord_264463).sum := by decide
  have hdescent : baseEnd_264463 < baseStart_264463 := by decide
  rcases family_descends (prefixWord ++ tailWord_264463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264465 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_264465 : Nat := 118140960795 + 264465 * 2 ^ 59
def prefixEnd_264465 : Nat := 4983230072969 + 3 ^ 40 * 264465 * 2
def baseEnd_264465 : Nat := 90531774194275342114169

theorem tailTrace_264465 : CollatzResearch.WordTrace tailWord_264465 prefixEnd_264465 90531774194275342114169 := by
  unfold tailWord_264465
  simp only [CollatzResearch.WordTrace]
  refine ⟨9645830986895946871178849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6430553991263964580785899 9645830986895946871178849)
  ·
    refine ⟨7234373240171960153384137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9645830986895946871178849 7234373240171960153384137)
    ·
      refine ⟨5425779930128970115038103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7234373240171960153384137 5425779930128970115038103)
      ·
        refine ⟨8138669895193455172557155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5425779930128970115038103 8138669895193455172557155)
        ·
          refine ⟨12208004842790182758835733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8138669895193455172557155 12208004842790182758835733)
          ·
            refine ⟨572250227005789816820425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12208004842790182758835733 572250227005789816820425)
            ·
              refine ⟨429187670254342362615319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572250227005789816820425 429187670254342362615319)
              ·
                refine ⟨643781505381513543922979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429187670254342362615319 643781505381513543922979)
                ·
                  refine ⟨965672258072270315884469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643781505381513543922979 965672258072270315884469)
                  ·
                    refine ⟨90531774194275342114169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 965672258072270315884469 90531774194275342114169)
                    ·
                      rfl

theorem cell22_264465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_264465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264465 prefixEnd_264465 := by exact prefixLift 264465
  have htrace : WordTrace (prefixWord ++ tailWord_264465) baseStart_264465 baseEnd_264465 := by
    simpa [prefixWord, tailWord_264465, baseEnd_264465] using wordTrace_append hprefix tailTrace_264465
  have hstable : (prefixWord ++ tailWord_264465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264465).length < 2 ^ (prefixWord ++ tailWord_264465).sum := by decide
  have hdescent : baseEnd_264465 < baseStart_264465 := by decide
  rcases family_descends (prefixWord ++ tailWord_264465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264480 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_264480 : Nat := 118140960795 + 264480 * 2 ^ 59
def prefixEnd_264480 : Nat := 4983230072969 + 3 ^ 40 * 264480 * 2
def baseEnd_264480 : Nat := 90536909000820302989123

theorem tailTrace_264480 : CollatzResearch.WordTrace tailWord_264480 prefixEnd_264480 90536909000820302989123 := by
  unfold tailWord_264480
  simp only [CollatzResearch.WordTrace]
  refine ⟨4823189040920802216487447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6430918721227736288649929 4823189040920802216487447)
  ·
    refine ⟨7234783561381203324731171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4823189040920802216487447 7234783561381203324731171)
    ·
      refine ⟨10852175342071804987096757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7234783561381203324731171 10852175342071804987096757)
      ·
        refine ⟨1017391438319231717540321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10852175342071804987096757 1017391438319231717540321)
        ·
          refine ⟨763043578739423788155241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017391438319231717540321 763043578739423788155241)
          ·
            refine ⟨572282684054567841116431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763043578739423788155241 572282684054567841116431)
            ·
              refine ⟨858424026081851761674647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572282684054567841116431 858424026081851761674647)
              ·
                refine ⟨1287636039122777642511971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858424026081851761674647 1287636039122777642511971)
                ·
                  refine ⟨1931454058684166463767957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287636039122777642511971 1931454058684166463767957)
                  ·
                    refine ⟨90536909000820302989123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1931454058684166463767957 90536909000820302989123)
                    ·
                      rfl

theorem cell22_264480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_264480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264480 prefixEnd_264480 := by exact prefixLift 264480
  have htrace : WordTrace (prefixWord ++ tailWord_264480) baseStart_264480 baseEnd_264480 := by
    simpa [prefixWord, tailWord_264480, baseEnd_264480] using wordTrace_append hprefix tailTrace_264480
  have hstable : (prefixWord ++ tailWord_264480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264480).length < 2 ^ (prefixWord ++ tailWord_264480).sum := by decide
  have hdescent : baseEnd_264480 < baseStart_264480 := by decide
  rcases family_descends (prefixWord ++ tailWord_264480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264516 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_264516 : Nat := 118140960795 + 264516 * 2 ^ 59
def prefixEnd_264516 : Nat := 4983230072969 + 3 ^ 40 * 264516 * 2
def baseEnd_264516 : Nat := 90549232536528209089013

theorem tailTrace_264516 : CollatzResearch.WordTrace tailWord_264516 prefixEnd_264516 90549232536528209089013 := by
  unfold tailWord_264516
  simp only [CollatzResearch.WordTrace]
  refine ⟨4823845554855591290642701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6431794073140788387523601 4823845554855591290642701)
  ·
    refine ⟨1808942083070846733991013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4823845554855591290642701 1808942083070846733991013)
    ·
      refine ⟨339176640575783762623315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1808942083070846733991013 339176640575783762623315)
      ·
        refine ⟨508764960863675643934973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339176640575783762623315 508764960863675643934973)
        ·
          refine ⟨190786860323878366475615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508764960863675643934973 190786860323878366475615)
          ·
            refine ⟨286180290485817549713423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190786860323878366475615 286180290485817549713423)
            ·
              refine ⟨429270435728726324570135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286180290485817549713423 429270435728726324570135)
              ·
                refine ⟨643905653593089486855203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429270435728726324570135 643905653593089486855203)
                ·
                  refine ⟨965858480389634230282805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643905653593089486855203 965858480389634230282805)
                  ·
                    refine ⟨90549232536528209089013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 965858480389634230282805 90549232536528209089013)
                    ·
                      rfl

theorem cell22_264516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_264516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264516 prefixEnd_264516 := by exact prefixLift 264516
  have htrace : WordTrace (prefixWord ++ tailWord_264516) baseStart_264516 baseEnd_264516 := by
    simpa [prefixWord, tailWord_264516, baseEnd_264516] using wordTrace_append hprefix tailTrace_264516
  have hstable : (prefixWord ++ tailWord_264516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264516).length < 2 ^ (prefixWord ++ tailWord_264516).sum := by decide
  have hdescent : baseEnd_264516 < baseStart_264516 := by decide
  rcases family_descends (prefixWord ++ tailWord_264516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264587 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 1, 4]
def baseStart_264587 : Nat := 118140960795 + 264587 * 2 ^ 59
def prefixEnd_264587 : Nat := 4983230072969 + 3 ^ 40 * 264587 * 2
def baseEnd_264587 : Nat := 90573537287507690563795

theorem tailTrace_264587 : CollatzResearch.WordTrace tailWord_264587 prefixEnd_264587 90573537287507690563795 := by
  unfold tailWord_264587
  simp only [CollatzResearch.WordTrace]
  refine ⟨9650280692453961707120015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6433520461635974471413343 9650280692453961707120015)
  ·
    refine ⟨14475421038680942560680023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9650280692453961707120015 14475421038680942560680023)
    ·
      refine ⟨21713131558021413841020035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14475421038680942560680023 21713131558021413841020035)
      ·
        refine ⟨32569697337032120761530053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21713131558021413841020035 32569697337032120761530053)
        ·
          refine ⟨6106818250693522642786885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32569697337032120761530053 6106818250693522642786885)
          ·
            refine ⟨1145028422005035495522541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6106818250693522642786885 1145028422005035495522541)
            ·
              refine ⟨429385658251888310820953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1145028422005035495522541 429385658251888310820953)
              ·
                refine ⟨322039243688916233115715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429385658251888310820953 322039243688916233115715)
                ·
                  refine ⟨483058865533374349673573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322039243688916233115715 483058865533374349673573)
                  ·
                    refine ⟨90573537287507690563795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483058865533374349673573 90573537287507690563795)
                    ·
                      rfl

theorem cell22_264587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 4].length) (baseStart_264587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264587 prefixEnd_264587 := by exact prefixLift 264587
  have htrace : WordTrace (prefixWord ++ tailWord_264587) baseStart_264587 baseEnd_264587 := by
    simpa [prefixWord, tailWord_264587, baseEnd_264587] using wordTrace_append hprefix tailTrace_264587
  have hstable : (prefixWord ++ tailWord_264587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264587).length < 2 ^ (prefixWord ++ tailWord_264587).sum := by decide
  have hdescent : baseEnd_264587 < baseStart_264587 := by decide
  rcases family_descends (prefixWord ++ tailWord_264587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264647 : List Nat := [1, 1, 4, 1, 1, 5, 3, 6]
def baseStart_264647 : Nat := 118140960795 + 264647 * 2 ^ 59
def prefixEnd_264647 : Nat := 4983230072969 + 3 ^ 40 * 264647 * 2
def baseEnd_264647 : Nat := 10066008501520837118179

theorem tailTrace_264647 : CollatzResearch.WordTrace tailWord_264647 prefixEnd_264647 10066008501520837118179 := by
  unfold tailWord_264647
  simp only [CollatzResearch.WordTrace]
  refine ⟨9652469072236591954304195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6434979381491061302869463 9652469072236591954304195)
  ·
    refine ⟨14478703608354887931456293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9652469072236591954304195 14478703608354887931456293)
    ·
      refine ⟨2714756926566541487148055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14478703608354887931456293 2714756926566541487148055)
      ·
        refine ⟨4072135389849812230722083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714756926566541487148055 4072135389849812230722083)
        ·
          refine ⟨6108203084774718346083125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4072135389849812230722083 6108203084774718346083125)
          ·
            refine ⟨572644039197629844945293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6108203084774718346083125 572644039197629844945293)
            ·
              refine ⟨214741514699111191854485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 572644039197629844945293 214741514699111191854485)
              ·
                refine ⟨10066008501520837118179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214741514699111191854485 10066008501520837118179)
                ·
                  rfl

theorem cell22_264647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 6].length) (baseStart_264647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264647 prefixEnd_264647 := by exact prefixLift 264647
  have htrace : WordTrace (prefixWord ++ tailWord_264647) baseStart_264647 baseEnd_264647 := by
    simpa [prefixWord, tailWord_264647, baseEnd_264647] using wordTrace_append hprefix tailTrace_264647
  have hstable : (prefixWord ++ tailWord_264647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264647).length < 2 ^ (prefixWord ++ tailWord_264647).sum := by decide
  have hdescent : baseEnd_264647 < baseStart_264647 := by decide
  rcases family_descends (prefixWord ++ tailWord_264647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264679 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 3, 3]
def baseStart_264679 : Nat := 118140960795 + 264679 * 2 ^ 59
def prefixEnd_264679 : Nat := 4983230072969 + 3 ^ 40 * 264679 * 2
def baseEnd_264679 : Nat := 90605030767650117263513

theorem tailTrace_264679 : CollatzResearch.WordTrace tailWord_264679 prefixEnd_264679 90605030767650117263513 := by
  unfold tailWord_264679
  simp only [CollatzResearch.WordTrace]
  refine ⟨9653636208120661419469091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6435757472080440946312727 9653636208120661419469091)
  ·
    refine ⟨14480454312180992129203637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9653636208120661419469091 14480454312180992129203637)
    ·
      refine ⟨1357542591766968012112841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14480454312180992129203637 1357542591766968012112841)
      ·
        refine ⟨1018156943825226009084631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1357542591766968012112841 1018156943825226009084631)
        ·
          refine ⟨1527235415737839013626947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018156943825226009084631 1527235415737839013626947)
          ·
            refine ⟨2290853123606758520440421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527235415737839013626947 2290853123606758520440421)
            ·
              refine ⟨429534960676267222582579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2290853123606758520440421 429534960676267222582579)
              ·
                refine ⟨644302441014400833873869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429534960676267222582579 644302441014400833873869)
                ·
                  refine ⟨241613415380400312702701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644302441014400833873869 241613415380400312702701)
                  ·
                    refine ⟨90605030767650117263513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241613415380400312702701 90605030767650117263513)
                    ·
                      rfl

theorem cell22_264679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_264679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264679 prefixEnd_264679 := by exact prefixLift 264679
  have htrace : WordTrace (prefixWord ++ tailWord_264679) baseStart_264679 baseEnd_264679 := by
    simpa [prefixWord, tailWord_264679, baseEnd_264679] using wordTrace_append hprefix tailTrace_264679
  have hstable : (prefixWord ++ tailWord_264679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264679).length < 2 ^ (prefixWord ++ tailWord_264679).sum := by decide
  have hdescent : baseEnd_264679 < baseStart_264679 := by decide
  rcases family_descends (prefixWord ++ tailWord_264679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264769 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_264769 : Nat := 118140960795 + 264769 * 2 ^ 59
def prefixEnd_264769 : Nat := 4983230072969 + 3 ^ 40 * 264769 * 2
def baseEnd_264769 : Nat := 90635839606919882513237

theorem tailTrace_264769 : CollatzResearch.WordTrace tailWord_264769 prefixEnd_264769 90635839606919882513237 := by
  unfold tailWord_264769
  simp only [CollatzResearch.WordTrace]
  refine ⟨9656918777794606790245361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6437945851863071193496907 9656918777794606790245361)
  ·
    refine ⟨7242689083345955092684021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9656918777794606790245361 7242689083345955092684021)
    ·
      refine ⟨679002101563683289939127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7242689083345955092684021 679002101563683289939127)
      ·
        refine ⟨1018503152345524934908691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679002101563683289939127 1018503152345524934908691)
        ·
          refine ⟨1527754728518287402363037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018503152345524934908691 1527754728518287402363037)
          ·
            refine ⟨572908023194357775886139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1527754728518287402363037 572908023194357775886139)
            ·
              refine ⟨859362034791536663829209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572908023194357775886139 859362034791536663829209)
              ·
                refine ⟨644521526093652497871907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859362034791536663829209 644521526093652497871907)
                ·
                  refine ⟨966782289140478746807861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644521526093652497871907 966782289140478746807861)
                  ·
                    refine ⟨90635839606919882513237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 966782289140478746807861 90635839606919882513237)
                    ·
                      rfl

theorem cell22_264769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_264769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264769 prefixEnd_264769 := by exact prefixLift 264769
  have htrace : WordTrace (prefixWord ++ tailWord_264769) baseStart_264769 baseEnd_264769 := by
    simpa [prefixWord, tailWord_264769, baseEnd_264769] using wordTrace_append hprefix tailTrace_264769
  have hstable : (prefixWord ++ tailWord_264769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264769).length < 2 ^ (prefixWord ++ tailWord_264769).sum := by decide
  have hdescent : baseEnd_264769 < baseStart_264769 := by decide
  rcases family_descends (prefixWord ++ tailWord_264769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264786 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_264786 : Nat := 118140960795 + 264786 * 2 ^ 59
def prefixEnd_264786 : Nat := 4983230072969 + 3 ^ 40 * 264786 * 2
def baseEnd_264786 : Nat := 90641659054337504838185

theorem tailTrace_264786 : CollatzResearch.WordTrace tailWord_264786 prefixEnd_264786 90641659054337504838185 := by
  unfold tailWord_264786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414384704683254673403553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6438359212488679129076141 2414384704683254673403553)
  ·
    refine ⟨1810788528512441005052665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2414384704683254673403553 1810788528512441005052665)
    ·
      refine ⟨1358091396384330753789499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1810788528512441005052665 1358091396384330753789499)
      ·
        refine ⟨2037137094576496130684249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1358091396384330753789499 2037137094576496130684249)
        ·
          refine ⟨1527852820932372098013187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2037137094576496130684249 1527852820932372098013187)
          ·
            refine ⟨2291779231398558147019781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527852820932372098013187 2291779231398558147019781)
            ·
              refine ⟨429708605887229652566209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2291779231398558147019781 429708605887229652566209)
              ·
                refine ⟨322281454415422239424657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429708605887229652566209 322281454415422239424657)
                ·
                  refine ⟨241711090811566679568493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322281454415422239424657 241711090811566679568493)
                  ·
                    refine ⟨90641659054337504838185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241711090811566679568493 90641659054337504838185)
                    ·
                      rfl

theorem cell22_264786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_264786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264786 prefixEnd_264786 := by exact prefixLift 264786
  have htrace : WordTrace (prefixWord ++ tailWord_264786) baseStart_264786 baseEnd_264786 := by
    simpa [prefixWord, tailWord_264786, baseEnd_264786] using wordTrace_append hprefix tailTrace_264786
  have hstable : (prefixWord ++ tailWord_264786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264786).length < 2 ^ (prefixWord ++ tailWord_264786).sum := by decide
  have hdescent : baseEnd_264786 < baseStart_264786 := by decide
  rcases family_descends (prefixWord ++ tailWord_264786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264788 : List Nat := [2, 4, 1, 1, 1, 5, 2, 2, 4]
def baseStart_264788 : Nat := 118140960795 + 264788 * 2 ^ 59
def prefixEnd_264788 : Nat := 4983230072969 + 3 ^ 40 * 264788 * 2
def baseEnd_264788 : Nat := 30214114565070055429393

theorem tailTrace_264788 : CollatzResearch.WordTrace tailWord_264788 prefixEnd_264788 30214114565070055429393 := by
  unfold tailWord_264788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828805882362886517593509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6438407843150515356791345 4828805882362886517593509)
  ·
    refine ⟨905401102943041222048783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4828805882362886517593509 905401102943041222048783)
    ·
      refine ⟨1358101654414561833073175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 905401102943041222048783 1358101654414561833073175)
      ·
        refine ⟨2037152481621842749609763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1358101654414561833073175 2037152481621842749609763)
        ·
          refine ⟨3055728722432764124414645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037152481621842749609763 3055728722432764124414645)
          ·
            refine ⟨286474567728071636663873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3055728722432764124414645 286474567728071636663873)
            ·
              refine ⟨214855925796053727497905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286474567728071636663873 214855925796053727497905)
              ·
                refine ⟨161141944347040295623429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214855925796053727497905 161141944347040295623429)
                ·
                  refine ⟨30214114565070055429393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161141944347040295623429 30214114565070055429393)
                  ·
                    rfl

theorem cell22_264788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_264788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264788 prefixEnd_264788 := by exact prefixLift 264788
  have htrace : WordTrace (prefixWord ++ tailWord_264788) baseStart_264788 baseEnd_264788 := by
    simpa [prefixWord, tailWord_264788, baseEnd_264788] using wordTrace_append hprefix tailTrace_264788
  have hstable : (prefixWord ++ tailWord_264788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264788).length < 2 ^ (prefixWord ++ tailWord_264788).sum := by decide
  have hdescent : baseEnd_264788 < baseStart_264788 := by decide
  rcases family_descends (prefixWord ++ tailWord_264788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264818 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_264818 : Nat := 118140960795 + 264818 * 2 ^ 59
def prefixEnd_264818 : Nat := 4983230072969 + 3 ^ 40 * 264818 * 2
def baseEnd_264818 : Nat := 90652613308300088038087

theorem tailTrace_264818 : CollatzResearch.WordTrace tailWord_264818 prefixEnd_264818 90652613308300088038087 := by
  unfold tailWord_264818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414676488654272039694777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6439137303078058772519405 2414676488654272039694777)
  ·
    refine ⟨1811007366490704029771083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2414676488654272039694777 1811007366490704029771083)
    ·
      refine ⟨2716511049736056044656625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811007366490704029771083 2716511049736056044656625)
      ·
        refine ⟨2037383287302042033492469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2716511049736056044656625 2037383287302042033492469)
        ·
          refine ⟨191004683184566440639919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2037383287302042033492469 191004683184566440639919)
          ·
            refine ⟨286507024776849660959879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191004683184566440639919 286507024776849660959879)
            ·
              refine ⟨429760537165274491439819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286507024776849660959879 429760537165274491439819)
              ·
                refine ⟨644640805747911737159729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429760537165274491439819 644640805747911737159729)
                ·
                  refine ⟨483480604310933802869797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644640805747911737159729 483480604310933802869797)
                  ·
                    refine ⟨90652613308300088038087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483480604310933802869797 90652613308300088038087)
                    ·
                      rfl

theorem cell22_264818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_264818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264818 prefixEnd_264818 := by exact prefixLift 264818
  have htrace : WordTrace (prefixWord ++ tailWord_264818) baseStart_264818 baseEnd_264818 := by
    simpa [prefixWord, tailWord_264818, baseEnd_264818] using wordTrace_append hprefix tailTrace_264818
  have hstable : (prefixWord ++ tailWord_264818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264818).length < 2 ^ (prefixWord ++ tailWord_264818).sum := by decide
  have hdescent : baseEnd_264818 < baseStart_264818 := by decide
  rcases family_descends (prefixWord ++ tailWord_264818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264906 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_264906 : Nat := 118140960795 + 264906 * 2 ^ 59
def prefixEnd_264906 : Nat := 4983230072969 + 3 ^ 40 * 264906 * 2
def baseEnd_264906 : Nat := 30227579168899063945939

theorem tailTrace_264906 : CollatzResearch.WordTrace tailWord_264906 prefixEnd_264906 30227579168899063945939 := by
  unfold tailWord_264906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415478894574569796995643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6441277052198852791988381 2415478894574569796995643)
  ·
    refine ⟨3623218341861854695493465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2415478894574569796995643 3623218341861854695493465)
    ·
      refine ⟨2717413756396391021620099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3623218341861854695493465 2717413756396391021620099)
      ·
        refine ⟨4076120634594586532430149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717413756396391021620099 4076120634594586532430149)
        ·
          refine ⟨764272618986484974830653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4076120634594586532430149 764272618986484974830653)
          ·
            refine ⟨286602232119931865561495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 764272618986484974830653 286602232119931865561495)
            ·
              refine ⟨429903348179897798342243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286602232119931865561495 429903348179897798342243)
              ·
                refine ⟨644855022269846697513365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429903348179897798342243 644855022269846697513365)
                ·
                  refine ⟨30227579168899063945939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 644855022269846697513365 30227579168899063945939)
                  ·
                    rfl

theorem cell22_264906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_264906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264906 prefixEnd_264906 := by exact prefixLift 264906
  have htrace : WordTrace (prefixWord ++ tailWord_264906) baseStart_264906 baseEnd_264906 := by
    simpa [prefixWord, tailWord_264906, baseEnd_264906] using wordTrace_append hprefix tailTrace_264906
  have hstable : (prefixWord ++ tailWord_264906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264906).length < 2 ^ (prefixWord ++ tailWord_264906).sum := by decide
  have hdescent : baseEnd_264906 < baseStart_264906 := by decide
  rcases family_descends (prefixWord ++ tailWord_264906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264921 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 2, 3]
def baseStart_264921 : Nat := 118140960795 + 264921 * 2 ^ 59
def prefixEnd_264921 : Nat := 4983230072969 + 3 ^ 40 * 264921 * 2
def baseEnd_264921 : Nat := 90687872313242152712771

theorem tailTrace_264921 : CollatzResearch.WordTrace tailWord_264921 prefixEnd_264921 90687872313242152712771 := by
  unfold tailWord_264921
  simp only [CollatzResearch.WordTrace]
  refine ⟨9662462673243936749778617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6441641782162624499852411 9662462673243936749778617)
  ·
    refine ⟨7246847004932952562333963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9662462673243936749778617 7246847004932952562333963)
    ·
      refine ⟨10870270507399428843500945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7246847004932952562333963 10870270507399428843500945)
      ·
        refine ⟨8152702880549571632625709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10870270507399428843500945 8152702880549571632625709)
        ·
          refine ⟨3057263580206089362234641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8152702880549571632625709 3057263580206089362234641)
          ·
            refine ⟨2292947685154567021675981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3057263580206089362234641 2292947685154567021675981)
            ·
              refine ⟨859855381932962633128493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2292947685154567021675981 859855381932962633128493)
              ·
                refine ⟨322445768224860987423185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859855381932962633128493 322445768224860987423185)
                ·
                  refine ⟨241834326168645740567389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322445768224860987423185 241834326168645740567389)
                  ·
                    refine ⟨90687872313242152712771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241834326168645740567389 90687872313242152712771)
                    ·
                      rfl

theorem cell22_264921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_264921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264921 prefixEnd_264921 := by exact prefixLift 264921
  have htrace : WordTrace (prefixWord ++ tailWord_264921) baseStart_264921 baseEnd_264921 := by
    simpa [prefixWord, tailWord_264921, baseEnd_264921] using wordTrace_append hprefix tailTrace_264921
  have hstable : (prefixWord ++ tailWord_264921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264921).length < 2 ^ (prefixWord ++ tailWord_264921).sum := by decide
  have hdescent : baseEnd_264921 < baseStart_264921 := by decide
  rcases family_descends (prefixWord ++ tailWord_264921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264964 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_264964 : Nat := 118140960795 + 264964 * 2 ^ 59
def prefixEnd_264964 : Nat := 4983230072969 + 3 ^ 40 * 264964 * 2
def baseEnd_264964 : Nat := 90702592092004373887639

theorem tailTrace_264964 : CollatzResearch.WordTrace tailWord_264964 prefixEnd_264964 90702592092004373887639 := by
  unfold tailWord_264964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4832015506044077546796973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6442687341392103395729297 4832015506044077546796973)
  ·
    refine ⟨1812005814766529080048865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4832015506044077546796973 1812005814766529080048865)
    ·
      refine ⟨1359004361074896810036649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1812005814766529080048865 1359004361074896810036649)
      ·
        refine ⟨1019253270806172607527487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1359004361074896810036649 1019253270806172607527487)
        ·
          refine ⟨1528879906209258911291231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019253270806172607527487 1528879906209258911291231)
          ·
            refine ⟨2293319859313888366936847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528879906209258911291231 2293319859313888366936847)
            ·
              refine ⟨3439979788970832550405271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293319859313888366936847 3439979788970832550405271)
              ·
                refine ⟨5159969683456248825607907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3439979788970832550405271 5159969683456248825607907)
                ·
                  refine ⟨7739954525184373238411861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5159969683456248825607907 7739954525184373238411861)
                  ·
                    refine ⟨90702592092004373887639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7739954525184373238411861 90702592092004373887639)
                    ·
                      rfl

theorem cell22_264964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_264964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264964 prefixEnd_264964 := by exact prefixLift 264964
  have htrace : WordTrace (prefixWord ++ tailWord_264964) baseStart_264964 baseEnd_264964 := by
    simpa [prefixWord, tailWord_264964, baseEnd_264964] using wordTrace_append hprefix tailTrace_264964
  have hstable : (prefixWord ++ tailWord_264964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264964).length < 2 ^ (prefixWord ++ tailWord_264964).sum := by decide
  have hdescent : baseEnd_264964 < baseStart_264964 := by decide
  rcases family_descends (prefixWord ++ tailWord_264964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264979 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 5]
def baseStart_264979 : Nat := 118140960795 + 264979 * 2 ^ 59
def prefixEnd_264979 : Nat := 4983230072969 + 3 ^ 40 * 264979 * 2
def baseEnd_264979 : Nat := 30235908966183111587531

theorem tailTrace_264979 : CollatzResearch.WordTrace tailWord_264979 prefixEnd_264979 30235908966183111587531 := by
  unfold tailWord_264979
  simp only [CollatzResearch.WordTrace]
  refine ⟨9664578107033812655389991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6443052071355875103593327 9664578107033812655389991)
  ·
    refine ⟨14496867160550718983084987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9664578107033812655389991 14496867160550718983084987)
    ·
      refine ⟨21745300740826078474627481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14496867160550718983084987 21745300740826078474627481)
      ·
        refine ⟨16308975555619558855970611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21745300740826078474627481 16308975555619558855970611)
        ·
          refine ⟨24463463333429338283955917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16308975555619558855970611 24463463333429338283955917)
          ·
            refine ⟨9173798750036001856483469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24463463333429338283955917 9173798750036001856483469)
            ·
              refine ⟨3440174531263500696181301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9173798750036001856483469 3440174531263500696181301)
              ·
                refine ⟨322516362305953190266997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3440174531263500696181301 322516362305953190266997)
                ·
                  refine ⟨30235908966183111587531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322516362305953190266997 30235908966183111587531)
                  ·
                    rfl

theorem cell22_264979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 5].length) (baseStart_264979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264979 prefixEnd_264979 := by exact prefixLift 264979
  have htrace : WordTrace (prefixWord ++ tailWord_264979) baseStart_264979 baseEnd_264979 := by
    simpa [prefixWord, tailWord_264979, baseEnd_264979] using wordTrace_append hprefix tailTrace_264979
  have hstable : (prefixWord ++ tailWord_264979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264979).length < 2 ^ (prefixWord ++ tailWord_264979).sum := by decide
  have hdescent : baseEnd_264979 < baseStart_264979 := by decide
  rcases family_descends (prefixWord ++ tailWord_264979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264983 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 3, 3]
def baseStart_264983 : Nat := 118140960795 + 264983 * 2 ^ 59
def prefixEnd_264983 : Nat := 4983230072969 + 3 ^ 40 * 264983 * 2
def baseEnd_264983 : Nat := 90709096180294657662581

theorem tailTrace_264983 : CollatzResearch.WordTrace tailWord_264983 prefixEnd_264983 90709096180294657662581 := by
  unfold tailWord_264983
  simp only [CollatzResearch.WordTrace]
  refine ⟨9664723999019321338535603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6443149332679547559023735 9664723999019321338535603)
  ·
    refine ⟨14497085998528982007803405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9664723999019321338535603 14497085998528982007803405)
    ·
      refine ⟨5436407249448368252926277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14497085998528982007803405 5436407249448368252926277)
      ·
        refine ⟨1019326359271569047423677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5436407249448368252926277 1019326359271569047423677)
        ·
          refine ⟨382247384726838392783879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1019326359271569047423677 382247384726838392783879)
          ·
            refine ⟨573371077090257589175819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382247384726838392783879 573371077090257589175819)
            ·
              refine ⟨860056615635386383763729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573371077090257589175819 860056615635386383763729)
              ·
                refine ⟨645042461726539787822797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 860056615635386383763729 645042461726539787822797)
                ·
                  refine ⟨241890923147452420433549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645042461726539787822797 241890923147452420433549)
                  ·
                    refine ⟨90709096180294657662581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241890923147452420433549 90709096180294657662581)
                    ·
                      rfl

theorem cell22_264983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_264983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_264983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_264983 prefixEnd_264983 := by exact prefixLift 264983
  have htrace : WordTrace (prefixWord ++ tailWord_264983) baseStart_264983 baseEnd_264983 := by
    simpa [prefixWord, tailWord_264983, baseEnd_264983] using wordTrace_append hprefix tailTrace_264983
  have hstable : (prefixWord ++ tailWord_264983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264983).length < 2 ^ (prefixWord ++ tailWord_264983).sum := by decide
  have hdescent : baseEnd_264983 < baseStart_264983 := by decide
  rcases family_descends (prefixWord ++ tailWord_264983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265000 : List Nat := [2, 1, 5, 1, 1, 1, 4, 3, 1, 3]
def baseStart_265000 : Nat := 118140960795 + 265000 * 2 ^ 59
def prefixEnd_265000 : Nat := 4983230072969 + 3 ^ 40 * 265000 * 2
def baseEnd_265000 : Nat := 90714915627712279987529

theorem tailTrace_265000 : CollatzResearch.WordTrace tailWord_265000 prefixEnd_265000 90714915627712279987529 := by
  unfold tailWord_265000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4832672019978866620952227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6443562693305155494602969 4832672019978866620952227)
  ·
    refine ⟨7249008029968299931428341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4832672019978866620952227 7249008029968299931428341)
    ·
      refine ⟨679594502809528118571407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7249008029968299931428341 679594502809528118571407)
      ·
        refine ⟨1019391754214292177857111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679594502809528118571407 1019391754214292177857111)
        ·
          refine ⟨1529087631321438266785667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019391754214292177857111 1529087631321438266785667)
          ·
            refine ⟨2293631446982157400178501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529087631321438266785667 2293631446982157400178501)
            ·
              refine ⟨430055896309154512533469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2293631446982157400178501 430055896309154512533469)
              ·
                refine ⟨161270961115932942200051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430055896309154512533469 161270961115932942200051)
                ·
                  refine ⟨241906441673899413300077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161270961115932942200051 241906441673899413300077)
                  ·
                    refine ⟨90714915627712279987529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241906441673899413300077 90714915627712279987529)
                    ·
                      rfl

theorem cell22_265000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_265000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265000 prefixEnd_265000 := by exact prefixLift 265000
  have htrace : WordTrace (prefixWord ++ tailWord_265000) baseStart_265000 baseEnd_265000 := by
    simpa [prefixWord, tailWord_265000, baseEnd_265000] using wordTrace_append hprefix tailTrace_265000
  have hstable : (prefixWord ++ tailWord_265000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265000).length < 2 ^ (prefixWord ++ tailWord_265000).sum := by decide
  have hdescent : baseEnd_265000 < baseStart_265000 := by decide
  rcases family_descends (prefixWord ++ tailWord_265000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265013 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 5]
def baseStart_265013 : Nat := 118140960795 + 265013 * 2 ^ 59
def prefixEnd_265013 : Nat := 4983230072969 + 3 ^ 40 * 265013 * 2
def baseEnd_265013 : Nat := 30239788597794859804163

theorem tailTrace_265013 : CollatzResearch.WordTrace tailWord_265013 prefixEnd_265013 30239788597794859804163 := by
  unfold tailWord_265013
  simp only [CollatzResearch.WordTrace]
  refine ⟨9665818188910636462127693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6443878792607090974751795 9665818188910636462127693)
  ·
    refine ⟨3624681820841488673297885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9665818188910636462127693 3624681820841488673297885)
    ·
      refine ⟨1359255682815558252486707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3624681820841488673297885 1359255682815558252486707)
      ·
        refine ⟨2038883524223337378730061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359255682815558252486707 2038883524223337378730061)
        ·
          refine ⟨764581321583751517023773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2038883524223337378730061 764581321583751517023773)
          ·
            refine ⟨286717995593906818883915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 764581321583751517023773 286717995593906818883915)
            ·
              refine ⟨430076993390860228325873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286717995593906818883915 430076993390860228325873)
              ·
                refine ⟨322557745043145171244405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430076993390860228325873 322557745043145171244405)
                ·
                  refine ⟨30239788597794859804163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322557745043145171244405 30239788597794859804163)
                  ·
                    rfl

theorem cell22_265013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_265013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265013 prefixEnd_265013 := by exact prefixLift 265013
  have htrace : WordTrace (prefixWord ++ tailWord_265013) baseStart_265013 baseEnd_265013 := by
    simpa [prefixWord, tailWord_265013, baseEnd_265013] using wordTrace_append hprefix tailTrace_265013
  have hstable : (prefixWord ++ tailWord_265013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265013).length < 2 ^ (prefixWord ++ tailWord_265013).sum := by decide
  have hdescent : baseEnd_265013 < baseStart_265013 := by decide
  rcases family_descends (prefixWord ++ tailWord_265013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265056 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 6, 3]
def baseStart_265056 : Nat := 118140960795 + 265056 * 2 ^ 59
def prefixEnd_265056 : Nat := 4983230072969 + 3 ^ 40 * 265056 * 2
def baseEnd_265056 : Nat := 90734085572146800587357

theorem tailTrace_265056 : CollatzResearch.WordTrace tailWord_265056 prefixEnd_265056 90734085572146800587357 := by
  unfold tailWord_265056
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833693263877427402971511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6444924351836569870628681 4833693263877427402971511)
  ·
    refine ⟨7250539895816141104457267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4833693263877427402971511 7250539895816141104457267)
    ·
      refine ⟨10875809843724211656685901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7250539895816141104457267 10875809843724211656685901)
      ·
        refine ⟨4078428691396579371257213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10875809843724211656685901 4078428691396579371257213)
        ·
          refine ⟨1529410759273717264221455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4078428691396579371257213 1529410759273717264221455)
          ·
            refine ⟨2294116138910575896332183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529410759273717264221455 2294116138910575896332183)
            ·
              refine ⟨3441174208365863844498275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294116138910575896332183 3441174208365863844498275)
              ·
                refine ⟨5161761312548795766747413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441174208365863844498275 5161761312548795766747413)
                ·
                  refine ⟨241957561525724801566285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5161761312548795766747413 241957561525724801566285)
                  ·
                    refine ⟨90734085572146800587357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241957561525724801566285 90734085572146800587357)
                    ·
                      rfl

theorem cell22_265056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_265056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265056 prefixEnd_265056 := by exact prefixLift 265056
  have htrace : WordTrace (prefixWord ++ tailWord_265056) baseStart_265056 baseEnd_265056 := by
    simpa [prefixWord, tailWord_265056, baseEnd_265056] using wordTrace_append hprefix tailTrace_265056
  have hstable : (prefixWord ++ tailWord_265056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265056).length < 2 ^ (prefixWord ++ tailWord_265056).sum := by decide
  have hdescent : baseEnd_265056 < baseStart_265056 := by decide
  rcases family_descends (prefixWord ++ tailWord_265056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265146 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_265146 : Nat := 118140960795 + 265146 * 2 ^ 59
def prefixEnd_265146 : Nat := 4983230072969 + 3 ^ 40 * 265146 * 2
def baseEnd_265146 : Nat := 90764894411416565837081

theorem tailTrace_265146 : CollatzResearch.WordTrace tailWord_265146 prefixEnd_265146 90764894411416565837081 := by
  unfold tailWord_265146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417667274357200044179823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6447112731619200117812861 2417667274357200044179823)
  ·
    refine ⟨3626500911535800066269735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417667274357200044179823 3626500911535800066269735)
    ·
      refine ⟨5439751367303700099404603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3626500911535800066269735 5439751367303700099404603)
      ·
        refine ⟨8159627050955550149106905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5439751367303700099404603 8159627050955550149106905)
        ·
          refine ⟨6119720288216662611830179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8159627050955550149106905 6119720288216662611830179)
          ·
            refine ⟨9179580432324993917745269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6119720288216662611830179 9179580432324993917745269)
            ·
              refine ⟨860585665530468179788619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9179580432324993917745269 860585665530468179788619)
              ·
                refine ⟨1290878498295702269682929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860585665530468179788619 1290878498295702269682929)
                ·
                  refine ⟨968158873721776702262197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290878498295702269682929 968158873721776702262197)
                  ·
                    refine ⟨90764894411416565837081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 968158873721776702262197 90764894411416565837081)
                    ·
                      rfl

theorem cell22_265146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_265146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265146 prefixEnd_265146 := by exact prefixLift 265146
  have htrace : WordTrace (prefixWord ++ tailWord_265146) baseStart_265146 baseEnd_265146 := by
    simpa [prefixWord, tailWord_265146, baseEnd_265146] using wordTrace_append hprefix tailTrace_265146
  have hstable : (prefixWord ++ tailWord_265146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265146).length < 2 ^ (prefixWord ++ tailWord_265146).sum := by decide
  have hdescent : baseEnd_265146 < baseStart_265146 := by decide
  rcases family_descends (prefixWord ++ tailWord_265146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265221 : List Nat := [1, 3, 1, 1, 2, 3, 3, 8]
def baseStart_265221 : Nat := 118140960795 + 265221 * 2 ^ 59
def prefixEnd_265221 : Nat := 4983230072969 + 3 ^ 40 * 265221 * 2
def baseEnd_265221 : Nat := 10087840938237930023539

theorem tailTrace_265221 : CollatzResearch.WordTrace tailWord_265221 prefixEnd_265221 10087840938237930023539 := by
  unfold tailWord_265221
  simp only [CollatzResearch.WordTrace]
  refine ⟨9673404572157087985699517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6448936381438058657133011 9673404572157087985699517)
  ·
    refine ⟨3627526714558907994637319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9673404572157087985699517 3627526714558907994637319)
    ·
      refine ⟨5441290071838361991955979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3627526714558907994637319 5441290071838361991955979)
      ·
        refine ⟨8161935107757542987933969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5441290071838361991955979 8161935107757542987933969)
        ·
          refine ⟨6121451330818157240950477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8161935107757542987933969 6121451330818157240950477)
          ·
            refine ⟨2295544249056808965356429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6121451330818157240950477 2295544249056808965356429)
            ·
              refine ⟨860829093396303362008661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2295544249056808965356429 860829093396303362008661)
              ·
                refine ⟨10087840938237930023539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 860829093396303362008661 10087840938237930023539)
                ·
                  rfl

theorem cell22_265221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 8].length) (baseStart_265221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265221 prefixEnd_265221 := by exact prefixLift 265221
  have htrace : WordTrace (prefixWord ++ tailWord_265221) baseStart_265221 baseEnd_265221 := by
    simpa [prefixWord, tailWord_265221, baseEnd_265221] using wordTrace_append hprefix tailTrace_265221
  have hstable : (prefixWord ++ tailWord_265221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265221).length < 2 ^ (prefixWord ++ tailWord_265221).sum := by decide
  have hdescent : baseEnd_265221 < baseStart_265221 := by decide
  rcases family_descends (prefixWord ++ tailWord_265221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265223 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 2, 4]
def baseStart_265223 : Nat := 118140960795 + 265223 * 2 ^ 59
def prefixEnd_265223 : Nat := 4983230072969 + 3 ^ 40 * 265223 * 2
def baseEnd_265223 : Nat := 90791253085014031661845

theorem tailTrace_265223 : CollatzResearch.WordTrace tailWord_265223 prefixEnd_265223 90791253085014031661845 := by
  unfold tailWord_265223
  simp only [CollatzResearch.WordTrace]
  refine ⟨9673477518149842327272323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6448985012099894884848215 9673477518149842327272323)
  ·
    refine ⟨14510216277224763490908485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9673477518149842327272323 14510216277224763490908485)
    ·
      refine ⟨2720665551979643154545341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14510216277224763490908485 2720665551979643154545341)
      ·
        refine ⟨1020249581992366182954503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2720665551979643154545341 1020249581992366182954503)
        ·
          refine ⟨1530374372988549274431755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020249581992366182954503 1530374372988549274431755)
          ·
            refine ⟨2295561559482823911647633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530374372988549274431755 2295561559482823911647633)
            ·
              refine ⟨1721671169612117933735725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295561559482823911647633 1721671169612117933735725)
              ·
                refine ⟨645626688604544225150897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1721671169612117933735725 645626688604544225150897)
                ·
                  refine ⟨484220016453408168863173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 645626688604544225150897 484220016453408168863173)
                  ·
                    refine ⟨90791253085014031661845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 484220016453408168863173 90791253085014031661845)
                    ·
                      rfl

theorem cell22_265223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_265223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265223 prefixEnd_265223 := by exact prefixLift 265223
  have htrace : WordTrace (prefixWord ++ tailWord_265223) baseStart_265223 baseEnd_265223 := by
    simpa [prefixWord, tailWord_265223, baseEnd_265223] using wordTrace_append hprefix tailTrace_265223
  have hstable : (prefixWord ++ tailWord_265223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265223).length < 2 ^ (prefixWord ++ tailWord_265223).sum := by decide
  have hdescent : baseEnd_265223 < baseStart_265223 := by decide
  rcases family_descends (prefixWord ++ tailWord_265223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265255 : List Nat := [1, 1, 7, 1, 1, 2, 2, 7]
def baseStart_265255 : Nat := 118140960795 + 265255 * 2 ^ 59
def prefixEnd_265255 : Nat := 4983230072969 + 3 ^ 40 * 265255 * 2
def baseEnd_265255 : Nat := 10089134148775179429083

theorem tailTrace_265255 : CollatzResearch.WordTrace tailWord_265255 prefixEnd_265255 10089134148775179429083 := by
  unfold tailWord_265255
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674644654033911792437219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6449763102689274528291479 9674644654033911792437219)
  ·
    refine ⟨14511966981050867688655829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9674644654033911792437219 14511966981050867688655829)
    ·
      refine ⟨340124226118379711452871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14511966981050867688655829 340124226118379711452871)
      ·
        refine ⟨510186339177569567179307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340124226118379711452871 510186339177569567179307)
        ·
          refine ⟨765279508766354350768961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510186339177569567179307 765279508766354350768961)
          ·
            refine ⟨573959631574765763076721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765279508766354350768961 573959631574765763076721)
            ·
              refine ⟨430469723681074322307541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573959631574765763076721 430469723681074322307541)
              ·
                refine ⟨10089134148775179429083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 430469723681074322307541 10089134148775179429083)
                ·
                  rfl

theorem cell22_265255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 7].length) (baseStart_265255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265255 prefixEnd_265255 := by exact prefixLift 265255
  have htrace : WordTrace (prefixWord ++ tailWord_265255) baseStart_265255 baseEnd_265255 := by
    simpa [prefixWord, tailWord_265255, baseEnd_265255] using wordTrace_append hprefix tailTrace_265255
  have hstable : (prefixWord ++ tailWord_265255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265255).length < 2 ^ (prefixWord ++ tailWord_265255).sum := by decide
  have hdescent : baseEnd_265255 < baseStart_265255 := by decide
  rcases family_descends (prefixWord ++ tailWord_265255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265313 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_265313 : Nat := 118140960795 + 265313 * 2 ^ 59
def prefixEnd_265313 : Nat := 4983230072969 + 3 ^ 40 * 265313 * 2
def baseEnd_265313 : Nat := 90822061924283796911569

theorem tailTrace_265313 : CollatzResearch.WordTrace tailWord_265313 prefixEnd_265313 90822061924283796911569 := by
  unfold tailWord_265313
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676760087823787698048593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6451173391882525132032395 9676760087823787698048593)
  ·
    refine ⟨7257570065867840773536445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9676760087823787698048593 7257570065867840773536445)
    ·
      refine ⟨2721588774700440290076167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7257570065867840773536445 2721588774700440290076167)
      ·
        refine ⟨4082383162050660435114251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721588774700440290076167 4082383162050660435114251)
        ·
          refine ⟨6123574743075990652671377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082383162050660435114251 6123574743075990652671377)
          ·
            refine ⟨4592681057306992989503533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6123574743075990652671377 4592681057306992989503533)
            ·
              refine ⟨1722255396490122371063825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4592681057306992989503533 1722255396490122371063825)
              ·
                refine ⟨1291691547367591778297869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722255396490122371063825 1291691547367591778297869)
                ·
                  refine ⟨484384330262846916861701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1291691547367591778297869 484384330262846916861701)
                  ·
                    refine ⟨90822061924283796911569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 484384330262846916861701 90822061924283796911569)
                    ·
                      rfl

theorem cell22_265313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_265313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265313 prefixEnd_265313 := by exact prefixLift 265313
  have htrace : WordTrace (prefixWord ++ tailWord_265313) baseStart_265313 baseEnd_265313 := by
    simpa [prefixWord, tailWord_265313, baseEnd_265313] using wordTrace_append hprefix tailTrace_265313
  have hstable : (prefixWord ++ tailWord_265313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265313).length < 2 ^ (prefixWord ++ tailWord_265313).sum := by decide
  have hdescent : baseEnd_265313 < baseStart_265313 := by decide
  rcases family_descends (prefixWord ++ tailWord_265313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265328 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 6]
def baseStart_265328 : Nat := 118140960795 + 265328 * 2 ^ 59
def prefixEnd_265328 : Nat := 4983230072969 + 3 ^ 40 * 265328 * 2
def baseEnd_265328 : Nat := 30275732243609585928841

theorem tailTrace_265328 : CollatzResearch.WordTrace tailWord_265328 prefixEnd_265328 30275732243609585928841 := by
  unfold tailWord_265328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838653591384722629922319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6451538121846296839896425 4838653591384722629922319)
  ·
    refine ⟨7257980387077083944883479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4838653591384722629922319 7257980387077083944883479)
    ·
      refine ⟨10886970580615625917325219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7257980387077083944883479 10886970580615625917325219)
      ·
        refine ⟨16330455870923438875987829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10886970580615625917325219 16330455870923438875987829)
        ·
          refine ⟨1530980237899072394623859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16330455870923438875987829 1530980237899072394623859)
          ·
            refine ⟨2296470356848608591935789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530980237899072394623859 2296470356848608591935789)
            ·
              refine ⟨861176383818228221975921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2296470356848608591935789 861176383818228221975921)
              ·
                refine ⟨645882287863671166481941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861176383818228221975921 645882287863671166481941)
                ·
                  refine ⟨30275732243609585928841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 645882287863671166481941 30275732243609585928841)
                  ·
                    rfl

theorem cell22_265328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_265328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265328 prefixEnd_265328 := by exact prefixLift 265328
  have htrace : WordTrace (prefixWord ++ tailWord_265328) baseStart_265328 baseEnd_265328 := by
    simpa [prefixWord, tailWord_265328, baseEnd_265328] using wordTrace_append hprefix tailTrace_265328
  have hstable : (prefixWord ++ tailWord_265328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265328).length < 2 ^ (prefixWord ++ tailWord_265328).sum := by decide
  have hdescent : baseEnd_265328 < baseStart_265328 := by decide
  rcases family_descends (prefixWord ++ tailWord_265328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265330 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_265330 : Nat := 118140960795 + 265330 * 2 ^ 59
def prefixEnd_265330 : Nat := 4983230072969 + 3 ^ 40 * 265330 * 2
def baseEnd_265330 : Nat := 90827881371701419236517

theorem tailTrace_265330 : CollatzResearch.WordTrace tailWord_265330 prefixEnd_265330 90827881371701419236517 := by
  unfold tailWord_265330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419345032190549900354361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6451586752508133067611629 2419345032190549900354361)
  ·
    refine ⟨1814508774142912425265771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2419345032190549900354361 1814508774142912425265771)
    ·
      refine ⟨2721763161214368637898657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814508774142912425265771 2721763161214368637898657)
      ·
        refine ⟨2041322370910776478423993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2721763161214368637898657 2041322370910776478423993)
        ·
          refine ⟨1530991778183082358817995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2041322370910776478423993 1530991778183082358817995)
          ·
            refine ⟨2296487667274623538226993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530991778183082358817995 2296487667274623538226993)
            ·
              refine ⟨1722365750455967653670245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296487667274623538226993 1722365750455967653670245)
              ·
                refine ⟨322943578210493935063171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1722365750455967653670245 322943578210493935063171)
                ·
                  refine ⟨484415367315740902594757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322943578210493935063171 484415367315740902594757)
                  ·
                    refine ⟨90827881371701419236517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 484415367315740902594757 90827881371701419236517)
                    ·
                      rfl

theorem cell22_265330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_265330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265330 prefixEnd_265330 := by exact prefixLift 265330
  have htrace : WordTrace (prefixWord ++ tailWord_265330) baseStart_265330 baseEnd_265330 := by
    simpa [prefixWord, tailWord_265330, baseEnd_265330] using wordTrace_append hprefix tailTrace_265330
  have hstable : (prefixWord ++ tailWord_265330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265330).length < 2 ^ (prefixWord ++ tailWord_265330).sum := by decide
  have hdescent : baseEnd_265330 < baseStart_265330 := by decide
  rcases family_descends (prefixWord ++ tailWord_265330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265360 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 2, 3]
def baseStart_265360 : Nat := 118140960795 + 265360 * 2 ^ 59
def prefixEnd_265360 : Nat := 4983230072969 + 3 ^ 40 * 265360 * 2
def baseEnd_265360 : Nat := 90838150984791340986425

theorem tailTrace_265360 : CollatzResearch.WordTrace tailWord_265360 prefixEnd_265360 90838150984791340986425 := by
  unfold tailWord_265360
  simp only [CollatzResearch.WordTrace]
  refine ⟨4839237159326757362504767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6452316212435676483339689 4839237159326757362504767)
  ·
    refine ⟨7258855738990136043757151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4839237159326757362504767 7258855738990136043757151)
    ·
      refine ⟨10888283608485204065635727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7258855738990136043757151 10888283608485204065635727)
      ·
        refine ⟨16332425412727806098453591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10888283608485204065635727 16332425412727806098453591)
        ·
          refine ⟨24498638119091709147680387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16332425412727806098453591 24498638119091709147680387)
          ·
            refine ⟨36747957178637563721520581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24498638119091709147680387 36747957178637563721520581)
            ·
              refine ⟨6890241970994543197785109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36747957178637563721520581 6890241970994543197785109)
              ·
                refine ⟨322980092390369212396177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6890241970994543197785109 322980092390369212396177)
                ·
                  refine ⟨242235069292776909297133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322980092390369212396177 242235069292776909297133)
                  ·
                    refine ⟨90838150984791340986425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242235069292776909297133 90838150984791340986425)
                    ·
                      rfl

theorem cell22_265360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_265360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265360 prefixEnd_265360 := by exact prefixLift 265360
  have htrace : WordTrace (prefixWord ++ tailWord_265360) baseStart_265360 baseEnd_265360 := by
    simpa [prefixWord, tailWord_265360, baseEnd_265360] using wordTrace_append hprefix tailTrace_265360
  have hstable : (prefixWord ++ tailWord_265360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265360).length < 2 ^ (prefixWord ++ tailWord_265360).sum := by decide
  have hdescent : baseEnd_265360 < baseStart_265360 := by decide
  rcases family_descends (prefixWord ++ tailWord_265360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265362 : List Nat := [3, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_265362 : Nat := 118140960795 + 265362 * 2 ^ 59
def prefixEnd_265362 : Nat := 4983230072969 + 3 ^ 40 * 265362 * 2
def baseEnd_265362 : Nat := 30279611875221334145473

theorem tailTrace_265362 : CollatzResearch.WordTrace tailWord_265362 prefixEnd_265362 30279611875221334145473 := by
  unfold tailWord_265362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419636816161567266645585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6452364843097512711054893 2419636816161567266645585)
  ·
    refine ⟨1814727612121175449984189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2419636816161567266645585 1814727612121175449984189)
    ·
      refine ⟨680522854545440793744071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1814727612121175449984189 680522854545440793744071)
      ·
        refine ⟨1020784281818161190616107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680522854545440793744071 1020784281818161190616107)
        ·
          refine ⟨1531176422727241785924161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020784281818161190616107 1531176422727241785924161)
          ·
            refine ⟨1148382317045431339443121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1531176422727241785924161 1148382317045431339443121)
            ·
              refine ⟨861286737784073504582341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148382317045431339443121 861286737784073504582341)
              ·
                refine ⟨161491263334513782109189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 861286737784073504582341 161491263334513782109189)
                ·
                  refine ⟨30279611875221334145473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161491263334513782109189 30279611875221334145473)
                  ·
                    rfl

theorem cell22_265362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_265362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265362 prefixEnd_265362 := by exact prefixLift 265362
  have htrace : WordTrace (prefixWord ++ tailWord_265362) baseStart_265362 baseEnd_265362 := by
    simpa [prefixWord, tailWord_265362, baseEnd_265362] using wordTrace_append hprefix tailTrace_265362
  have hstable : (prefixWord ++ tailWord_265362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265362).length < 2 ^ (prefixWord ++ tailWord_265362).sum := by decide
  have hdescent : baseEnd_265362 < baseStart_265362 := by decide
  rcases family_descends (prefixWord ++ tailWord_265362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265373 : List Nat := [1, 4, 2, 1, 1, 2, 2, 9]
def baseStart_265373 : Nat := 118140960795 + 265373 * 2 ^ 59
def prefixEnd_265373 : Nat := 4983230072969 + 3 ^ 40 * 265373 * 2
def baseEnd_265373 : Nat := 10093622350051515601265

theorem tailTrace_265373 : CollatzResearch.WordTrace tailWord_265373 prefixEnd_265373 10093622350051515601265 := by
  unfold tailWord_265373
  simp only [CollatzResearch.WordTrace]
  refine ⟨9678948467606417945232773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6452632311737611963488515 9678948467606417945232773)
  ·
    refine ⟨1814802837676203364731145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9678948467606417945232773 1814802837676203364731145)
    ·
      refine ⟨1361102128257152523548359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1814802837676203364731145 1361102128257152523548359)
      ·
        refine ⟨2041653192385728785322539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1361102128257152523548359 2041653192385728785322539)
        ·
          refine ⟨3062479788578593177983809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041653192385728785322539 3062479788578593177983809)
          ·
            refine ⟨2296859841433944883487857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3062479788578593177983809 2296859841433944883487857)
            ·
              refine ⟨1722644881075458662615893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296859841433944883487857 1722644881075458662615893)
              ·
                refine ⟨10093622350051515601265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1722644881075458662615893 10093622350051515601265)
                ·
                  rfl

theorem cell22_265373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 9].length) (baseStart_265373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265373 prefixEnd_265373 := by exact prefixLift 265373
  have htrace : WordTrace (prefixWord ++ tailWord_265373) baseStart_265373 baseEnd_265373 := by
    simpa [prefixWord, tailWord_265373, baseEnd_265373] using wordTrace_append hprefix tailTrace_265373
  have hstable : (prefixWord ++ tailWord_265373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265373).length < 2 ^ (prefixWord ++ tailWord_265373).sum := by decide
  have hdescent : baseEnd_265373 < baseStart_265373 := by decide
  rcases family_descends (prefixWord ++ tailWord_265373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265405 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_265405 : Nat := 118140960795 + 265405 * 2 ^ 59
def prefixEnd_265405 : Nat := 4983230072969 + 3 ^ 40 * 265405 * 2
def baseEnd_265405 : Nat := 90853555404426223611287

theorem tailTrace_265405 : CollatzResearch.WordTrace tailWord_265405 prefixEnd_265405 90853555404426223611287 := by
  unfold tailWord_265405
  simp only [CollatzResearch.WordTrace]
  refine ⟨9680115603490487410397669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6453410402326991606931779 9680115603490487410397669)
  ·
    refine ⟨1815021675654466389449563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9680115603490487410397669 1815021675654466389449563)
    ·
      refine ⟨2722532513481699584174345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815021675654466389449563 2722532513481699584174345)
      ·
        refine ⟨2041899385111274688130759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2722532513481699584174345 2041899385111274688130759)
        ·
          refine ⟨3062849077666912032196139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041899385111274688130759 3062849077666912032196139)
          ·
            refine ⟨4594273616500368048294209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062849077666912032196139 4594273616500368048294209)
            ·
              refine ⟨3445705212375276036220657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4594273616500368048294209 3445705212375276036220657)
              ·
                refine ⟨2584278909281457027165493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3445705212375276036220657 2584278909281457027165493)
                ·
                  refine ⟨242276147745136596296765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2584278909281457027165493 242276147745136596296765)
                  ·
                    refine ⟨90853555404426223611287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242276147745136596296765 90853555404426223611287)
                    ·
                      rfl

theorem cell22_265405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_265405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265405 prefixEnd_265405 := by exact prefixLift 265405
  have htrace : WordTrace (prefixWord ++ tailWord_265405) baseStart_265405 baseEnd_265405 := by
    simpa [prefixWord, tailWord_265405, baseEnd_265405] using wordTrace_append hprefix tailTrace_265405
  have hstable : (prefixWord ++ tailWord_265405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265405).length < 2 ^ (prefixWord ++ tailWord_265405).sum := by decide
  have hdescent : baseEnd_265405 < baseStart_265405 := by decide
  rcases family_descends (prefixWord ++ tailWord_265405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265428 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_265428 : Nat := 118140960795 + 265428 * 2 ^ 59
def prefixEnd_265428 : Nat := 4983230072969 + 3 ^ 40 * 265428 * 2
def baseEnd_265428 : Nat := 90861428774461830286217

theorem tailTrace_265428 : CollatzResearch.WordTrace tailWord_265428 prefixEnd_265428 90861428774461830286217 := by
  unfold tailWord_265428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840477241203581169242469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6453969654938108225656625 4840477241203581169242469)
  ·
    refine ⟨907589482725671469232963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4840477241203581169242469 907589482725671469232963)
    ·
      refine ⟨1361384224088507203849445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907589482725671469232963 1361384224088507203849445)
      ·
        refine ⟨255259542016595100721771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1361384224088507203849445 255259542016595100721771)
        ·
          refine ⟨382889313024892651082657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255259542016595100721771 382889313024892651082657)
          ·
            refine ⟨287166984768669488311993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382889313024892651082657 287166984768669488311993)
            ·
              refine ⟨215375238576502116233995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287166984768669488311993 215375238576502116233995)
              ·
                refine ⟨323062857864753174350993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215375238576502116233995 323062857864753174350993)
                ·
                  refine ⟨242297143398564880763245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323062857864753174350993 242297143398564880763245)
                  ·
                    refine ⟨90861428774461830286217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242297143398564880763245 90861428774461830286217)
                    ·
                      rfl

theorem cell22_265428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_265428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265428 prefixEnd_265428 := by exact prefixLift 265428
  have htrace : WordTrace (prefixWord ++ tailWord_265428) baseStart_265428 baseEnd_265428 := by
    simpa [prefixWord, tailWord_265428, baseEnd_265428] using wordTrace_append hprefix tailTrace_265428
  have hstable : (prefixWord ++ tailWord_265428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265428).length < 2 ^ (prefixWord ++ tailWord_265428).sum := by decide
  have hdescent : baseEnd_265428 < baseStart_265428 := by decide
  rcases family_descends (prefixWord ++ tailWord_265428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265433 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_265433 : Nat := 118140960795 + 265433 * 2 ^ 59
def prefixEnd_265433 : Nat := 4983230072969 + 3 ^ 40 * 265433 * 2
def baseEnd_265433 : Nat := 90863140376643483911201

theorem tailTrace_265433 : CollatzResearch.WordTrace tailWord_265433 prefixEnd_265433 90863140376643483911201 := by
  unfold tailWord_265433
  simp only [CollatzResearch.WordTrace]
  refine ⟨9681136847389048192416953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6454091231592698794944635 9681136847389048192416953)
  ·
    refine ⟨7260852635541786144312715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9681136847389048192416953 7260852635541786144312715)
    ·
      refine ⟨10891278953312679216469073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7260852635541786144312715 10891278953312679216469073)
      ·
        refine ⟨8168459214984509412351805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10891278953312679216469073 8168459214984509412351805)
        ·
          refine ⟨3063172205619191029631927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8168459214984509412351805 3063172205619191029631927)
          ·
            refine ⟨4594758308428786544447891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063172205619191029631927 4594758308428786544447891)
            ·
              refine ⟨6892137462643179816671837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594758308428786544447891 6892137462643179816671837)
              ·
                refine ⟨2584551548491192431251939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6892137462643179816671837 2584551548491192431251939)
                ·
                  refine ⟨3876827322736788646877909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584551548491192431251939 3876827322736788646877909)
                  ·
                    refine ⟨90863140376643483911201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3876827322736788646877909 90863140376643483911201)
                    ·
                      rfl

theorem cell22_265433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_265433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265433 prefixEnd_265433 := by exact prefixLift 265433
  have htrace : WordTrace (prefixWord ++ tailWord_265433) baseStart_265433 baseEnd_265433 := by
    simpa [prefixWord, tailWord_265433, baseEnd_265433] using wordTrace_append hprefix tailTrace_265433
  have hstable : (prefixWord ++ tailWord_265433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265433).length < 2 ^ (prefixWord ++ tailWord_265433).sum := by decide
  have hdescent : baseEnd_265433 < baseStart_265433 := by decide
  rcases family_descends (prefixWord ++ tailWord_265433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265463 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 8]
def baseStart_265463 : Nat := 118140960795 + 265463 * 2 ^ 59
def prefixEnd_265463 : Nat := 4983230072969 + 3 ^ 40 * 265463 * 2
def baseEnd_265463 : Nat := 30291136663244468553703

theorem tailTrace_265463 : CollatzResearch.WordTrace tailWord_265463 prefixEnd_265463 30291136663244468553703 := by
  unfold tailWord_265463
  simp only [CollatzResearch.WordTrace]
  refine ⟨9682231037280363316009043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6454820691520242210672695 9682231037280363316009043)
  ·
    refine ⟨14523346555920544974013565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9682231037280363316009043 14523346555920544974013565)
    ·
      refine ⟨5446254958470204365255087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14523346555920544974013565 5446254958470204365255087)
      ·
        refine ⟨8169382437705306547882631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5446254958470204365255087 8169382437705306547882631)
        ·
          refine ⟨12254073656557959821823947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8169382437705306547882631 12254073656557959821823947)
          ·
            refine ⟨18381110484836939732735921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12254073656557959821823947 18381110484836939732735921)
            ·
              refine ⟨13785832863627704799551941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18381110484836939732735921 13785832863627704799551941)
              ·
                refine ⟨2584843661930194649915989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13785832863627704799551941 2584843661930194649915989)
                ·
                  refine ⟨30291136663244468553703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2584843661930194649915989 30291136663244468553703)
                  ·
                    rfl

theorem cell22_265463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 8].length) (baseStart_265463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265463 prefixEnd_265463 := by exact prefixLift 265463
  have htrace : WordTrace (prefixWord ++ tailWord_265463) baseStart_265463 baseEnd_265463 := by
    simpa [prefixWord, tailWord_265463, baseEnd_265463] using wordTrace_append hprefix tailTrace_265463
  have hstable : (prefixWord ++ tailWord_265463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265463).length < 2 ^ (prefixWord ++ tailWord_265463).sum := by decide
  have hdescent : baseEnd_265463 < baseStart_265463 := by decide
  rcases family_descends (prefixWord ++ tailWord_265463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265512 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_265512 : Nat := 118140960795 + 265512 * 2 ^ 59
def prefixEnd_265512 : Nat := 4983230072969 + 3 ^ 40 * 265512 * 2
def baseEnd_265512 : Nat := 90890183691113611185959

theorem tailTrace_265512 : CollatzResearch.WordTrace tailWord_265512 prefixEnd_265512 90890183691113611185959 := by
  unfold tailWord_265512
  simp only [CollatzResearch.WordTrace]
  refine ⟨4842009107051422342271395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6456012142735229789695193 4842009107051422342271395)
  ·
    refine ⟨7263013660577133513407093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4842009107051422342271395 7263013660577133513407093)
    ·
      refine ⟨680907530679106266881915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7263013660577133513407093 680907530679106266881915)
      ·
        refine ⟨1021361296018659400322873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680907530679106266881915 1021361296018659400322873)
        ·
          refine ⟨766020972013994550242155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021361296018659400322873 766020972013994550242155)
          ·
            refine ⟨1149031458020991825363233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766020972013994550242155 1149031458020991825363233)
            ·
              refine ⟨861773593515743869022425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149031458020991825363233 861773593515743869022425)
              ·
                refine ⟨646330195136807901766819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861773593515743869022425 646330195136807901766819)
                ·
                  refine ⟨969495292705211852650229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646330195136807901766819 969495292705211852650229)
                  ·
                    refine ⟨90890183691113611185959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 969495292705211852650229 90890183691113611185959)
                    ·
                      rfl

theorem cell22_265512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_265512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265512 prefixEnd_265512 := by exact prefixLift 265512
  have htrace : WordTrace (prefixWord ++ tailWord_265512) baseStart_265512 baseEnd_265512 := by
    simpa [prefixWord, tailWord_265512, baseEnd_265512] using wordTrace_append hprefix tailTrace_265512
  have hstable : (prefixWord ++ tailWord_265512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265512).length < 2 ^ (prefixWord ++ tailWord_265512).sum := by decide
  have hdescent : baseEnd_265512 < baseStart_265512 := by decide
  rcases family_descends (prefixWord ++ tailWord_265512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265514 : List Nat := [3, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_265514 : Nat := 118140960795 + 265514 * 2 ^ 59
def prefixEnd_265514 : Nat := 4983230072969 + 3 ^ 40 * 265514 * 2
def baseEnd_265514 : Nat := 30296956110662090878651

theorem tailTrace_265514 : CollatzResearch.WordTrace tailWord_265514 prefixEnd_265514 30296956110662090878651 := by
  unfold tailWord_265514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421022790023899756528899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6456060773397066017410397 2421022790023899756528899)
  ·
    refine ⟨3631534185035849634793349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2421022790023899756528899 3631534185035849634793349)
    ·
      refine ⟨680912659694221806523753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3631534185035849634793349 680912659694221806523753)
      ·
        refine ⟨510684494770666354892815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680912659694221806523753 510684494770666354892815)
        ·
          refine ⟨766026742155999532339223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510684494770666354892815 766026742155999532339223)
          ·
            refine ⟨1149040113233999298508835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766026742155999532339223 1149040113233999298508835)
            ·
              refine ⟨1723560169850998947763253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149040113233999298508835 1723560169850998947763253)
              ·
                refine ⟨161583765923531151352805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1723560169850998947763253 161583765923531151352805)
                ·
                  refine ⟨30296956110662090878651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161583765923531151352805 30296956110662090878651)
                  ·
                    rfl

theorem cell22_265514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_265514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265514 prefixEnd_265514 := by exact prefixLift 265514
  have htrace : WordTrace (prefixWord ++ tailWord_265514) baseStart_265514 baseEnd_265514 := by
    simpa [prefixWord, tailWord_265514, baseEnd_265514] using wordTrace_append hprefix tailTrace_265514
  have hstable : (prefixWord ++ tailWord_265514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265514).length < 2 ^ (prefixWord ++ tailWord_265514).sum := by decide
  have hdescent : baseEnd_265514 < baseStart_265514 := by decide
  rcases family_descends (prefixWord ++ tailWord_265514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265525 : List Nat := [1, 3, 3, 1, 2, 3, 9]
def baseStart_265525 : Nat := 118140960795 + 265525 * 2 ^ 59
def prefixEnd_265525 : Nat := 4983230072969 + 3 ^ 40 * 265525 * 2
def baseEnd_265525 : Nat := 3366467920621700392997

theorem tailTrace_265525 : CollatzResearch.WordTrace tailWord_265525 prefixEnd_265525 3366467920621700392997 := by
  unfold tailWord_265525
  simp only [CollatzResearch.WordTrace]
  refine ⟨9684492363055747904766029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6456328242037165269844019 9684492363055747904766029)
  ·
    refine ⟨3631684636145905464287261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9684492363055747904766029 3631684636145905464287261)
    ·
      refine ⟨1361881738554714549107723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3631684636145905464287261 1361881738554714549107723)
      ·
        refine ⟨2042822607832071823661585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1361881738554714549107723 2042822607832071823661585)
        ·
          refine ⟨1532116955874053867746189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2042822607832071823661585 1532116955874053867746189)
          ·
            refine ⟨574543858452770200404821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1532116955874053867746189 574543858452770200404821)
            ·
              refine ⟨3366467920621700392997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 574543858452770200404821 3366467920621700392997)
              ·
                rfl

theorem cell22_265525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 9].length) (baseStart_265525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265525 prefixEnd_265525 := by exact prefixLift 265525
  have htrace : WordTrace (prefixWord ++ tailWord_265525) baseStart_265525 baseEnd_265525 := by
    simpa [prefixWord, tailWord_265525, baseEnd_265525] using wordTrace_append hprefix tailTrace_265525
  have hstable : (prefixWord ++ tailWord_265525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265525).length < 2 ^ (prefixWord ++ tailWord_265525).sum := by decide
  have hdescent : baseEnd_265525 < baseStart_265525 := by decide
  rcases family_descends (prefixWord ++ tailWord_265525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265529 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 4, 3]
def baseStart_265529 : Nat := 118140960795 + 265529 * 2 ^ 59
def prefixEnd_265529 : Nat := 4983230072969 + 3 ^ 40 * 265529 * 2
def baseEnd_265529 : Nat := 90896003138531233510907

theorem tailTrace_265529 : CollatzResearch.WordTrace tailWord_265529 prefixEnd_265529 90896003138531233510907 := by
  unfold tailWord_265529
  simp only [CollatzResearch.WordTrace]
  refine ⟨9684638255041256587911641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6456425503360837725274427 9684638255041256587911641)
  ·
    refine ⟨7263478691280942440933731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9684638255041256587911641 7263478691280942440933731)
    ·
      refine ⟨10895218036921413661400597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7263478691280942440933731 10895218036921413661400597)
      ·
        refine ⟨510713345480691265378153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10895218036921413661400597 510713345480691265378153)
        ·
          refine ⟨383035009110518449033615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510713345480691265378153 383035009110518449033615)
          ·
            refine ⟨574552513665777673550423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383035009110518449033615 574552513665777673550423)
            ·
              refine ⟨861828770498666510325635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574552513665777673550423 861828770498666510325635)
              ·
                refine ⟨1292743155747999765488453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861828770498666510325635 1292743155747999765488453)
                ·
                  refine ⟨242389341702749956029085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1292743155747999765488453 242389341702749956029085)
                  ·
                    refine ⟨90896003138531233510907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242389341702749956029085 90896003138531233510907)
                    ·
                      rfl

theorem cell22_265529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_265529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265529 prefixEnd_265529 := by exact prefixLift 265529
  have htrace : WordTrace (prefixWord ++ tailWord_265529) baseStart_265529 baseEnd_265529 := by
    simpa [prefixWord, tailWord_265529, baseEnd_265529] using wordTrace_append hprefix tailTrace_265529
  have hstable : (prefixWord ++ tailWord_265529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265529).length < 2 ^ (prefixWord ++ tailWord_265529).sum := by decide
  have hdescent : baseEnd_265529 < baseStart_265529 := by decide
  rcases family_descends (prefixWord ++ tailWord_265529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265565 : List Nat := [1, 4, 5, 1, 1, 2, 1, 3, 4]
def baseStart_265565 : Nat := 118140960795 + 265565 * 2 ^ 59
def prefixEnd_265565 : Nat := 4983230072969 + 3 ^ 40 * 265565 * 2
def baseEnd_265565 : Nat := 30302775558079713203599

theorem tailTrace_265565 : CollatzResearch.WordTrace tailWord_265565 prefixEnd_265565 30302775558079713203599 := by
  unfold tailWord_265565
  simp only [CollatzResearch.WordTrace]
  refine ⟨9685951282910834736222149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6457300855273889824148099 9685951282910834736222149)
  ·
    refine ⟨1816115865545781513041653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9685951282910834736222149 1816115865545781513041653)
    ·
      refine ⟨170260862394917016847655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1816115865545781513041653 170260862394917016847655)
      ·
        refine ⟨255391293592375525271483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170260862394917016847655 255391293592375525271483)
        ·
          refine ⟨383086940388563287907225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255391293592375525271483 383086940388563287907225)
          ·
            refine ⟨287315205291422465930419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383086940388563287907225 287315205291422465930419)
            ·
              refine ⟨430972807937133698895629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287315205291422465930419 430972807937133698895629)
              ·
                refine ⟨161614802976425137085861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430972807937133698895629 161614802976425137085861)
                ·
                  refine ⟨30302775558079713203599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161614802976425137085861 30302775558079713203599)
                  ·
                    rfl

theorem cell22_265565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_265565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265565 prefixEnd_265565 := by exact prefixLift 265565
  have htrace : WordTrace (prefixWord ++ tailWord_265565) baseStart_265565 baseEnd_265565 := by
    simpa [prefixWord, tailWord_265565, baseEnd_265565] using wordTrace_append hprefix tailTrace_265565
  have hstable : (prefixWord ++ tailWord_265565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265565).length < 2 ^ (prefixWord ++ tailWord_265565).sum := by decide
  have hdescent : baseEnd_265565 < baseStart_265565 := by decide
  rcases family_descends (prefixWord ++ tailWord_265565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265585 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_265585 : Nat := 118140960795 + 265585 * 2 ^ 59
def prefixEnd_265585 : Nat := 4983230072969 + 3 ^ 40 * 265585 * 2
def baseEnd_265585 : Nat := 90915173082965754110735

theorem tailTrace_265585 : CollatzResearch.WordTrace tailWord_265585 prefixEnd_265585 90915173082965754110735 := by
  unfold tailWord_265585
  simp only [CollatzResearch.WordTrace]
  refine ⟨9686680742838378151950209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6457787161892252101300139 9686680742838378151950209)
  ·
    refine ⟨7265010557128783613962657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9686680742838378151950209 7265010557128783613962657)
    ·
      refine ⟨5448757917846587710471993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7265010557128783613962657 5448757917846587710471993)
      ·
        refine ⟨4086568438384940782853995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5448757917846587710471993 4086568438384940782853995)
        ·
          refine ⟨6129852657577411174280993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086568438384940782853995 6129852657577411174280993)
          ·
            refine ⟨4597389493183058380710745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129852657577411174280993 4597389493183058380710745)
            ·
              refine ⟨3448042119887293785533059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4597389493183058380710745 3448042119887293785533059)
              ·
                refine ⟨5172063179830940678299589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448042119887293785533059 5172063179830940678299589)
                ·
                  refine ⟨969761846218301377181173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5172063179830940678299589 969761846218301377181173)
                  ·
                    refine ⟨90915173082965754110735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 969761846218301377181173 90915173082965754110735)
                    ·
                      rfl

theorem cell22_265585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_265585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265585 prefixEnd_265585 := by exact prefixLift 265585
  have htrace : WordTrace (prefixWord ++ tailWord_265585) baseStart_265585 baseEnd_265585 := by
    simpa [prefixWord, tailWord_265585, baseEnd_265585] using wordTrace_append hprefix tailTrace_265585
  have hstable : (prefixWord ++ tailWord_265585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265585).length < 2 ^ (prefixWord ++ tailWord_265585).sum := by decide
  have hdescent : baseEnd_265585 < baseStart_265585 := by decide
  rcases family_descends (prefixWord ++ tailWord_265585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265591 : List Nat := [1, 1, 3, 1, 1, 2, 7, 2, 1, 3]
def baseStart_265591 : Nat := 118140960795 + 265591 * 2 ^ 59
def prefixEnd_265591 : Nat := 4983230072969 + 3 ^ 40 * 265591 * 2
def baseEnd_265591 : Nat := 90917227005583738460717

theorem tailTrace_265591 : CollatzResearch.WordTrace tailWord_265591 prefixEnd_265591 90917227005583738460717 := by
  unfold tailWord_265591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9686899580816641176668627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6457933053877760784445751 9686899580816641176668627)
  ·
    refine ⟨14530349371224961765002941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9686899580816641176668627 14530349371224961765002941)
    ·
      refine ⟨5448881014209360661876103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14530349371224961765002941 5448881014209360661876103)
      ·
        refine ⟨8173321521314040992814155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5448881014209360661876103 8173321521314040992814155)
        ·
          refine ⟨12259982281971061489221233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8173321521314040992814155 12259982281971061489221233)
          ·
            refine ⟨9194986711478296116915925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12259982281971061489221233 9194986711478296116915925)
            ·
              refine ⟨215507501050272565240217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9194986711478296116915925 215507501050272565240217)
              ·
                refine ⟨161630625787704423930163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215507501050272565240217 161630625787704423930163)
                ·
                  refine ⟨242445938681556635895245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161630625787704423930163 242445938681556635895245)
                  ·
                    refine ⟨90917227005583738460717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242445938681556635895245 90917227005583738460717)
                    ·
                      rfl

theorem cell22_265591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_265591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265591 prefixEnd_265591 := by exact prefixLift 265591
  have htrace : WordTrace (prefixWord ++ tailWord_265591) baseStart_265591 baseEnd_265591 := by
    simpa [prefixWord, tailWord_265591, baseEnd_265591] using wordTrace_append hprefix tailTrace_265591
  have hstable : (prefixWord ++ tailWord_265591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265591).length < 2 ^ (prefixWord ++ tailWord_265591).sum := by decide
  have hdescent : baseEnd_265591 < baseStart_265591 := by decide
  rcases family_descends (prefixWord ++ tailWord_265591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265604 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 5]
def baseStart_265604 : Nat := 118140960795 + 265604 * 2 ^ 59
def prefixEnd_265604 : Nat := 4983230072969 + 3 ^ 40 * 265604 * 2
def baseEnd_265604 : Nat := 30307225723752012628559

theorem tailTrace_265604 : CollatzResearch.WordTrace tailWord_265604 prefixEnd_265604 30307225723752012628559 := by
  unfold tailWord_265604
  simp only [CollatzResearch.WordTrace]
  refine ⟨4843686864884772198445933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6458249153179696264594577 4843686864884772198445933)
  ·
    refine ⟨1816382574331789574417225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4843686864884772198445933 1816382574331789574417225)
    ·
      refine ⟨1362286930748842180812919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1816382574331789574417225 1362286930748842180812919)
      ·
        refine ⟨2043430396123263271219379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362286930748842180812919 2043430396123263271219379)
        ·
          refine ⟨3065145594184894906829069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043430396123263271219379 3065145594184894906829069)
          ·
            refine ⟨1149429597819335590060901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3065145594184894906829069 1149429597819335590060901)
            ·
              refine ⟨215518049591125423136419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1149429597819335590060901 215518049591125423136419)
              ·
                refine ⟨323277074386688134704629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215518049591125423136419 323277074386688134704629)
                ·
                  refine ⟨30307225723752012628559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323277074386688134704629 30307225723752012628559)
                  ·
                    rfl

theorem cell22_265604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_265604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265604 prefixEnd_265604 := by exact prefixLift 265604
  have htrace : WordTrace (prefixWord ++ tailWord_265604) baseStart_265604 baseEnd_265604 := by
    simpa [prefixWord, tailWord_265604, baseEnd_265604] using wordTrace_append hprefix tailTrace_265604
  have hstable : (prefixWord ++ tailWord_265604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265604).length < 2 ^ (prefixWord ++ tailWord_265604).sum := by decide
  have hdescent : baseEnd_265604 < baseStart_265604 := by decide
  rcases family_descends (prefixWord ++ tailWord_265604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265647 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 4, 3]
def baseStart_265647 : Nat := 118140960795 + 265647 * 2 ^ 59
def prefixEnd_265647 : Nat := 4983230072969 + 3 ^ 40 * 265647 * 2
def baseEnd_265647 : Nat := 90936396950018259060545

theorem tailTrace_265647 : CollatzResearch.WordTrace tailWord_265647 prefixEnd_265647 90936396950018259060545 := by
  unfold tailWord_265647
  simp only [CollatzResearch.WordTrace]
  refine ⟨9688942068613762740707195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6459294712409175160471463 9688942068613762740707195)
  ·
    refine ⟨14533413102920644111060793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9688942068613762740707195 14533413102920644111060793)
    ·
      refine ⟨10900059827190483083295595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14533413102920644111060793 10900059827190483083295595)
      ·
        refine ⟨16350089740785724624943393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10900059827190483083295595 16350089740785724624943393)
        ·
          refine ⟨12262567305589293468707545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16350089740785724624943393 12262567305589293468707545)
          ·
            refine ⟨9196925479191970101530659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12262567305589293468707545 9196925479191970101530659)
            ·
              refine ⟨13795388218787955152295989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9196925479191970101530659 13795388218787955152295989)
              ·
                refine ⟨1293317645511370795527749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13795388218787955152295989 1293317645511370795527749)
                ·
                  refine ⟨242497058533382024161453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293317645511370795527749 242497058533382024161453)
                  ·
                    refine ⟨90936396950018259060545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242497058533382024161453 90936396950018259060545)
                    ·
                      rfl

theorem cell22_265647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_265647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265647 prefixEnd_265647 := by exact prefixLift 265647
  have htrace : WordTrace (prefixWord ++ tailWord_265647) baseStart_265647 baseEnd_265647 := by
    simpa [prefixWord, tailWord_265647, baseEnd_265647] using wordTrace_append hprefix tailTrace_265647
  have hstable : (prefixWord ++ tailWord_265647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265647).length < 2 ^ (prefixWord ++ tailWord_265647).sum := by decide
  have hdescent : baseEnd_265647 < baseStart_265647 := by decide
  rcases family_descends (prefixWord ++ tailWord_265647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265649 : List Nat := [1, 2, 2, 4, 1, 1, 3, 4, 4]
def baseStart_265649 : Nat := 118140960795 + 265649 * 2 ^ 59
def prefixEnd_265649 : Nat := 4983230072969 + 3 ^ 40 * 265649 * 2
def baseEnd_265649 : Nat := 30312360530296973503513

theorem tailTrace_265649 : CollatzResearch.WordTrace tailWord_265649 prefixEnd_265649 30312360530296973503513 := by
  unfold tailWord_265649
  simp only [CollatzResearch.WordTrace]
  refine ⟨9689015014606517082280001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6459343343071011388186667 9689015014606517082280001)
  ·
    refine ⟨7266761260954887811710001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9689015014606517082280001 7266761260954887811710001)
    ·
      refine ⟨5450070945716165858782501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7266761260954887811710001 5450070945716165858782501)
      ·
        refine ⟨1021888302321781098521719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5450070945716165858782501 1021888302321781098521719)
        ·
          refine ⟨1532832453482671647782579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021888302321781098521719 1532832453482671647782579)
          ·
            refine ⟨2299248680224007471673869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532832453482671647782579 2299248680224007471673869)
            ·
              refine ⟨862218255084002801877701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2299248680224007471673869 862218255084002801877701)
              ·
                refine ⟨161665922828250525352069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 862218255084002801877701 161665922828250525352069)
                ·
                  refine ⟨30312360530296973503513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161665922828250525352069 30312360530296973503513)
                  ·
                    rfl

theorem cell22_265649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 4].length) (baseStart_265649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265649 prefixEnd_265649 := by exact prefixLift 265649
  have htrace : WordTrace (prefixWord ++ tailWord_265649) baseStart_265649 baseEnd_265649 := by
    simpa [prefixWord, tailWord_265649, baseEnd_265649] using wordTrace_append hprefix tailTrace_265649
  have hstable : (prefixWord ++ tailWord_265649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265649).length < 2 ^ (prefixWord ++ tailWord_265649).sum := by decide
  have hdescent : baseEnd_265649 < baseStart_265649 := by decide
  rcases family_descends (prefixWord ++ tailWord_265649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265662 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_265662 : Nat := 118140960795 + 265662 * 2 ^ 59
def prefixEnd_265662 : Nat := 4983230072969 + 3 ^ 40 * 265662 * 2
def baseEnd_265662 : Nat := 90941531756563219935499

theorem tailTrace_265662 : CollatzResearch.WordTrace tailWord_265662 prefixEnd_265662 90941531756563219935499 := by
  unfold tailWord_265662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1211186145444927537812905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6459659442372946868335493 1211186145444927537812905)
  ·
    refine ⟨908389609083695653359679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1211186145444927537812905 908389609083695653359679)
    ·
      refine ⟨1362584413625543480039519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908389609083695653359679 1362584413625543480039519)
      ·
        refine ⟨2043876620438315220059279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362584413625543480039519 2043876620438315220059279)
        ·
          refine ⟨3065814930657472830088919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043876620438315220059279 3065814930657472830088919)
          ·
            refine ⟨4598722395986209245133379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065814930657472830088919 4598722395986209245133379)
            ·
              refine ⟨6898083593979313867700069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598722395986209245133379 6898083593979313867700069)
              ·
                refine ⟨1293390673871121350193763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6898083593979313867700069 1293390673871121350193763)
                ·
                  refine ⟨1940086010806682025290645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293390673871121350193763 1940086010806682025290645)
                  ·
                    refine ⟨90941531756563219935499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1940086010806682025290645 90941531756563219935499)
                    ·
                      rfl

theorem cell22_265662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_265662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265662 prefixEnd_265662 := by exact prefixLift 265662
  have htrace : WordTrace (prefixWord ++ tailWord_265662) baseStart_265662 baseEnd_265662 := by
    simpa [prefixWord, tailWord_265662, baseEnd_265662] using wordTrace_append hprefix tailTrace_265662
  have hstable : (prefixWord ++ tailWord_265662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265662).length < 2 ^ (prefixWord ++ tailWord_265662).sum := by decide
  have hdescent : baseEnd_265662 < baseStart_265662 := by decide
  rcases family_descends (prefixWord ++ tailWord_265662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265664 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 2, 3]
def baseStart_265664 : Nat := 118140960795 + 265664 * 2 ^ 59
def prefixEnd_265664 : Nat := 4983230072969 + 3 ^ 40 * 265664 * 2
def baseEnd_265664 : Nat := 90942216397435881385493

theorem tailTrace_265664 : CollatzResearch.WordTrace tailWord_265664 prefixEnd_265664 90942216397435881385493 := by
  unfold tailWord_265664
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844781054776087322038023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6459708073034783096050697 4844781054776087322038023)
  ·
    refine ⟨7267171582164130983057035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4844781054776087322038023 7267171582164130983057035)
    ·
      refine ⟨10900757373246196474585553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7267171582164130983057035 10900757373246196474585553)
      ·
        refine ⟨8175568029934647355939165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10900757373246196474585553 8175568029934647355939165)
        ·
          refine ⟨3065838011225492758477187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8175568029934647355939165 3065838011225492758477187)
          ·
            refine ⟨4598757016838239137715781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065838011225492758477187 4598757016838239137715781)
            ·
              refine ⟨862266940657169838321709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4598757016838239137715781 862266940657169838321709)
              ·
                refine ⟨323350102746438689370641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 862266940657169838321709 323350102746438689370641)
                ·
                  refine ⟨242512577059829017027981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323350102746438689370641 242512577059829017027981)
                  ·
                    refine ⟨90942216397435881385493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242512577059829017027981 90942216397435881385493)
                    ·
                      rfl

theorem cell22_265664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_265664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265664 prefixEnd_265664 := by exact prefixLift 265664
  have htrace : WordTrace (prefixWord ++ tailWord_265664) baseStart_265664 baseEnd_265664 := by
    simpa [prefixWord, tailWord_265664, baseEnd_265664] using wordTrace_append hprefix tailTrace_265664
  have hstable : (prefixWord ++ tailWord_265664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265664).length < 2 ^ (prefixWord ++ tailWord_265664).sum := by decide
  have hdescent : baseEnd_265664 < baseStart_265664 := by decide
  rcases family_descends (prefixWord ++ tailWord_265664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265734 : List Nat := [6, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_265734 : Nat := 118140960795 + 265734 * 2 ^ 59
def prefixEnd_265734 : Nat := 4983230072969 + 3 ^ 40 * 265734 * 2
def baseEnd_265734 : Nat := 30322059609326344045093

theorem tailTrace_265734 : CollatzResearch.WordTrace tailWord_265734 prefixEnd_265734 30322059609326344045093 := by
  unfold tailWord_265734
  simp only [CollatzResearch.WordTrace]
  refine ⟨302878600603080518722633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6461410146199051066082837 302878600603080518722633)
  ·
    refine ⟨227158950452310389041975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302878600603080518722633 227158950452310389041975)
    ·
      refine ⟨340738425678465583562963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227158950452310389041975 340738425678465583562963)
      ·
        refine ⟨511107638517698375344445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340738425678465583562963 511107638517698375344445)
        ·
          refine ⟨191665364444136890754167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511107638517698375344445 191665364444136890754167)
          ·
            refine ⟨287498046666205336131251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191665364444136890754167 287498046666205336131251)
            ·
              refine ⟨431247069999308004196877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287498046666205336131251 431247069999308004196877)
              ·
                refine ⟨161717651249740501573829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431247069999308004196877 161717651249740501573829)
                ·
                  refine ⟨30322059609326344045093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161717651249740501573829 30322059609326344045093)
                  ·
                    rfl

theorem cell22_265734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_265734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265734 prefixEnd_265734 := by exact prefixLift 265734
  have htrace : WordTrace (prefixWord ++ tailWord_265734) baseStart_265734 baseEnd_265734 := by
    simpa [prefixWord, tailWord_265734, baseEnd_265734] using wordTrace_append hprefix tailTrace_265734
  have hstable : (prefixWord ++ tailWord_265734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265734).length < 2 ^ (prefixWord ++ tailWord_265734).sum := by decide
  have hdescent : baseEnd_265734 < baseStart_265734 := by decide
  rcases family_descends (prefixWord ++ tailWord_265734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265760 : List Nat := [2, 1, 1, 6, 1, 2, 3, 2, 1, 3]
def baseStart_265760 : Nat := 118140960795 + 265760 * 2 ^ 59
def prefixEnd_265760 : Nat := 4983230072969 + 3 ^ 40 * 265760 * 2
def baseEnd_265760 : Nat := 90975079159323630985199

theorem tailTrace_265760 : CollatzResearch.WordTrace tailWord_265760 prefixEnd_265760 90975079159323630985199 := by
  unfold tailWord_265760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846531758602191519785367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6462042344802922026380489 4846531758602191519785367)
  ·
    refine ⟨7269797637903287279678051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4846531758602191519785367 7269797637903287279678051)
    ·
      refine ⟨10904696456854930919517077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7269797637903287279678051 10904696456854930919517077)
      ·
        refine ⟨511157646415074886852363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10904696456854930919517077 511157646415074886852363)
        ·
          refine ⟨766736469622612330278545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511157646415074886852363 766736469622612330278545)
          ·
            refine ⟨575052352216959247708909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766736469622612330278545 575052352216959247708909)
            ·
              refine ⟨215644632081359717890841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575052352216959247708909 215644632081359717890841)
              ·
                refine ⟨161733474061019788418131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215644632081359717890841 161733474061019788418131)
                ·
                  refine ⟨242600211091529682627197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161733474061019788418131 242600211091529682627197)
                  ·
                    refine ⟨90975079159323630985199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242600211091529682627197 90975079159323630985199)
                    ·
                      rfl

theorem cell22_265760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 3].length) (baseStart_265760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265760 prefixEnd_265760 := by exact prefixLift 265760
  have htrace : WordTrace (prefixWord ++ tailWord_265760) baseStart_265760 baseEnd_265760 := by
    simpa [prefixWord, tailWord_265760, baseEnd_265760] using wordTrace_append hprefix tailTrace_265760
  have hstable : (prefixWord ++ tailWord_265760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265760).length < 2 ^ (prefixWord ++ tailWord_265760).sum := by decide
  have hdescent : baseEnd_265760 < baseStart_265760 := by decide
  rcases family_descends (prefixWord ++ tailWord_265760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265829 : List Nat := [1, 3, 1, 3, 3, 1, 3, 7]
def baseStart_265829 : Nat := 118140960795 + 265829 * 2 ^ 59
def prefixEnd_265829 : Nat := 4983230072969 + 3 ^ 40 * 265829 * 2
def baseEnd_265829 : Nat := 10110966585492272334443

theorem tailTrace_265829 : CollatzResearch.WordTrace tailWord_265829 prefixEnd_265829 10110966585492272334443 := by
  unfold tailWord_265829
  simp only [CollatzResearch.WordTrace]
  refine ⟨9695580153954407823832541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6463720102636271882555027 9695580153954407823832541)
  ·
    refine ⟨3635842557732902933937203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9695580153954407823832541 3635842557732902933937203)
    ·
      refine ⟨5453763836599354400905805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3635842557732902933937203 5453763836599354400905805)
      ·
        refine ⟨2045161438724757900339677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5453763836599354400905805 2045161438724757900339677)
        ·
          refine ⟨766935539521784212627379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2045161438724757900339677 766935539521784212627379)
          ·
            refine ⟨1150403309282676318941069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766935539521784212627379 1150403309282676318941069)
            ·
              refine ⟨431401240981003619602901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1150403309282676318941069 431401240981003619602901)
              ·
                refine ⟨10110966585492272334443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 431401240981003619602901 10110966585492272334443)
                ·
                  rfl

theorem cell22_265829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 7].length) (baseStart_265829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265829 prefixEnd_265829 := by exact prefixLift 265829
  have htrace : WordTrace (prefixWord ++ tailWord_265829) baseStart_265829 baseEnd_265829 := by
    simpa [prefixWord, tailWord_265829, baseEnd_265829] using wordTrace_append hprefix tailTrace_265829
  have hstable : (prefixWord ++ tailWord_265829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265829).length < 2 ^ (prefixWord ++ tailWord_265829).sum := by decide
  have hdescent : baseEnd_265829 < baseStart_265829 := by decide
  rcases family_descends (prefixWord ++ tailWord_265829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265891 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 5]
def baseStart_265891 : Nat := 118140960795 + 265891 * 2 ^ 59
def prefixEnd_265891 : Nat := 4983230072969 + 3 ^ 40 * 265891 * 2
def baseEnd_265891 : Nat := 30339974378827651986599

theorem tailTrace_265891 : CollatzResearch.WordTrace tailWord_265891 prefixEnd_265891 30339974378827651986599 := by
  unfold tailWord_265891
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697841479729792412589527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6465227653153194941726351 9697841479729792412589527)
  ·
    refine ⟨14546762219594688618884291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9697841479729792412589527 14546762219594688618884291)
    ·
      refine ⟨21820143329392032928326437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14546762219594688618884291 21820143329392032928326437)
      ·
        refine ⟨4091276874261006174061207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21820143329392032928326437 4091276874261006174061207)
        ·
          refine ⟨6136915311391509261091811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091276874261006174061207 6136915311391509261091811)
          ·
            refine ⟨9205372967087263891637717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6136915311391509261091811 9205372967087263891637717)
            ·
              refine ⟨215750928916107747460259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9205372967087263891637717 215750928916107747460259)
              ·
                refine ⟨323626393374161621190389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215750928916107747460259 323626393374161621190389)
                ·
                  refine ⟨30339974378827651986599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323626393374161621190389 30339974378827651986599)
                  ·
                    rfl

theorem cell22_265891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 5].length) (baseStart_265891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265891 prefixEnd_265891 := by exact prefixLift 265891
  have htrace : WordTrace (prefixWord ++ tailWord_265891) baseStart_265891 baseEnd_265891 := by
    simpa [prefixWord, tailWord_265891, baseEnd_265891] using wordTrace_append hprefix tailTrace_265891
  have hstable : (prefixWord ++ tailWord_265891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265891).length < 2 ^ (prefixWord ++ tailWord_265891).sum := by decide
  have hdescent : baseEnd_265891 < baseStart_265891 := by decide
  rcases family_descends (prefixWord ++ tailWord_265891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265904 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_265904 : Nat := 118140960795 + 265904 * 2 ^ 59
def prefixEnd_265904 : Nat := 4983230072969 + 3 ^ 40 * 265904 * 2
def baseEnd_265904 : Nat := 91024373302155255384757

theorem tailTrace_265904 : CollatzResearch.WordTrace tailWord_265904 prefixEnd_265904 91024373302155255384757 := by
  unfold tailWord_265904
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849157814341347816406383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6465543752455130421875177 4849157814341347816406383)
  ·
    refine ⟨7273736721512021724609575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4849157814341347816406383 7273736721512021724609575)
    ·
      refine ⟨10910605082268032586914363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7273736721512021724609575 10910605082268032586914363)
      ·
        refine ⟨16365907623402048880371545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10910605082268032586914363 16365907623402048880371545)
        ·
          refine ⟨12274430717551536660278659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16365907623402048880371545 12274430717551536660278659)
          ·
            refine ⟨18411646076327304990417989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12274430717551536660278659 18411646076327304990417989)
            ·
              refine ⟨3452183639311369685703373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18411646076327304990417989 3452183639311369685703373)
              ·
                refine ⟨1294568864741763632138765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3452183639311369685703373 1294568864741763632138765)
                ·
                  refine ⟨485463324278161362052037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1294568864741763632138765 485463324278161362052037)
                  ·
                    refine ⟨91024373302155255384757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 485463324278161362052037 91024373302155255384757)
                    ·
                      rfl

theorem cell22_265904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_265904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265904 prefixEnd_265904 := by exact prefixLift 265904
  have htrace : WordTrace (prefixWord ++ tailWord_265904) baseStart_265904 baseEnd_265904 := by
    simpa [prefixWord, tailWord_265904, baseEnd_265904] using wordTrace_append hprefix tailTrace_265904
  have hstable : (prefixWord ++ tailWord_265904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265904).length < 2 ^ (prefixWord ++ tailWord_265904).sum := by decide
  have hdescent : baseEnd_265904 < baseStart_265904 := by decide
  rcases family_descends (prefixWord ++ tailWord_265904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265955 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 1, 4]
def baseStart_265955 : Nat := 118140960795 + 265955 * 2 ^ 59
def prefixEnd_265955 : Nat := 4983230072969 + 3 ^ 40 * 265955 * 2
def baseEnd_265955 : Nat := 91041831644408122359601

theorem tailTrace_265955 : CollatzResearch.WordTrace tailWord_265955 prefixEnd_265955 91041831644408122359601 := by
  unfold tailWord_265955
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700175751497931342919319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6466783834331954228612879 9700175751497931342919319)
  ·
    refine ⟨14550263627246897014378979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9700175751497931342919319 14550263627246897014378979)
    ·
      refine ⟨21825395440870345521568469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14550263627246897014378979 21825395440870345521568469)
      ·
        refine ⟨511532705645398723161761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21825395440870345521568469 511532705645398723161761)
        ·
          refine ⟨383649529234049042371321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511532705645398723161761 383649529234049042371321)
          ·
            refine ⟨287737146925536781778491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383649529234049042371321 287737146925536781778491)
            ·
              refine ⟨431605720388305172667737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287737146925536781778491 431605720388305172667737)
              ·
                refine ⟨323704290291228879500803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431605720388305172667737 323704290291228879500803)
                ·
                  refine ⟨485556435436843319251205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323704290291228879500803 485556435436843319251205)
                  ·
                    refine ⟨91041831644408122359601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 485556435436843319251205 91041831644408122359601)
                    ·
                      rfl

theorem cell22_265955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 4].length) (baseStart_265955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265955 prefixEnd_265955 := by exact prefixLift 265955
  have htrace : WordTrace (prefixWord ++ tailWord_265955) baseStart_265955 baseEnd_265955 := by
    simpa [prefixWord, tailWord_265955, baseEnd_265955] using wordTrace_append hprefix tailTrace_265955
  have hstable : (prefixWord ++ tailWord_265955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265955).length < 2 ^ (prefixWord ++ tailWord_265955).sum := by decide
  have hdescent : baseEnd_265955 < baseStart_265955 := by decide
  rcases family_descends (prefixWord ++ tailWord_265955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265964 : List Nat := [2, 2, 1, 1, 2, 2, 4, 8]
def baseStart_265964 : Nat := 118140960795 + 265964 * 2 ^ 59
def prefixEnd_265964 : Nat := 4983230072969 + 3 ^ 40 * 265964 * 2
def baseEnd_265964 : Nat := 10116101392037233209397

theorem tailTrace_265964 : CollatzResearch.WordTrace tailWord_265964 prefixEnd_265964 10116101392037233209397 := by
  unfold tailWord_265964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4850252004232662939998473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6467002672310217253331297 4850252004232662939998473)
  ·
    refine ⟨3637689003174497204998855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4850252004232662939998473 3637689003174497204998855)
    ·
      refine ⟨5456533504761745807498283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3637689003174497204998855 5456533504761745807498283)
      ·
        refine ⟨8184800257142618711247425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456533504761745807498283 8184800257142618711247425)
        ·
          refine ⟨6138600192856964033435569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8184800257142618711247425 6138600192856964033435569)
          ·
            refine ⟨4603950144642723025076677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6138600192856964033435569 4603950144642723025076677)
            ·
              refine ⟨863240652120510567201877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4603950144642723025076677 863240652120510567201877)
              ·
                refine ⟨10116101392037233209397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 863240652120510567201877 10116101392037233209397)
                ·
                  rfl

theorem cell22_265964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 8].length) (baseStart_265964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_265964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_265964 prefixEnd_265964 := by exact prefixLift 265964
  have htrace : WordTrace (prefixWord ++ tailWord_265964) baseStart_265964 baseEnd_265964 := by
    simpa [prefixWord, tailWord_265964, baseEnd_265964] using wordTrace_append hprefix tailTrace_265964
  have hstable : (prefixWord ++ tailWord_265964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265964).length < 2 ^ (prefixWord ++ tailWord_265964).sum := by decide
  have hdescent : baseEnd_265964 < baseStart_265964 := by decide
  rcases family_descends (prefixWord ++ tailWord_265964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266060 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 5]
def baseStart_266060 : Nat := 118140960795 + 266060 * 2 ^ 59
def prefixEnd_266060 : Nat := 4983230072969 + 3 ^ 40 * 266060 * 2
def baseEnd_266060 : Nat := 30359258430074282828093

theorem tailTrace_266060 : CollatzResearch.WordTrace tailWord_266060 prefixEnd_266060 30359258430074282828093 := by
  unfold tailWord_266060
  simp only [CollatzResearch.WordTrace]
  refine ⟨4852002708058767137745817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6469336944078356183661089 4852002708058767137745817)
  ·
    refine ⟨3639002031044075353309363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4852002708058767137745817 3639002031044075353309363)
    ·
      refine ⟨5458503046566113029964045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3639002031044075353309363 5458503046566113029964045)
      ·
        refine ⟨2046938642462292386236517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5458503046566113029964045 2046938642462292386236517)
        ·
          refine ⟨383800995461679822419347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2046938642462292386236517 383800995461679822419347)
          ·
            refine ⟨575701493192519733629021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383800995461679822419347 575701493192519733629021)
            ·
              refine ⟨215888059947194900110883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575701493192519733629021 215888059947194900110883)
              ·
                refine ⟨323832089920792350166325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215888059947194900110883 323832089920792350166325)
                ·
                  refine ⟨30359258430074282828093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323832089920792350166325 30359258430074282828093)
                  ·
                    rfl

theorem cell22_266060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_266060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266060 prefixEnd_266060 := by exact prefixLift 266060
  have htrace : WordTrace (prefixWord ++ tailWord_266060) baseStart_266060 baseEnd_266060 := by
    simpa [prefixWord, tailWord_266060, baseEnd_266060] using wordTrace_append hprefix tailTrace_266060
  have hstable : (prefixWord ++ tailWord_266060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266060).length < 2 ^ (prefixWord ++ tailWord_266060).sum := by decide
  have hdescent : baseEnd_266060 < baseStart_266060 := by decide
  rcases family_descends (prefixWord ++ tailWord_266060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266073 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_266073 : Nat := 118140960795 + 266073 * 2 ^ 59
def prefixEnd_266073 : Nat := 4983230072969 + 3 ^ 40 * 266073 * 2
def baseEnd_266073 : Nat := 91082225455895147909239

theorem tailTrace_266073 : CollatzResearch.WordTrace tailWord_266073 prefixEnd_266073 91082225455895147909239 := by
  unfold tailWord_266073
  simp only [CollatzResearch.WordTrace]
  refine ⟨9704479565070437495714873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6469653043380291663809915 9704479565070437495714873)
  ·
    refine ⟨7278359673802828121786155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9704479565070437495714873 7278359673802828121786155)
    ·
      refine ⟨10917539510704242182679233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7278359673802828121786155 10917539510704242182679233)
      ·
        refine ⟨8188154633028181637009425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10917539510704242182679233 8188154633028181637009425)
        ·
          refine ⟨6141115974771136227757069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8188154633028181637009425 6141115974771136227757069)
          ·
            refine ⟨2302918490539176085408901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6141115974771136227757069 2302918490539176085408901)
            ·
              refine ⟨431797216976095516014169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2302918490539176085408901 431797216976095516014169)
              ·
                refine ⟨323847912732071637010627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431797216976095516014169 323847912732071637010627)
                ·
                  refine ⟨485771869098107455515941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323847912732071637010627 485771869098107455515941)
                  ·
                    refine ⟨91082225455895147909239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 485771869098107455515941 91082225455895147909239)
                    ·
                      rfl

theorem cell22_266073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_266073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266073 prefixEnd_266073 := by exact prefixLift 266073
  have htrace : WordTrace (prefixWord ++ tailWord_266073) baseStart_266073 baseEnd_266073 := by
    simpa [prefixWord, tailWord_266073, baseEnd_266073] using wordTrace_append hprefix tailTrace_266073
  have hstable : (prefixWord ++ tailWord_266073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266073).length < 2 ^ (prefixWord ++ tailWord_266073).sum := by decide
  have hdescent : baseEnd_266073 < baseStart_266073 := by decide
  rcases family_descends (prefixWord ++ tailWord_266073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266105 : List Nat := [1, 2, 1, 3, 2, 2, 5, 2, 4]
def baseStart_266105 : Nat := 118140960795 + 266105 * 2 ^ 59
def prefixEnd_266105 : Nat := 4983230072969 + 3 ^ 40 * 266105 * 2
def baseEnd_266105 : Nat := 30364393236619243703047

theorem tailTrace_266105 : CollatzResearch.WordTrace tailWord_266105 prefixEnd_266105 30364393236619243703047 := by
  unfold tailWord_266105
  simp only [CollatzResearch.WordTrace]
  refine ⟨9705646700954506960879769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6470431133969671307253179 9705646700954506960879769)
  ·
    refine ⟨7279235025715880220659827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9705646700954506960879769 7279235025715880220659827)
    ·
      refine ⟨10918852538573820330989741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7279235025715880220659827 10918852538573820330989741)
      ·
        refine ⟨4094569701965182624121153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10918852538573820330989741 4094569701965182624121153)
        ·
          refine ⟨3070927276473886968090865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4094569701965182624121153 3070927276473886968090865)
          ·
            refine ⟨2303195457355415226068149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3070927276473886968090865 2303195457355415226068149)
            ·
              refine ⟨215924574127070177443889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2303195457355415226068149 215924574127070177443889)
              ·
                refine ⟨161943430595302633082917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215924574127070177443889 161943430595302633082917)
                ·
                  refine ⟨30364393236619243703047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161943430595302633082917 30364393236619243703047)
                  ·
                    rfl

theorem cell22_266105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 4].length) (baseStart_266105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266105 prefixEnd_266105 := by exact prefixLift 266105
  have htrace : WordTrace (prefixWord ++ tailWord_266105) baseStart_266105 baseEnd_266105 := by
    simpa [prefixWord, tailWord_266105, baseEnd_266105] using wordTrace_append hprefix tailTrace_266105
  have hstable : (prefixWord ++ tailWord_266105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266105).length < 2 ^ (prefixWord ++ tailWord_266105).sum := by decide
  have hdescent : baseEnd_266105 < baseStart_266105 := by decide
  rcases family_descends (prefixWord ++ tailWord_266105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266116 : List Nat := [2, 3, 2, 1, 1, 1, 3, 9]
def baseStart_266116 : Nat := 118140960795 + 266116 * 2 ^ 59
def prefixEnd_266116 : Nat := 4983230072969 + 3 ^ 40 * 266116 * 2
def baseEnd_266116 : Nat := 10121882803850818787123

theorem tailTrace_266116 : CollatzResearch.WordTrace tailWord_266116 prefixEnd_266116 10121882803850818787123 := by
  unfold tailWord_266116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4853023951957327919765101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6470698602609770559686801 4853023951957327919765101)
  ·
    refine ⟨1819883981983997969911913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4853023951957327919765101 1819883981983997969911913)
    ·
      refine ⟨1364912986487998477433935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1819883981983997969911913 1364912986487998477433935)
      ·
        refine ⟨2047369479731997716150903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364912986487998477433935 2047369479731997716150903)
        ·
          refine ⟨3071054219597996574226355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047369479731997716150903 3071054219597996574226355)
          ·
            refine ⟨4606581329396994861339533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071054219597996574226355 4606581329396994861339533)
            ·
              refine ⟨1727467998523873073002325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4606581329396994861339533 1727467998523873073002325)
              ·
                refine ⟨10121882803850818787123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1727467998523873073002325 10121882803850818787123)
                ·
                  rfl

theorem cell22_266116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 9].length) (baseStart_266116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266116 prefixEnd_266116 := by exact prefixLift 266116
  have htrace : WordTrace (prefixWord ++ tailWord_266116) baseStart_266116 baseEnd_266116 := by
    simpa [prefixWord, tailWord_266116, baseEnd_266116] using wordTrace_append hprefix tailTrace_266116
  have hstable : (prefixWord ++ tailWord_266116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266116).length < 2 ^ (prefixWord ++ tailWord_266116).sum := by decide
  have hdescent : baseEnd_266116 < baseStart_266116 := by decide
  rcases family_descends (prefixWord ++ tailWord_266116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266223 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 6]
def baseStart_266223 : Nat := 118140960795 + 266223 * 2 ^ 59
def prefixEnd_266223 : Nat := 4983230072969 + 3 ^ 40 * 266223 * 2
def baseEnd_266223 : Nat := 30377857840448252219593

theorem tailTrace_266223 : CollatzResearch.WordTrace tailWord_266223 prefixEnd_266223 30377857840448252219593 := by
  unfold tailWord_266223
  simp only [CollatzResearch.WordTrace]
  refine ⟨9709950514527013113675323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6473300343018008742450215 9709950514527013113675323)
  ·
    refine ⟨14564925771790519670512985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9709950514527013113675323 14564925771790519670512985)
    ·
      refine ⟨10923694328842889752884739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14564925771790519670512985 10923694328842889752884739)
      ·
        refine ⟨16385541493264334629327109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10923694328842889752884739 16385541493264334629327109)
        ·
          refine ⟨3072289029987062742998833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16385541493264334629327109 3072289029987062742998833)
          ·
            refine ⟨2304216772490297057249125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3072289029987062742998833 2304216772490297057249125)
            ·
              refine ⟨432040644841930698234211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2304216772490297057249125 432040644841930698234211)
              ·
                refine ⟨648060967262896047351317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432040644841930698234211 648060967262896047351317)
                ·
                  refine ⟨30377857840448252219593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 648060967262896047351317 30377857840448252219593)
                  ·
                    rfl

theorem cell22_266223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 6].length) (baseStart_266223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266223 prefixEnd_266223 := by exact prefixLift 266223
  have htrace : WordTrace (prefixWord ++ tailWord_266223) baseStart_266223 baseEnd_266223 := by
    simpa [prefixWord, tailWord_266223, baseEnd_266223] using wordTrace_append hprefix tailTrace_266223
  have hstable : (prefixWord ++ tailWord_266223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266223).length < 2 ^ (prefixWord ++ tailWord_266223).sum := by decide
  have hdescent : baseEnd_266223 < baseStart_266223 := by decide
  rcases family_descends (prefixWord ++ tailWord_266223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266268 : List Nat := [2, 2, 3, 1, 3, 1, 10]
def baseStart_266268 : Nat := 118140960795 + 266268 * 2 ^ 59
def prefixEnd_266268 : Nat := 4983230072969 + 3 ^ 40 * 266268 * 2
def baseEnd_266268 : Nat := 3375888071888134788283

theorem tailTrace_266268 : CollatzResearch.WordTrace tailWord_266268 prefixEnd_266268 3375888071888134788283 := by
  unfold tailWord_266268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855795899681992899531729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6474394532909323866042305 4855795899681992899531729)
  ·
    refine ⟨3641846924761494674648797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4855795899681992899531729 3641846924761494674648797)
    ·
      refine ⟨1365692596785560502993299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3641846924761494674648797 1365692596785560502993299)
      ·
        refine ⟨2048538895178340754489949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365692596785560502993299 2048538895178340754489949)
        ·
          refine ⟨768202085691877782933731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2048538895178340754489949 768202085691877782933731)
          ·
            refine ⟨1152303128537816674400597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768202085691877782933731 1152303128537816674400597)
            ·
              refine ⟨3375888071888134788283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1152303128537816674400597 3375888071888134788283)
              ·
                rfl

theorem cell22_266268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 10].length) (baseStart_266268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266268 prefixEnd_266268 := by exact prefixLift 266268
  have htrace : WordTrace (prefixWord ++ tailWord_266268) baseStart_266268 baseEnd_266268 := by
    simpa [prefixWord, tailWord_266268, baseEnd_266268] using wordTrace_append hprefix tailTrace_266268
  have hstable : (prefixWord ++ tailWord_266268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266268).length < 2 ^ (prefixWord ++ tailWord_266268).sum := by decide
  have hdescent : baseEnd_266268 < baseStart_266268 := by decide
  rcases family_descends (prefixWord ++ tailWord_266268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266289 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 2, 3]
def baseStart_266289 : Nat := 118140960795 + 266289 * 2 ^ 59
def prefixEnd_266289 : Nat := 4983230072969 + 3 ^ 40 * 266289 * 2
def baseEnd_266289 : Nat := 91156166670142584508577

theorem tailTrace_266289 : CollatzResearch.WordTrace tailWord_266289 prefixEnd_266289 91156166670142584508577 := by
  unfold tailWord_266289
  simp only [CollatzResearch.WordTrace]
  refine ⟨9712357732287906385577921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6474905154858604257051947 9712357732287906385577921)
  ·
    refine ⟨7284268299215929789183441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9712357732287906385577921 7284268299215929789183441)
    ·
      refine ⟨5463201224411947341887581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7284268299215929789183441 5463201224411947341887581)
      ·
        refine ⟨2048700459154480253207843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5463201224411947341887581 2048700459154480253207843)
        ·
          refine ⟨3073050688731720379811765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048700459154480253207843 3073050688731720379811765)
          ·
            refine ⟨288098502068598785607353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3073050688731720379811765 288098502068598785607353)
            ·
              refine ⟨216073876551449089205515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288098502068598785607353 216073876551449089205515)
              ·
                refine ⟨324110814827173633808273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216073876551449089205515 324110814827173633808273)
                ·
                  refine ⟨243083111120380225356205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324110814827173633808273 243083111120380225356205)
                  ·
                    refine ⟨91156166670142584508577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243083111120380225356205 91156166670142584508577)
                    ·
                      rfl

theorem cell22_266289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_266289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266289 prefixEnd_266289 := by exact prefixLift 266289
  have htrace : WordTrace (prefixWord ++ tailWord_266289) baseStart_266289 baseEnd_266289 := by
    simpa [prefixWord, tailWord_266289, baseEnd_266289] using wordTrace_append hprefix tailTrace_266289
  have hstable : (prefixWord ++ tailWord_266289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266289).length < 2 ^ (prefixWord ++ tailWord_266289).sum := by decide
  have hdescent : baseEnd_266289 < baseStart_266289 := by decide
  rcases family_descends (prefixWord ++ tailWord_266289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266300 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_266300 : Nat := 118140960795 + 266300 * 2 ^ 59
def prefixEnd_266300 : Nat := 4983230072969 + 3 ^ 40 * 266300 * 2
def baseEnd_266300 : Nat := 91159932194942222483543

theorem tailTrace_266300 : CollatzResearch.WordTrace tailWord_266300 prefixEnd_266300 91159932194942222483543 := by
  unfold tailWord_266300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4856379467624027632114177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6475172623498703509485569 4856379467624027632114177)
  ·
    refine ⟨3642284600718020724085633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4856379467624027632114177 3642284600718020724085633)
    ·
      refine ⟨2731713450538515543064225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3642284600718020724085633 2731713450538515543064225)
      ·
        refine ⟨2048785087903886657298169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2731713450538515543064225 2048785087903886657298169)
        ·
          refine ⟨1536588815927914992973627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2048785087903886657298169 1536588815927914992973627)
          ·
            refine ⟨2304883223891872489460441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536588815927914992973627 2304883223891872489460441)
            ·
              refine ⟨1728662417918904367095331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2304883223891872489460441 1728662417918904367095331)
              ·
                refine ⟨2592993626878356550642997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728662417918904367095331 2592993626878356550642997)
                ·
                  refine ⟨243093152519845926622781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2592993626878356550642997 243093152519845926622781)
                  ·
                    refine ⟨91159932194942222483543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243093152519845926622781 91159932194942222483543)
                    ·
                      rfl

theorem cell22_266300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_266300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266300 prefixEnd_266300 := by exact prefixLift 266300
  have htrace : WordTrace (prefixWord ++ tailWord_266300) baseStart_266300 baseEnd_266300 := by
    simpa [prefixWord, tailWord_266300, baseEnd_266300] using wordTrace_append hprefix tailTrace_266300
  have hstable : (prefixWord ++ tailWord_266300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266300).length < 2 ^ (prefixWord ++ tailWord_266300).sum := by decide
  have hdescent : baseEnd_266300 < baseStart_266300 := by decide
  rcases family_descends (prefixWord ++ tailWord_266300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266330 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_266330 : Nat := 118140960795 + 266330 * 2 ^ 59
def prefixEnd_266330 : Nat := 4983230072969 + 3 ^ 40 * 266330 * 2
def baseEnd_266330 : Nat := 30390067269344048077817

theorem tailTrace_266330 : CollatzResearch.WordTrace tailWord_266330 prefixEnd_266330 30390067269344048077817 := by
  unfold tailWord_266330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428463281284842596955111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6475902083426246925213629 2428463281284842596955111)
  ·
    refine ⟨3642694921927263895432667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2428463281284842596955111 3642694921927263895432667)
    ·
      refine ⟨5464042382890895843149001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3642694921927263895432667 5464042382890895843149001)
      ·
        refine ⟨4098031787168171882361751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5464042382890895843149001 4098031787168171882361751)
        ·
          refine ⟨6147047680752257823542627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4098031787168171882361751 6147047680752257823542627)
          ·
            refine ⟨9220571521128386735313941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147047680752257823542627 9220571521128386735313941)
            ·
              refine ⟨432214290052893128217841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9220571521128386735313941 432214290052893128217841)
              ·
                refine ⟨324160717539669846163381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432214290052893128217841 324160717539669846163381)
                ·
                  refine ⟨30390067269344048077817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324160717539669846163381 30390067269344048077817)
                  ·
                    rfl

theorem cell22_266330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_266330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266330 prefixEnd_266330 := by exact prefixLift 266330
  have htrace : WordTrace (prefixWord ++ tailWord_266330) baseStart_266330 baseEnd_266330 := by
    simpa [prefixWord, tailWord_266330, baseEnd_266330] using wordTrace_append hprefix tailTrace_266330
  have hstable : (prefixWord ++ tailWord_266330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266330).length < 2 ^ (prefixWord ++ tailWord_266330).sum := by decide
  have hdescent : baseEnd_266330 < baseStart_266330 := by decide
  rcases family_descends (prefixWord ++ tailWord_266330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266360 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_266360 : Nat := 118140960795 + 266360 * 2 ^ 59
def prefixEnd_266360 : Nat := 4983230072969 + 3 ^ 40 * 266360 * 2
def baseEnd_266360 : Nat := 91180471421122065983359

theorem tailTrace_266360 : CollatzResearch.WordTrace tailWord_266360 prefixEnd_266360 91180471421122065983359 := by
  unfold tailWord_266360
  simp only [CollatzResearch.WordTrace]
  refine ⟨4857473657515342755706267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6476631543353790340941689 4857473657515342755706267)
  ·
    refine ⟨7286210486273014133559401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4857473657515342755706267 7286210486273014133559401)
    ·
      refine ⟨5464657864704760600169551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7286210486273014133559401 5464657864704760600169551)
      ·
        refine ⟨8196986797057140900254327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5464657864704760600169551 8196986797057140900254327)
        ·
          refine ⟨12295480195585711350381491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8196986797057140900254327 12295480195585711350381491)
          ·
            refine ⟨18443220293378567025572237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12295480195585711350381491 18443220293378567025572237)
            ·
              refine ⟨6916207610016962634589589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18443220293378567025572237 6916207610016962634589589)
              ·
                refine ⟨324197231719545123496387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6916207610016962634589589 324197231719545123496387)
                ·
                  refine ⟨486295847579317685244581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324197231719545123496387 486295847579317685244581)
                  ·
                    refine ⟨91180471421122065983359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 486295847579317685244581 91180471421122065983359)
                    ·
                      rfl

theorem cell22_266360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_266360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266360 prefixEnd_266360 := by exact prefixLift 266360
  have htrace : WordTrace (prefixWord ++ tailWord_266360) baseStart_266360 baseEnd_266360 := by
    simpa [prefixWord, tailWord_266360, baseEnd_266360] using wordTrace_append hprefix tailTrace_266360
  have hstable : (prefixWord ++ tailWord_266360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266360).length < 2 ^ (prefixWord ++ tailWord_266360).sum := by decide
  have hdescent : baseEnd_266360 < baseStart_266360 := by decide
  rcases family_descends (prefixWord ++ tailWord_266360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266392 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 6]
def baseStart_266392 : Nat := 118140960795 + 266392 * 2 ^ 59
def prefixEnd_266392 : Nat := 4983230072969 + 3 ^ 40 * 266392 * 2
def baseEnd_266392 : Nat := 30397141891694883061087

theorem tailTrace_266392 : CollatzResearch.WordTrace tailWord_266392 prefixEnd_266392 30397141891694883061087 := by
  unfold tailWord_266392
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858057225457377488288715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6477409633943169984384953 4858057225457377488288715)
  ·
    refine ⟨7287085838186066232433073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4858057225457377488288715 7287085838186066232433073)
    ·
      refine ⟨5465314378639549674324805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7287085838186066232433073 5465314378639549674324805)
      ·
        refine ⟨1024746445994915563935901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5465314378639549674324805 1024746445994915563935901)
        ·
          refine ⟨384279917248093336475963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1024746445994915563935901 384279917248093336475963)
          ·
            refine ⟨576419875872140004713945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384279917248093336475963 576419875872140004713945)
            ·
              refine ⟨432314906904105003535459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576419875872140004713945 432314906904105003535459)
              ·
                refine ⟨648472360356157505303189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432314906904105003535459 648472360356157505303189)
                ·
                  refine ⟨30397141891694883061087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 648472360356157505303189 30397141891694883061087)
                  ·
                    rfl

theorem cell22_266392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_266392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266392 prefixEnd_266392 := by exact prefixLift 266392
  have htrace : WordTrace (prefixWord ++ tailWord_266392) baseStart_266392 baseEnd_266392 := by
    simpa [prefixWord, tailWord_266392, baseEnd_266392] using wordTrace_append hprefix tailTrace_266392
  have hstable : (prefixWord ++ tailWord_266392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266392).length < 2 ^ (prefixWord ++ tailWord_266392).sum := by decide
  have hdescent : baseEnd_266392 < baseStart_266392 := by decide
  rcases family_descends (prefixWord ++ tailWord_266392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266454 : List Nat := [5, 2, 1, 2, 1, 2, 2, 7]
def baseStart_266454 : Nat := 118140960795 + 266454 * 2 ^ 59
def prefixEnd_266454 : Nat := 4983230072969 + 3 ^ 40 * 266454 * 2
def baseEnd_266454 : Nat := 10134738838015239348119

theorem tailTrace_266454 : CollatzResearch.WordTrace tailWord_266454 prefixEnd_266454 10134738838015239348119 := by
  unfold tailWord_266454
  simp only [CollatzResearch.WordTrace]
  refine ⟨607398486043133722833401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6478917184460093043556277 607398486043133722833401)
  ·
    refine ⟨455548864532350292125051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 607398486043133722833401 455548864532350292125051)
    ·
      refine ⟨683323296798525438187577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455548864532350292125051 683323296798525438187577)
      ·
        refine ⟨512492472598894078640683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683323296798525438187577 512492472598894078640683)
        ·
          refine ⟨768738708898341117961025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512492472598894078640683 768738708898341117961025)
          ·
            refine ⟨576554031673755838470769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768738708898341117961025 576554031673755838470769)
            ·
              refine ⟨432415523755316878853077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576554031673755838470769 432415523755316878853077)
              ·
                refine ⟨10134738838015239348119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 432415523755316878853077 10134738838015239348119)
                ·
                  rfl

theorem cell22_266454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_266454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266454 prefixEnd_266454 := by exact prefixLift 266454
  have htrace : WordTrace (prefixWord ++ tailWord_266454) baseStart_266454 baseEnd_266454 := by
    simpa [prefixWord, tailWord_266454, baseEnd_266454] using wordTrace_append hprefix tailTrace_266454
  have hstable : (prefixWord ++ tailWord_266454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266454).length < 2 ^ (prefixWord ++ tailWord_266454).sum := by decide
  have hdescent : baseEnd_266454 < baseStart_266454 := by decide
  rcases family_descends (prefixWord ++ tailWord_266454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266503 : List Nat := [1, 1, 4, 5, 1, 1, 1, 4, 1, 3]
def baseStart_266503 : Nat := 118140960795 + 266503 * 2 ^ 59
def prefixEnd_266503 : Nat := 4983230072969 + 3 ^ 40 * 266503 * 2
def baseEnd_266503 : Nat := 91229423243517359657921

theorem tailTrace_266503 : CollatzResearch.WordTrace tailWord_266503 prefixEnd_266503 91229423243517359657921 := by
  unfold tailWord_266503
  simp only [CollatzResearch.WordTrace]
  refine ⟨9720162953512620933868163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6480108635675080622578775 9720162953512620933868163)
  ·
    refine ⟨14580244430268931400802245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9720162953512620933868163 14580244430268931400802245)
    ·
      refine ⟨2733795830675424637650421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14580244430268931400802245 2733795830675424637650421)
      ·
        refine ⟨256293359125821059779727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2733795830675424637650421 256293359125821059779727)
        ·
          refine ⟨384440038688731589669591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256293359125821059779727 384440038688731589669591)
          ·
            refine ⟨576660058033097384504387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384440038688731589669591 576660058033097384504387)
            ·
              refine ⟨864990087049646076756581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576660058033097384504387 864990087049646076756581)
              ·
                refine ⟨162185641321808639391859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 864990087049646076756581 162185641321808639391859)
                ·
                  refine ⟨243278461982712959087789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162185641321808639391859 243278461982712959087789)
                  ·
                    refine ⟨91229423243517359657921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243278461982712959087789 91229423243517359657921)
                    ·
                      rfl

theorem cell22_266503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_266503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266503 prefixEnd_266503 := by exact prefixLift 266503
  have htrace : WordTrace (prefixWord ++ tailWord_266503) baseStart_266503 baseEnd_266503 := by
    simpa [prefixWord, tailWord_266503, baseEnd_266503] using wordTrace_append hprefix tailTrace_266503
  have hstable : (prefixWord ++ tailWord_266503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266503).length < 2 ^ (prefixWord ++ tailWord_266503).sum := by decide
  have hdescent : baseEnd_266503 < baseStart_266503 := by decide
  rcases family_descends (prefixWord ++ tailWord_266503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266527 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 6]
def baseStart_266527 : Nat := 118140960795 + 266527 * 2 ^ 59
def prefixEnd_266527 : Nat := 4983230072969 + 3 ^ 40 * 266527 * 2
def baseEnd_266527 : Nat := 30412546311329765685949

theorem tailTrace_266527 : CollatzResearch.WordTrace tailWord_266527 prefixEnd_266527 30412546311329765685949 := by
  unfold tailWord_266527
  simp only [CollatzResearch.WordTrace]
  refine ⟨9721038305425673032741835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6480692203617115355161223 9721038305425673032741835)
  ·
    refine ⟨14581557458138509549112753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9721038305425673032741835 14581557458138509549112753)
    ·
      refine ⟨10936168093603882161834565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14581557458138509549112753 10936168093603882161834565)
      ·
        refine ⟨2050531517550727905343981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10936168093603882161834565 2050531517550727905343981)
        ·
          refine ⟨768949319081522964503993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2050531517550727905343981 768949319081522964503993)
          ·
            refine ⟨576711989311142223377995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768949319081522964503993 576711989311142223377995)
            ·
              refine ⟨865067983966713335066993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576711989311142223377995 865067983966713335066993)
              ·
                refine ⟨648800987975035001300245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865067983966713335066993 648800987975035001300245)
                ·
                  refine ⟨30412546311329765685949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 648800987975035001300245 30412546311329765685949)
                  ·
                    rfl

theorem cell22_266527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 6].length) (baseStart_266527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266527 prefixEnd_266527 := by exact prefixLift 266527
  have htrace : WordTrace (prefixWord ++ tailWord_266527) baseStart_266527 baseEnd_266527 := by
    simpa [prefixWord, tailWord_266527, baseEnd_266527] using wordTrace_append hprefix tailTrace_266527
  have hstable : (prefixWord ++ tailWord_266527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266527).length < 2 ^ (prefixWord ++ tailWord_266527).sum := by decide
  have hdescent : baseEnd_266527 < baseStart_266527 := by decide
  rcases family_descends (prefixWord ++ tailWord_266527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266576 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 2, 3]
def baseStart_266576 : Nat := 118140960795 + 266576 * 2 ^ 59
def prefixEnd_266576 : Nat := 4983230072969 + 3 ^ 40 * 266576 * 2
def baseEnd_266576 : Nat := 91254412635369502582697

theorem tailTrace_266576 : CollatzResearch.WordTrace tailWord_266576 prefixEnd_266576 91254412635369502582697 := by
  unfold tailWord_266576
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861412741124077200637791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6481883654832102934183721 4861412741124077200637791)
  ·
    refine ⟨7292119111686115800956687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4861412741124077200637791 7292119111686115800956687)
    ·
      refine ⟨10938178667529173701435031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7292119111686115800956687 10938178667529173701435031)
      ·
        refine ⟨16407268001293760552152547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10938178667529173701435031 16407268001293760552152547)
        ·
          refine ⟨24610902001940640828228821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16407268001293760552152547 24610902001940640828228821)
          ·
            refine ⟨576818015670483769411613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 24610902001940640828228821 576818015670483769411613)
            ·
              refine ⟨216306755876431413529355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576818015670483769411613 216306755876431413529355)
              ·
                refine ⟨324460133814647120294033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216306755876431413529355 324460133814647120294033)
                ·
                  refine ⟨243345100360985340220525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324460133814647120294033 243345100360985340220525)
                  ·
                    refine ⟨91254412635369502582697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243345100360985340220525 91254412635369502582697)
                    ·
                      rfl

theorem cell22_266576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 3].length) (baseStart_266576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266576 prefixEnd_266576 := by exact prefixLift 266576
  have htrace : WordTrace (prefixWord ++ tailWord_266576) baseStart_266576 baseEnd_266576 := by
    simpa [prefixWord, tailWord_266576, baseEnd_266576] using wordTrace_append hprefix tailTrace_266576
  have hstable : (prefixWord ++ tailWord_266576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266576).length < 2 ^ (prefixWord ++ tailWord_266576).sum := by decide
  have hdescent : baseEnd_266576 < baseStart_266576 := by decide
  rcases family_descends (prefixWord ++ tailWord_266576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266617 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 5]
def baseStart_266617 : Nat := 118140960795 + 266617 * 2 ^ 59
def prefixEnd_266617 : Nat := 4983230072969 + 3 ^ 40 * 266617 * 2
def baseEnd_266617 : Nat := 30422815924419687435857

theorem tailTrace_266617 : CollatzResearch.WordTrace tailWord_266617 prefixEnd_266617 30422815924419687435857 := by
  unfold tailWord_266617
  simp only [CollatzResearch.WordTrace]
  refine ⟨9724320875099618403518105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6482880583399745602345403 9724320875099618403518105)
  ·
    refine ⟨7293240656324713802638579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9724320875099618403518105 7293240656324713802638579)
    ·
      refine ⟨10939860984487070703957869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7293240656324713802638579 10939860984487070703957869)
      ·
        refine ⟨4102447869182651513984201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10939860984487070703957869 4102447869182651513984201)
        ·
          refine ⟨3076835901886988635488151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4102447869182651513984201 3076835901886988635488151)
          ·
            refine ⟨4615253852830482953232227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076835901886988635488151 4615253852830482953232227)
            ·
              refine ⟨6922880779245724429848341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615253852830482953232227 6922880779245724429848341)
              ·
                refine ⟨324510036527143332649141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6922880779245724429848341 324510036527143332649141)
                ·
                  refine ⟨30422815924419687435857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324510036527143332649141 30422815924419687435857)
                  ·
                    rfl

theorem cell22_266617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_266617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266617 prefixEnd_266617 := by exact prefixLift 266617
  have htrace : WordTrace (prefixWord ++ tailWord_266617) baseStart_266617 baseEnd_266617 := by
    simpa [prefixWord, tailWord_266617, baseEnd_266617] using wordTrace_append hprefix tailTrace_266617
  have hstable : (prefixWord ++ tailWord_266617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266617).length < 2 ^ (prefixWord ++ tailWord_266617).sum := by decide
  have hdescent : baseEnd_266617 < baseStart_266617 := by decide
  rcases family_descends (prefixWord ++ tailWord_266617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266621 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_266621 : Nat := 118140960795 + 266621 * 2 ^ 59
def prefixEnd_266621 : Nat := 4983230072969 + 3 ^ 40 * 266621 * 2
def baseEnd_266621 : Nat := 91269817055004385207559

theorem tailTrace_266621 : CollatzResearch.WordTrace tailWord_266621 prefixEnd_266621 91269817055004385207559 := by
  unfold tailWord_266621
  simp only [CollatzResearch.WordTrace]
  refine ⟨9724466767085127086663717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6482977844723418057775811 9724466767085127086663717)
  ·
    refine ⟨1823337518828461328749447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9724466767085127086663717 1823337518828461328749447)
    ·
      refine ⟨2735006278242691993124171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1823337518828461328749447 2735006278242691993124171)
      ·
        refine ⟨4102509417364037989686257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735006278242691993124171 4102509417364037989686257)
        ·
          refine ⟨3076882063023028492264693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4102509417364037989686257 3076882063023028492264693)
          ·
            refine ⟨288457693408408921149815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3076882063023028492264693 288457693408408921149815)
            ·
              refine ⟨432686540112613381724723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288457693408408921149815 432686540112613381724723)
              ·
                refine ⟨649029810168920072587085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432686540112613381724723 649029810168920072587085)
                ·
                  refine ⟨243386178813345027220157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649029810168920072587085 243386178813345027220157)
                  ·
                    refine ⟨91269817055004385207559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243386178813345027220157 91269817055004385207559)
                    ·
                      rfl

theorem cell22_266621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_266621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266621 prefixEnd_266621 := by exact prefixLift 266621
  have htrace : WordTrace (prefixWord ++ tailWord_266621) baseStart_266621 baseEnd_266621 := by
    simpa [prefixWord, tailWord_266621, baseEnd_266621] using wordTrace_append hprefix tailTrace_266621
  have hstable : (prefixWord ++ tailWord_266621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266621).length < 2 ^ (prefixWord ++ tailWord_266621).sum := by decide
  have hdescent : baseEnd_266621 < baseStart_266621 := by decide
  rcases family_descends (prefixWord ++ tailWord_266621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266632 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_266632 : Nat := 118140960795 + 266632 * 2 ^ 59
def prefixEnd_266632 : Nat := 4983230072969 + 3 ^ 40 * 266632 * 2
def baseEnd_266632 : Nat := 91273582579804023182525

theorem tailTrace_266632 : CollatzResearch.WordTrace tailWord_266632 prefixEnd_266632 91273582579804023182525 := by
  unfold tailWord_266632
  simp only [CollatzResearch.WordTrace]
  refine ⟨4862433985022637982657075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6483245313363517310209433 4862433985022637982657075)
  ·
    refine ⟨7293650977533956973985613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4862433985022637982657075 7293650977533956973985613)
    ·
      refine ⟨2735119116575233865244605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7293650977533956973985613 2735119116575233865244605)
      ·
        refine ⟨1025669668715712699466727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2735119116575233865244605 1025669668715712699466727)
        ·
          refine ⟨1538504503073569049200091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025669668715712699466727 1538504503073569049200091)
          ·
            refine ⟨2307756754610353573800137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538504503073569049200091 2307756754610353573800137)
            ·
              refine ⟨1730817565957765180350103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307756754610353573800137 1730817565957765180350103)
              ·
                refine ⟨2596226348936647770525155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730817565957765180350103 2596226348936647770525155)
                ·
                  refine ⟨3894339523404971655787733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596226348936647770525155 3894339523404971655787733)
                  ·
                    refine ⟨91273582579804023182525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3894339523404971655787733 91273582579804023182525)
                    ·
                      rfl

theorem cell22_266632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_266632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266632 prefixEnd_266632 := by exact prefixLift 266632
  have htrace : WordTrace (prefixWord ++ tailWord_266632) baseStart_266632 baseEnd_266632 := by
    simpa [prefixWord, tailWord_266632, baseEnd_266632] using wordTrace_append hprefix tailTrace_266632
  have hstable : (prefixWord ++ tailWord_266632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266632).length < 2 ^ (prefixWord ++ tailWord_266632).sum := by decide
  have hdescent : baseEnd_266632 < baseStart_266632 := by decide
  rcases family_descends (prefixWord ++ tailWord_266632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266709 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_266709 : Nat := 118140960795 + 266709 * 2 ^ 59
def prefixEnd_266709 : Nat := 4983230072969 + 3 ^ 40 * 266709 * 2
def baseEnd_266709 : Nat := 91299941253401489007289

theorem tailTrace_266709 : CollatzResearch.WordTrace tailWord_266709 prefixEnd_266709 91299941253401489007289 := by
  unfold tailWord_266709
  simp only [CollatzResearch.WordTrace]
  refine ⟨9727676390766318115867181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6485117593844212077244787 9727676390766318115867181)
  ·
    refine ⟨3647878646537369293450193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9727676390766318115867181 3647878646537369293450193)
    ·
      refine ⟨2735908984903026970087645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3647878646537369293450193 2735908984903026970087645)
      ·
        refine ⟨1025965869338635113782867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2735908984903026970087645 1025965869338635113782867)
        ·
          refine ⟨1538948804007952670674301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025965869338635113782867 1538948804007952670674301)
          ·
            refine ⟨577105801502982251502863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1538948804007952670674301 577105801502982251502863)
            ·
              refine ⟨865658702254473377254295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577105801502982251502863 865658702254473377254295)
              ·
                refine ⟨1298488053381710065881443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865658702254473377254295 1298488053381710065881443)
                ·
                  refine ⟨1947732080072565098822165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298488053381710065881443 1947732080072565098822165)
                  ·
                    refine ⟨91299941253401489007289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1947732080072565098822165 91299941253401489007289)
                    ·
                      rfl

theorem cell22_266709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_266709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266709 prefixEnd_266709 := by exact prefixLift 266709
  have htrace : WordTrace (prefixWord ++ tailWord_266709) baseStart_266709 baseEnd_266709 := by
    simpa [prefixWord, tailWord_266709, baseEnd_266709] using wordTrace_append hprefix tailTrace_266709
  have hstable : (prefixWord ++ tailWord_266709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266709).length < 2 ^ (prefixWord ++ tailWord_266709).sum := by decide
  have hdescent : baseEnd_266709 < baseStart_266709 := by decide
  rcases family_descends (prefixWord ++ tailWord_266709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266728 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 2, 3]
def baseStart_266728 : Nat := 118140960795 + 266728 * 2 ^ 59
def prefixEnd_266728 : Nat := 4983230072969 + 3 ^ 40 * 266728 * 2
def baseEnd_266728 : Nat := 91306445341691772782231

theorem tailTrace_266728 : CollatzResearch.WordTrace tailWord_266728 prefixEnd_266728 91306445341691772782231 := by
  unfold tailWord_266728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864184688848742180404419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6485579585131656240539225 4864184688848742180404419)
  ·
    refine ⟨7296277033273113270606629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4864184688848742180404419 7296277033273113270606629)
    ·
      refine ⟨1368051943738708738238743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7296277033273113270606629 1368051943738708738238743)
      ·
        refine ⟨2052077915608063107358115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368051943738708738238743 2052077915608063107358115)
        ·
          refine ⟨3078116873412094661037173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052077915608063107358115 3078116873412094661037173)
          ·
            refine ⟨288573456882383874472235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3078116873412094661037173 288573456882383874472235)
            ·
              refine ⟨432860185323575811708353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288573456882383874472235 432860185323575811708353)
              ·
                refine ⟨324645138992681858781265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432860185323575811708353 324645138992681858781265)
                ·
                  refine ⟨243483854244511394085949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324645138992681858781265 243483854244511394085949)
                  ·
                    refine ⟨91306445341691772782231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243483854244511394085949 91306445341691772782231)
                    ·
                      rfl

theorem cell22_266728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_266728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266728 prefixEnd_266728 := by exact prefixLift 266728
  have htrace : WordTrace (prefixWord ++ tailWord_266728) baseStart_266728 baseEnd_266728 := by
    simpa [prefixWord, tailWord_266728, baseEnd_266728] using wordTrace_append hprefix tailTrace_266728
  have hstable : (prefixWord ++ tailWord_266728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266728).length < 2 ^ (prefixWord ++ tailWord_266728).sum := by decide
  have hdescent : baseEnd_266728 < baseStart_266728 := by decide
  rcases family_descends (prefixWord ++ tailWord_266728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266767 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 3, 7]
def baseStart_266767 : Nat := 118140960795 + 266767 * 2 ^ 59
def prefixEnd_266767 : Nat := 4983230072969 + 3 ^ 40 * 266767 * 2
def baseEnd_266767 : Nat := 91319795838708671057111

theorem tailTrace_266767 : CollatzResearch.WordTrace tailWord_266767 prefixEnd_266767 91319795838708671057111 := by
  unfold tailWord_266767
  simp only [CollatzResearch.WordTrace]
  refine ⟨9729791824556194021478555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6486527883037462680985703 9729791824556194021478555)
  ·
    refine ⟨14594687736834291032217833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9729791824556194021478555 14594687736834291032217833)
    ·
      refine ⟨10946015802625718274163375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14594687736834291032217833 10946015802625718274163375)
      ·
        refine ⟨16419023703938577411245063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10946015802625718274163375 16419023703938577411245063)
        ·
          refine ⟨24628535555907866116867595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16419023703938577411245063 24628535555907866116867595)
          ·
            refine ⟨36942803333861799175301393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24628535555907866116867595 36942803333861799175301393)
            ·
              refine ⟨27707102500396349381476045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36942803333861799175301393 27707102500396349381476045)
              ·
                refine ⟨10390163437648631018053517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27707102500396349381476045 10390163437648631018053517)
                ·
                  refine ⟨3896311289118236631770069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10390163437648631018053517 3896311289118236631770069)
                  ·
                    refine ⟨91319795838708671057111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3896311289118236631770069 91319795838708671057111)
                    ·
                      rfl

theorem cell22_266767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_266767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266767 prefixEnd_266767 := by exact prefixLift 266767
  have htrace : WordTrace (prefixWord ++ tailWord_266767) baseStart_266767 baseEnd_266767 := by
    simpa [prefixWord, tailWord_266767, baseEnd_266767] using wordTrace_append hprefix tailTrace_266767
  have hstable : (prefixWord ++ tailWord_266767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266767).length < 2 ^ (prefixWord ++ tailWord_266767).sum := by decide
  have hdescent : baseEnd_266767 < baseStart_266767 := by decide
  rcases family_descends (prefixWord ++ tailWord_266767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266816 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_266816 : Nat := 118140960795 + 266816 * 2 ^ 59
def prefixEnd_266816 : Nat := 4983230072969 + 3 ^ 40 * 266816 * 2
def baseEnd_266816 : Nat := 91336569540088876581961

theorem tailTrace_266816 : CollatzResearch.WordTrace tailWord_266816 prefixEnd_266816 91336569540088876581961 := by
  unfold tailWord_266816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865789500689337695006151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6487719334252450260008201 4865789500689337695006151)
  ·
    refine ⟨7298684251034006542509227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4865789500689337695006151 7298684251034006542509227)
    ·
      refine ⟨10948026376551009813763841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7298684251034006542509227 10948026376551009813763841)
      ·
        refine ⟨8211019782413257360322881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10948026376551009813763841 8211019782413257360322881)
        ·
          refine ⟨6158264836809943020242161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8211019782413257360322881 6158264836809943020242161)
          ·
            refine ⟨4618698627607457265181621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6158264836809943020242161 4618698627607457265181621)
            ·
              refine ⟨433002996338199118610777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4618698627607457265181621 433002996338199118610777)
              ·
                refine ⟨324752247253649338958083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433002996338199118610777 324752247253649338958083)
                ·
                  refine ⟨487128370880474008437125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324752247253649338958083 487128370880474008437125)
                  ·
                    refine ⟨91336569540088876581961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487128370880474008437125 91336569540088876581961)
                    ·
                      rfl

theorem cell22_266816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_266816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266816 prefixEnd_266816 := by exact prefixLift 266816
  have htrace : WordTrace (prefixWord ++ tailWord_266816) baseStart_266816 baseEnd_266816 := by
    simpa [prefixWord, tailWord_266816, baseEnd_266816] using wordTrace_append hprefix tailTrace_266816
  have hstable : (prefixWord ++ tailWord_266816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266816).length < 2 ^ (prefixWord ++ tailWord_266816).sum := by decide
  have hdescent : baseEnd_266816 < baseStart_266816 := by decide
  rcases family_descends (prefixWord ++ tailWord_266816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266833 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 1, 4]
def baseStart_266833 : Nat := 118140960795 + 266833 * 2 ^ 59
def prefixEnd_266833 : Nat := 4983230072969 + 3 ^ 40 * 266833 * 2
def baseEnd_266833 : Nat := 91342388987506498906909

theorem tailTrace_266833 : CollatzResearch.WordTrace tailWord_266833 prefixEnd_266833 91342388987506498906909 := by
  unfold tailWord_266833
  simp only [CollatzResearch.WordTrace]
  refine ⟨9732199042317087293381153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6488132694878058195587435 9732199042317087293381153)
  ·
    refine ⟨7299149281737815470035865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9732199042317087293381153 7299149281737815470035865)
    ·
      refine ⟨5474361961303361602526899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7299149281737815470035865 5474361961303361602526899)
      ·
        refine ⟨8211542941955042403790349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5474361961303361602526899 8211542941955042403790349)
        ·
          refine ⟨3079328603233140901421381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8211542941955042403790349 3079328603233140901421381)
          ·
            refine ⟨577374113106213919016509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3079328603233140901421381 577374113106213919016509)
            ·
              refine ⟨216515292414830219631191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577374113106213919016509 216515292414830219631191)
              ·
                refine ⟨324772938622245329446787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216515292414830219631191 324772938622245329446787)
                ·
                  refine ⟨487159407933367994170181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324772938622245329446787 487159407933367994170181)
                  ·
                    refine ⟨91342388987506498906909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487159407933367994170181 91342388987506498906909)
                    ·
                      rfl

theorem cell22_266833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_266833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266833 prefixEnd_266833 := by exact prefixLift 266833
  have htrace : WordTrace (prefixWord ++ tailWord_266833) baseStart_266833 baseEnd_266833 := by
    simpa [prefixWord, tailWord_266833, baseEnd_266833] using wordTrace_append hprefix tailTrace_266833
  have hstable : (prefixWord ++ tailWord_266833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266833).length < 2 ^ (prefixWord ++ tailWord_266833).sum := by decide
  have hdescent : baseEnd_266833 < baseStart_266833 := by decide
  rcases family_descends (prefixWord ++ tailWord_266833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266848 : List Nat := [2, 1, 1, 3, 2, 1, 6, 2, 4]
def baseStart_266848 : Nat := 118140960795 + 266848 * 2 ^ 59
def prefixEnd_266848 : Nat := 4983230072969 + 3 ^ 40 * 266848 * 2
def baseEnd_266848 : Nat := 30449174598017153260621

theorem tailTrace_266848 : CollatzResearch.WordTrace tailWord_266848 prefixEnd_266848 30449174598017153260621 := by
  unfold tailWord_266848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4866373068631372427588599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6488497424841829903451465 4866373068631372427588599)
  ·
    refine ⟨7299559602947058641382899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4866373068631372427588599 7299559602947058641382899)
    ·
      refine ⟨10949339404420587962074349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7299559602947058641382899 10949339404420587962074349)
      ·
        refine ⟨4106002276657720485777881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10949339404420587962074349 4106002276657720485777881)
        ·
          refine ⟨3079501707493290364333411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4106002276657720485777881 3079501707493290364333411)
          ·
            refine ⟨4619252561239935546500117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079501707493290364333411 4619252561239935546500117)
            ·
              refine ⟨216527463808121978742193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4619252561239935546500117 216527463808121978742193)
              ·
                refine ⟨162395597856091484056645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216527463808121978742193 162395597856091484056645)
                ·
                  refine ⟨30449174598017153260621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162395597856091484056645 30449174598017153260621)
                  ·
                    rfl

theorem cell22_266848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 4].length) (baseStart_266848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266848 prefixEnd_266848 := by exact prefixLift 266848
  have htrace : WordTrace (prefixWord ++ tailWord_266848) baseStart_266848 baseEnd_266848 := by
    simpa [prefixWord, tailWord_266848, baseEnd_266848] using wordTrace_append hprefix tailTrace_266848
  have hstable : (prefixWord ++ tailWord_266848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266848).length < 2 ^ (prefixWord ++ tailWord_266848).sum := by decide
  have hdescent : baseEnd_266848 < baseStart_266848 := by decide
  rcases family_descends (prefixWord ++ tailWord_266848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266908 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_266908 : Nat := 118140960795 + 266908 * 2 ^ 59
def prefixEnd_266908 : Nat := 4983230072969 + 3 ^ 40 * 266908 * 2
def baseEnd_266908 : Nat := 91368063020231303281679

theorem tailTrace_266908 : CollatzResearch.WordTrace tailWord_266908 prefixEnd_266908 91368063020231303281679 := by
  unfold tailWord_266908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867467258522687551180689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6489956344696916734907585 4867467258522687551180689)
  ·
    refine ⟨3650600443892015663385517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4867467258522687551180689 3650600443892015663385517)
    ·
      refine ⟨1368975166459505873769569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3650600443892015663385517 1368975166459505873769569)
      ·
        refine ⟨1026731374844629405327177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1368975166459505873769569 1026731374844629405327177)
        ·
          refine ⟨770048531133472053995383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1026731374844629405327177 770048531133472053995383)
          ·
            refine ⟨1155072796700208080993075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770048531133472053995383 1155072796700208080993075)
            ·
              refine ⟨1732609195050312121489613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155072796700208080993075 1732609195050312121489613)
              ·
                refine ⟨649728448143867045558605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732609195050312121489613 649728448143867045558605)
                ·
                  refine ⟨243648168053950142084477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649728448143867045558605 243648168053950142084477)
                  ·
                    refine ⟨91368063020231303281679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243648168053950142084477 91368063020231303281679)
                    ·
                      rfl

theorem cell22_266908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_266908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266908 prefixEnd_266908 := by exact prefixLift 266908
  have htrace : WordTrace (prefixWord ++ tailWord_266908) baseStart_266908 baseEnd_266908 := by
    simpa [prefixWord, tailWord_266908, baseEnd_266908] using wordTrace_append hprefix tailTrace_266908
  have hstable : (prefixWord ++ tailWord_266908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266908).length < 2 ^ (prefixWord ++ tailWord_266908).sum := by decide
  have hdescent : baseEnd_266908 < baseStart_266908 := by decide
  rcases family_descends (prefixWord ++ tailWord_266908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266972 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 5]
def baseStart_266972 : Nat := 118140960795 + 266972 * 2 ^ 59
def prefixEnd_266972 : Nat := 4983230072969 + 3 ^ 40 * 266972 * 2
def baseEnd_266972 : Nat := 30463323842718823227161

theorem tailTrace_266972 : CollatzResearch.WordTrace tailWord_266972 prefixEnd_266972 30463323842718823227161 := by
  unfold tailWord_266972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4868634394406757016345585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6491512525875676021794113 4868634394406757016345585)
  ·
    refine ⟨3651475795805067762259189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4868634394406757016345585 3651475795805067762259189)
    ·
      refine ⟨342325855856725102711799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3651475795805067762259189 342325855856725102711799)
      ·
        refine ⟨513488783785087654067699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342325855856725102711799 513488783785087654067699)
        ·
          refine ⟨770233175677631481101549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513488783785087654067699 770233175677631481101549)
          ·
            refine ⟨288837440879111805413081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 770233175677631481101549 288837440879111805413081)
            ·
              refine ⟨216628080659333854059811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288837440879111805413081 216628080659333854059811)
              ·
                refine ⟨324942120989000781089717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216628080659333854059811 324942120989000781089717)
                ·
                  refine ⟨30463323842718823227161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324942120989000781089717 30463323842718823227161)
                  ·
                    rfl

theorem cell22_266972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_266972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266972 prefixEnd_266972 := by exact prefixLift 266972
  have htrace : WordTrace (prefixWord ++ tailWord_266972) baseStart_266972 baseEnd_266972 := by
    simpa [prefixWord, tailWord_266972, baseEnd_266972] using wordTrace_append hprefix tailTrace_266972
  have hstable : (prefixWord ++ tailWord_266972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266972).length < 2 ^ (prefixWord ++ tailWord_266972).sum := by decide
  have hdescent : baseEnd_266972 < baseStart_266972 := by decide
  rcases family_descends (prefixWord ++ tailWord_266972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266998 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_266998 : Nat := 118140960795 + 266998 * 2 ^ 59
def prefixEnd_266998 : Nat := 4983230072969 + 3 ^ 40 * 266998 * 2
def baseEnd_266998 : Nat := 91398871859501068531403

theorem tailTrace_266998 : CollatzResearch.WordTrace tailWord_266998 prefixEnd_266998 91398871859501068531403 := by
  unfold tailWord_266998
  simp only [CollatzResearch.WordTrace]
  refine ⟨608638567919957529571103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6492144724479546982091765 608638567919957529571103)
  ·
    refine ⟨912957851879936294356655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 608638567919957529571103 912957851879936294356655)
    ·
      refine ⟨1369436777819904441534983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 912957851879936294356655 1369436777819904441534983)
      ·
        refine ⟨2054155166729856662302475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369436777819904441534983 2054155166729856662302475)
        ·
          refine ⟨3081232750094784993453713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054155166729856662302475 3081232750094784993453713)
          ·
            refine ⟨2310924562571088745090285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3081232750094784993453713 2310924562571088745090285)
            ·
              refine ⟨866596710964158279408857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2310924562571088745090285 866596710964158279408857)
              ·
                refine ⟨649947533223118709556643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866596710964158279408857 649947533223118709556643)
                ·
                  refine ⟨974921299834678064334965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649947533223118709556643 974921299834678064334965)
                  ·
                    refine ⟨91398871859501068531403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 974921299834678064334965 91398871859501068531403)
                    ·
                      rfl

theorem cell22_266998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_266998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_266998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_266998 prefixEnd_266998 := by exact prefixLift 266998
  have htrace : WordTrace (prefixWord ++ tailWord_266998) baseStart_266998 baseEnd_266998 := by
    simpa [prefixWord, tailWord_266998, baseEnd_266998] using wordTrace_append hprefix tailTrace_266998
  have hstable : (prefixWord ++ tailWord_266998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266998).length < 2 ^ (prefixWord ++ tailWord_266998).sum := by decide
  have hdescent : baseEnd_266998 < baseStart_266998 := by decide
  rcases family_descends (prefixWord ++ tailWord_266998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267015 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 2, 3]
def baseStart_267015 : Nat := 118140960795 + 267015 * 2 ^ 59
def prefixEnd_267015 : Nat := 4983230072969 + 3 ^ 40 * 267015 * 2
def baseEnd_267015 : Nat := 91404691306918690856351

theorem tailTrace_267015 : CollatzResearch.WordTrace tailWord_267015 prefixEnd_267015 91404691306918690856351 := by
  unfold tailWord_267015
  simp only [CollatzResearch.WordTrace]
  refine ⟨9738837127657732376506499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6492558085105154917670999 9738837127657732376506499)
  ·
    refine ⟨14608255691486598564759749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9738837127657732376506499 14608255691486598564759749)
    ·
      refine ⟨2739047942153737230892453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14608255691486598564759749 2739047942153737230892453)
      ·
        refine ⟨513571489153825730792335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2739047942153737230892453 513571489153825730792335)
        ·
          refine ⟨770357233730738596188503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513571489153825730792335 770357233730738596188503)
          ·
            refine ⟨1155535850596107894282755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770357233730738596188503 1155535850596107894282755)
            ·
              refine ⟨1733303775894161841424133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155535850596107894282755 1733303775894161841424133)
              ·
                refine ⟨324994457980155345267025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1733303775894161841424133 324994457980155345267025)
                ·
                  refine ⟨243745843485116508950269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324994457980155345267025 243745843485116508950269)
                  ·
                    refine ⟨91404691306918690856351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243745843485116508950269 91404691306918690856351)
                    ·
                      rfl

theorem cell22_267015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_267015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267015 prefixEnd_267015 := by exact prefixLift 267015
  have htrace : WordTrace (prefixWord ++ tailWord_267015) baseStart_267015 baseEnd_267015 := by
    simpa [prefixWord, tailWord_267015, baseEnd_267015] using wordTrace_append hprefix tailTrace_267015
  have hstable : (prefixWord ++ tailWord_267015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267015).length < 2 ^ (prefixWord ++ tailWord_267015).sum := by decide
  have hdescent : baseEnd_267015 < baseStart_267015 := by decide
  rcases family_descends (prefixWord ++ tailWord_267015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267041 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_267041 : Nat := 118140960795 + 267041 * 2 ^ 59
def prefixEnd_267041 : Nat := 4983230072969 + 3 ^ 40 * 267041 * 2
def baseEnd_267041 : Nat := 91413591638263289706271

theorem tailTrace_267041 : CollatzResearch.WordTrace tailWord_267041 prefixEnd_267041 91413591638263289706271 := by
  unfold tailWord_267041
  simp only [CollatzResearch.WordTrace]
  refine ⟨9739785425563538816952977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6493190283709025877968651 9739785425563538816952977)
  ·
    refine ⟨7304839069172654112714733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9739785425563538816952977 7304839069172654112714733)
    ·
      refine ⟨2739314650939745292268025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7304839069172654112714733 2739314650939745292268025)
      ·
        refine ⟨2054485988204808969201019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2739314650939745292268025 2054485988204808969201019)
        ·
          refine ⟨3081728982307213453801529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054485988204808969201019 3081728982307213453801529)
          ·
            refine ⟨2311296736730410090351147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3081728982307213453801529 2311296736730410090351147)
            ·
              refine ⟨3466945105095615135526721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311296736730410090351147 3466945105095615135526721)
              ·
                refine ⟨2600208828821711351645041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3466945105095615135526721 2600208828821711351645041)
                ·
                  refine ⟨1950156621616283513733781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600208828821711351645041 1950156621616283513733781)
                  ·
                    refine ⟨91413591638263289706271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1950156621616283513733781 91413591638263289706271)
                    ·
                      rfl

theorem cell22_267041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_267041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267041 prefixEnd_267041 := by exact prefixLift 267041
  have htrace : WordTrace (prefixWord ++ tailWord_267041) baseStart_267041 baseEnd_267041 := by
    simpa [prefixWord, tailWord_267041, baseEnd_267041] using wordTrace_append hprefix tailTrace_267041
  have hstable : (prefixWord ++ tailWord_267041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267041).length < 2 ^ (prefixWord ++ tailWord_267041).sum := by decide
  have hdescent : baseEnd_267041 < baseStart_267041 := by decide
  rcases family_descends (prefixWord ++ tailWord_267041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267090 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_267090 : Nat := 118140960795 + 267090 * 2 ^ 59
def prefixEnd_267090 : Nat := 4983230072969 + 3 ^ 40 * 267090 * 2
def baseEnd_267090 : Nat := 30476788446547831743707

theorem tailTrace_267090 : CollatzResearch.WordTrace tailWord_267090 prefixEnd_267090 30476788446547831743707 := by
  unfold tailWord_267090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435393150596505046371681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6494381734924013456991149 2435393150596505046371681)
  ·
    refine ⟨1826544862947378784778761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2435393150596505046371681 1826544862947378784778761)
    ·
      refine ⟨1369908647210534088584071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1826544862947378784778761 1369908647210534088584071)
      ·
        refine ⟨2054862970815801132876107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369908647210534088584071 2054862970815801132876107)
        ·
          refine ⟨3082294456223701699314161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054862970815801132876107 3082294456223701699314161)
          ·
            refine ⟨2311720842167776274485621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3082294456223701699314161 2311720842167776274485621)
            ·
              refine ⟨216723828953229025733027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2311720842167776274485621 216723828953229025733027)
              ·
                refine ⟨325085743429843538599541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216723828953229025733027 325085743429843538599541)
                ·
                  refine ⟨30476788446547831743707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325085743429843538599541 30476788446547831743707)
                  ·
                    rfl

theorem cell22_267090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_267090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267090 prefixEnd_267090 := by exact prefixLift 267090
  have htrace : WordTrace (prefixWord ++ tailWord_267090) baseStart_267090 baseEnd_267090 := by
    simpa [prefixWord, tailWord_267090, baseEnd_267090] using wordTrace_append hprefix tailTrace_267090
  have hstable : (prefixWord ++ tailWord_267090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267090).length < 2 ^ (prefixWord ++ tailWord_267090).sum := by decide
  have hdescent : baseEnd_267090 < baseStart_267090 := by decide
  rcases family_descends (prefixWord ++ tailWord_267090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267154 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_267154 : Nat := 118140960795 + 267154 * 2 ^ 59
def prefixEnd_267154 : Nat := 4983230072969 + 3 ^ 40 * 267154 * 2
def baseEnd_267154 : Nat := 91452273847568661630925

theorem tailTrace_267154 : CollatzResearch.WordTrace tailWord_267154 prefixEnd_267154 91452273847568661630925 := by
  unfold tailWord_267154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435976718538539778954129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6495937916102772743877677 2435976718538539778954129)
  ·
    refine ⟨1826982538903904834215597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2435976718538539778954129 1826982538903904834215597)
    ·
      refine ⟨685118452088964312830849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1826982538903904834215597 685118452088964312830849)
      ·
        refine ⟨513838839066723234623137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685118452088964312830849 513838839066723234623137)
        ·
          refine ⟨385379129300042425967353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513838839066723234623137 385379129300042425967353)
          ·
            refine ⟨289034346975031819475515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385379129300042425967353 289034346975031819475515)
            ·
              refine ⟨433551520462547729213273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289034346975031819475515 433551520462547729213273)
              ·
                refine ⟨325163640346910796909955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433551520462547729213273 325163640346910796909955)
                ·
                  refine ⟨487745460520366195364933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325163640346910796909955 487745460520366195364933)
                  ·
                    refine ⟨91452273847568661630925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487745460520366195364933 91452273847568661630925)
                    ·
                      rfl

theorem cell22_267154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_267154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267154 prefixEnd_267154 := by exact prefixLift 267154
  have htrace : WordTrace (prefixWord ++ tailWord_267154) baseStart_267154 baseEnd_267154 := by
    simpa [prefixWord, tailWord_267154, baseEnd_267154] using wordTrace_append hprefix tailTrace_267154
  have hstable : (prefixWord ++ tailWord_267154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267154).length < 2 ^ (prefixWord ++ tailWord_267154).sum := by decide
  have hdescent : baseEnd_267154 < baseStart_267154 := by decide
  rcases family_descends (prefixWord ++ tailWord_267154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267165 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_267165 : Nat := 118140960795 + 267165 * 2 ^ 59
def prefixEnd_267165 : Nat := 4983230072969 + 3 ^ 40 * 267165 * 2
def baseEnd_267165 : Nat := 91456039372368299605891

theorem tailTrace_267165 : CollatzResearch.WordTrace tailWord_267165 prefixEnd_267165 91456039372368299605891 := by
  unfold tailWord_267165
  simp only [CollatzResearch.WordTrace]
  refine ⟨9744308077114307994466949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6496205384742871996311299 9744308077114307994466949)
  ·
    refine ⟨1827057764458932748962553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9744308077114307994466949 1827057764458932748962553)
    ·
      refine ⟨1370293323344199561721915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1827057764458932748962553 1370293323344199561721915)
      ·
        refine ⟨2055439985016299342582873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1370293323344199561721915 2055439985016299342582873)
        ·
          refine ⟨1541579988762224506937155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2055439985016299342582873 1541579988762224506937155)
          ·
            refine ⟨2312369983143336760405733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541579988762224506937155 2312369983143336760405733)
            ·
              refine ⟨433569371839375642576075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2312369983143336760405733 433569371839375642576075)
              ·
                refine ⟨650354057759063463864113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433569371839375642576075 650354057759063463864113)
                ·
                  refine ⟨487765543319297597898085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 650354057759063463864113 487765543319297597898085)
                  ·
                    refine ⟨91456039372368299605891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487765543319297597898085 91456039372368299605891)
                    ·
                      rfl

theorem cell22_267165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_267165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267165 prefixEnd_267165 := by exact prefixLift 267165
  have htrace : WordTrace (prefixWord ++ tailWord_267165) baseStart_267165 baseEnd_267165 := by
    simpa [prefixWord, tailWord_267165, baseEnd_267165] using wordTrace_append hprefix tailTrace_267165
  have hstable : (prefixWord ++ tailWord_267165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267165).length < 2 ^ (prefixWord ++ tailWord_267165).sum := by decide
  have hdescent : baseEnd_267165 < baseStart_267165 := by decide
  rcases family_descends (prefixWord ++ tailWord_267165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267193 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_267193 : Nat := 118140960795 + 267193 * 2 ^ 59
def prefixEnd_267193 : Nat := 4983230072969 + 3 ^ 40 * 267193 * 2
def baseEnd_267193 : Nat := 91465624344585559905805

theorem tailTrace_267193 : CollatzResearch.WordTrace tailWord_267193 prefixEnd_267193 91465624344585559905805 := by
  unfold tailWord_267193
  simp only [CollatzResearch.WordTrace]
  refine ⟨9745329321012868776486233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6496886214008579184324155 9745329321012868776486233)
  ·
    refine ⟨7308996990759651582364675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9745329321012868776486233 7308996990759651582364675)
    ·
      refine ⟨10963495486139477373547013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7308996990759651582364675 10963495486139477373547013)
      ·
        refine ⟨2055655403651152007540065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10963495486139477373547013 2055655403651152007540065)
        ·
          refine ⟨1541741552738364005655049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2055655403651152007540065 1541741552738364005655049)
          ·
            refine ⟨1156306164553773004241287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541741552738364005655049 1156306164553773004241287)
            ·
              refine ⟨1734459246830659506361931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156306164553773004241287 1734459246830659506361931)
              ·
                refine ⟨2601688870245989259542897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734459246830659506361931 2601688870245989259542897)
                ·
                  refine ⟨1951266652684491944657173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2601688870245989259542897 1951266652684491944657173)
                  ·
                    refine ⟨91465624344585559905805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1951266652684491944657173 91465624344585559905805)
                    ·
                      rfl

theorem cell22_267193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_267193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267193 prefixEnd_267193 := by exact prefixLift 267193
  have htrace : WordTrace (prefixWord ++ tailWord_267193) baseStart_267193 baseEnd_267193 := by
    simpa [prefixWord, tailWord_267193, baseEnd_267193] using wordTrace_append hprefix tailTrace_267193
  have hstable : (prefixWord ++ tailWord_267193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267193).length < 2 ^ (prefixWord ++ tailWord_267193).sum := by decide
  have hdescent : baseEnd_267193 < baseStart_267193 := by decide
  rcases family_descends (prefixWord ++ tailWord_267193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267197 : List Nat := [1, 4, 1, 2, 5, 1, 1, 7]
def baseStart_267197 : Nat := 118140960795 + 267197 * 2 ^ 59
def prefixEnd_267197 : Nat := 4983230072969 + 3 ^ 40 * 267197 * 2
def baseEnd_267197 : Nat := 10162999291814542533977

theorem tailTrace_267197 : CollatzResearch.WordTrace tailWord_267197 prefixEnd_267197 10162999291814542533977 := by
  unfold tailWord_267197
  simp only [CollatzResearch.WordTrace]
  refine ⟨9745475212998377459631845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6496983475332251639754563 9745475212998377459631845)
  ·
    refine ⟨1827276602437195773680971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9745475212998377459631845 1827276602437195773680971)
    ·
      refine ⟨2740914903655793660521457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1827276602437195773680971 2740914903655793660521457)
      ·
        refine ⟨2055686177741845245391093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2740914903655793660521457 2055686177741845245391093)
        ·
          refine ⟨192720579163297991755415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2055686177741845245391093 192720579163297991755415)
          ·
            refine ⟨289080868744946987633123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192720579163297991755415 289080868744946987633123)
            ·
              refine ⟨433621303117420481449685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289080868744946987633123 433621303117420481449685)
              ·
                refine ⟨10162999291814542533977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 433621303117420481449685 10162999291814542533977)
                ·
                  rfl

theorem cell22_267197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 7].length) (baseStart_267197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267197 prefixEnd_267197 := by exact prefixLift 267197
  have htrace : WordTrace (prefixWord ++ tailWord_267197) baseStart_267197 baseEnd_267197 := by
    simpa [prefixWord, tailWord_267197, baseEnd_267197] using wordTrace_append hprefix tailTrace_267197
  have hstable : (prefixWord ++ tailWord_267197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267197).length < 2 ^ (prefixWord ++ tailWord_267197).sum := by decide
  have hdescent : baseEnd_267197 < baseStart_267197 := by decide
  rcases family_descends (prefixWord ++ tailWord_267197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267229 : List Nat := [1, 4, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_267229 : Nat := 118140960795 + 267229 * 2 ^ 59
def prefixEnd_267229 : Nat := 4983230072969 + 3 ^ 40 * 267229 * 2
def baseEnd_267229 : Nat := 91477947880293466005695

theorem tailTrace_267229 : CollatzResearch.WordTrace tailWord_267229 prefixEnd_267229 91477947880293466005695 := by
  unfold tailWord_267229
  simp only [CollatzResearch.WordTrace]
  refine ⟨9746642348882446924796741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6497761565921631283197827 9746642348882446924796741)
  ·
    refine ⟨1827495440415458798399389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9746642348882446924796741 1827495440415458798399389)
    ·
      refine ⟨685310790155797049399771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1827495440415458798399389 685310790155797049399771)
      ·
        refine ⟨1027966185233695574099657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685310790155797049399771 1027966185233695574099657)
        ·
          refine ⟨770974638925271680574743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027966185233695574099657 770974638925271680574743)
          ·
            refine ⟨1156461958387907520862115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770974638925271680574743 1156461958387907520862115)
            ·
              refine ⟨1734692937581861281293173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156461958387907520862115 1734692937581861281293173)
              ·
                refine ⟨162627462898299495121235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1734692937581861281293173 162627462898299495121235)
                ·
                  refine ⟨243941194347449242681853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162627462898299495121235 243941194347449242681853)
                  ·
                    refine ⟨91477947880293466005695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243941194347449242681853 91477947880293466005695)
                    ·
                      rfl

theorem cell22_267229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_267229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267229 prefixEnd_267229 := by exact prefixLift 267229
  have htrace : WordTrace (prefixWord ++ tailWord_267229) baseStart_267229 baseEnd_267229 := by
    simpa [prefixWord, tailWord_267229, baseEnd_267229] using wordTrace_append hprefix tailTrace_267229
  have hstable : (prefixWord ++ tailWord_267229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267229).length < 2 ^ (prefixWord ++ tailWord_267229).sum := by decide
  have hdescent : baseEnd_267229 < baseStart_267229 := by decide
  rcases family_descends (prefixWord ++ tailWord_267229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267242 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_267242 : Nat := 118140960795 + 267242 * 2 ^ 59
def prefixEnd_267242 : Nat := 4983230072969 + 3 ^ 40 * 267242 * 2
def baseEnd_267242 : Nat := 30494132681988588476885

theorem tailTrace_267242 : CollatzResearch.WordTrace tailWord_267242 prefixEnd_267242 30494132681988588476885 := by
  unfold tailWord_267242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2436779124458837536254995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6498077665223566763346653 2436779124458837536254995)
  ·
    refine ⟨3655168686688256304382493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2436779124458837536254995 3655168686688256304382493)
    ·
      refine ⟨1370688257508096114143435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3655168686688256304382493 1370688257508096114143435)
      ·
        refine ⟨2056032386262144171215153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1370688257508096114143435 2056032386262144171215153)
        ·
          refine ⟨1542024289696608128411365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2056032386262144171215153 1542024289696608128411365)
          ·
            refine ⟨289129554318114024077131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1542024289696608128411365 289129554318114024077131)
            ·
              refine ⟨433694331477171036115697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289129554318114024077131 433694331477171036115697)
              ·
                refine ⟨325270748607878277086773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433694331477171036115697 325270748607878277086773)
                ·
                  refine ⟨30494132681988588476885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325270748607878277086773 30494132681988588476885)
                  ·
                    rfl

theorem cell22_267242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_267242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267242 prefixEnd_267242 := by exact prefixLift 267242
  have htrace : WordTrace (prefixWord ++ tailWord_267242) baseStart_267242 baseEnd_267242 := by
    simpa [prefixWord, tailWord_267242, baseEnd_267242] using wordTrace_append hprefix tailTrace_267242
  have hstable : (prefixWord ++ tailWord_267242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267242).length < 2 ^ (prefixWord ++ tailWord_267242).sum := by decide
  have hdescent : baseEnd_267242 < baseStart_267242 := by decide
  rcases family_descends (prefixWord ++ tailWord_267242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267272 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_267272 : Nat := 118140960795 + 267272 * 2 ^ 59
def prefixEnd_267272 : Nat := 4983230072969 + 3 ^ 40 * 267272 * 2
def baseEnd_267272 : Nat := 91492667659055687180563

theorem tailTrace_267272 : CollatzResearch.WordTrace tailWord_267272 prefixEnd_267272 91492667659055687180563 := by
  unfold tailWord_267272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874105343863332634306035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6498807125151110179074713 4874105343863332634306035)
  ·
    refine ⟨7311158015794998951459053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4874105343863332634306035 7311158015794998951459053)
    ·
      refine ⟨2741684255923124606797145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7311158015794998951459053 2741684255923124606797145)
      ·
        refine ⟨2056263191942343455097859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2741684255923124606797145 2056263191942343455097859)
        ·
          refine ⟨3084394787913515182646789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2056263191942343455097859 3084394787913515182646789)
          ·
            refine ⟨578324022733784096746273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3084394787913515182646789 578324022733784096746273)
            ·
              refine ⟨433743017050338072559705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578324022733784096746273 433743017050338072559705)
              ·
                refine ⟨325307262787753554419779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433743017050338072559705 325307262787753554419779)
                ·
                  refine ⟨487960894181630331629669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325307262787753554419779 487960894181630331629669)
                  ·
                    refine ⟨91492667659055687180563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 487960894181630331629669 91492667659055687180563)
                    ·
                      rfl

theorem cell22_267272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_267272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267272 prefixEnd_267272 := by exact prefixLift 267272
  have htrace : WordTrace (prefixWord ++ tailWord_267272) baseStart_267272 baseEnd_267272 := by
    simpa [prefixWord, tailWord_267272, baseEnd_267272] using wordTrace_append hprefix tailTrace_267272
  have hstable : (prefixWord ++ tailWord_267272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267272).length < 2 ^ (prefixWord ++ tailWord_267272).sum := by decide
  have hdescent : baseEnd_267272 < baseStart_267272 := by decide
  rcases family_descends (prefixWord ++ tailWord_267272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267334 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_267334 : Nat := 118140960795 + 267334 * 2 ^ 59
def prefixEnd_267334 : Nat := 4983230072969 + 3 ^ 40 * 267334 * 2
def baseEnd_267334 : Nat := 91513891526108192130373

theorem tailTrace_267334 : CollatzResearch.WordTrace tailWord_267334 prefixEnd_267334 91513891526108192130373 := by
  unfold tailWord_267334
  simp only [CollatzResearch.WordTrace]
  refine ⟨304702250421939058042783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6500314675668033238246037 304702250421939058042783)
  ·
    refine ⟨457053375632908587064175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304702250421939058042783 457053375632908587064175)
    ·
      refine ⟨685580063449362880596263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457053375632908587064175 685580063449362880596263)
      ·
        refine ⟨1028370095174044320894395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685580063449362880596263 1028370095174044320894395)
        ·
          refine ⟨1542555142761066481341593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028370095174044320894395 1542555142761066481341593)
          ·
            refine ⟨1156916357070799861006195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1542555142761066481341593 1156916357070799861006195)
            ·
              refine ⟨1735374535606199791509293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156916357070799861006195 1735374535606199791509293)
              ·
                refine ⟨650765450852324921815985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1735374535606199791509293 650765450852324921815985)
                ·
                  refine ⟨488074088139243691361989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 650765450852324921815985 488074088139243691361989)
                  ·
                    refine ⟨91513891526108192130373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 488074088139243691361989 91513891526108192130373)
                    ·
                      rfl

theorem cell22_267334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_267334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267334 prefixEnd_267334 := by exact prefixLift 267334
  have htrace : WordTrace (prefixWord ++ tailWord_267334) baseStart_267334 baseEnd_267334 := by
    simpa [prefixWord, tailWord_267334, baseEnd_267334] using wordTrace_append hprefix tailTrace_267334
  have hstable : (prefixWord ++ tailWord_267334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267334).length < 2 ^ (prefixWord ++ tailWord_267334).sum := by decide
  have hdescent : baseEnd_267334 < baseStart_267334 := by decide
  rcases family_descends (prefixWord ++ tailWord_267334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267362 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_267362 : Nat := 118140960795 + 267362 * 2 ^ 59
def prefixEnd_267362 : Nat := 4983230072969 + 3 ^ 40 * 267362 * 2
def baseEnd_267362 : Nat := 91523476498325452430287

theorem tailTrace_267362 : CollatzResearch.WordTrace tailWord_267362 prefixEnd_267362 91523476498325452430287 := by
  unfold tailWord_267362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437873314350152659847085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6500995504933740426258893 2437873314350152659847085)
  ·
    refine ⟨914202492881307247442657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2437873314350152659847085 914202492881307247442657)
    ·
      refine ⟨685651869660980435581993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 914202492881307247442657 685651869660980435581993)
      ·
        refine ⟨514238902245735326686495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685651869660980435581993 514238902245735326686495)
        ·
          refine ⟨771358353368602990029743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514238902245735326686495 771358353368602990029743)
          ·
            refine ⟨1157037530052904485044615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771358353368602990029743 1157037530052904485044615)
            ·
              refine ⟨1735556295079356727566923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157037530052904485044615 1735556295079356727566923)
              ·
                refine ⟨2603334442619035091350385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735556295079356727566923 2603334442619035091350385)
                ·
                  refine ⟨1952500831964276318512789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2603334442619035091350385 1952500831964276318512789)
                  ·
                    refine ⟨91523476498325452430287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1952500831964276318512789 91523476498325452430287)
                    ·
                      rfl

theorem cell22_267362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_267362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267362 prefixEnd_267362 := by exact prefixLift 267362
  have htrace : WordTrace (prefixWord ++ tailWord_267362) baseStart_267362 baseEnd_267362 := by
    simpa [prefixWord, tailWord_267362, baseEnd_267362] using wordTrace_append hprefix tailTrace_267362
  have hstable : (prefixWord ++ tailWord_267362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267362).length < 2 ^ (prefixWord ++ tailWord_267362).sum := by decide
  have hdescent : baseEnd_267362 < baseStart_267362 := by decide
  rcases family_descends (prefixWord ++ tailWord_267362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267375 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 2, 5]
def baseStart_267375 : Nat := 118140960795 + 267375 * 2 ^ 59
def prefixEnd_267375 : Nat := 4983230072969 + 3 ^ 40 * 267375 * 2
def baseEnd_267375 : Nat := 91527926663997751855247

theorem tailTrace_267375 : CollatzResearch.WordTrace tailWord_267375 prefixEnd_267375 91527926663997751855247 := by
  unfold tailWord_267375
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751967406353513859611579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6501311604235675906407719 9751967406353513859611579)
  ·
    refine ⟨14627951109530270789417369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9751967406353513859611579 14627951109530270789417369)
    ·
      refine ⟨10970963332147703092063027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14627951109530270789417369 10970963332147703092063027)
      ·
        refine ⟨16456444998221554638094541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10970963332147703092063027 16456444998221554638094541)
        ·
          refine ⟨6171166874333082989285453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16456444998221554638094541 6171166874333082989285453)
          ·
            refine ⟨2314187577874906120982045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6171166874333082989285453 2314187577874906120982045)
            ·
              refine ⟨867820341703089795368267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2314187577874906120982045 867820341703089795368267)
              ·
                refine ⟨1301730512554634693052401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867820341703089795368267 1301730512554634693052401)
                ·
                  refine ⟨976297884415976019789301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1301730512554634693052401 976297884415976019789301)
                  ·
                    refine ⟨91527926663997751855247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 976297884415976019789301 91527926663997751855247)
                    ·
                      rfl

theorem cell22_267375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_267375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267375 prefixEnd_267375 := by exact prefixLift 267375
  have htrace : WordTrace (prefixWord ++ tailWord_267375) baseStart_267375 baseEnd_267375 := by
    simpa [prefixWord, tailWord_267375, baseEnd_267375] using wordTrace_append hprefix tailTrace_267375
  have hstable : (prefixWord ++ tailWord_267375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267375).length < 2 ^ (prefixWord ++ tailWord_267375).sum := by decide
  have hdescent : baseEnd_267375 < baseStart_267375 := by decide
  rcases family_descends (prefixWord ++ tailWord_267375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267381 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_267381 : Nat := 118140960795 + 267381 * 2 ^ 59
def prefixEnd_267381 : Nat := 4983230072969 + 3 ^ 40 * 267381 * 2
def baseEnd_267381 : Nat := 91529980586615736205229

theorem tailTrace_267381 : CollatzResearch.WordTrace tailWord_267381 prefixEnd_267381 91529980586615736205229 := by
  unfold tailWord_267381
  simp only [CollatzResearch.WordTrace]
  refine ⟨9752186244331776884329997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6501457496221184589553331 9752186244331776884329997)
  ·
    refine ⟨3657069841624416331623749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9752186244331776884329997 3657069841624416331623749)
    ·
      refine ⟨685700595304578062179453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3657069841624416331623749 685700595304578062179453)
      ·
        refine ⟨257137723239216773317295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 685700595304578062179453 257137723239216773317295)
        ·
          refine ⟨385706584858825159975943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257137723239216773317295 385706584858825159975943)
          ·
            refine ⟨578559877288237739963915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385706584858825159975943 578559877288237739963915)
            ·
              refine ⟨867839815932356609945873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578559877288237739963915 867839815932356609945873)
              ·
                refine ⟨650879861949267457459405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867839815932356609945873 650879861949267457459405)
                ·
                  refine ⟨244079948230975296547277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650879861949267457459405 244079948230975296547277)
                  ·
                    refine ⟨91529980586615736205229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244079948230975296547277 91529980586615736205229)
                    ·
                      rfl

theorem cell22_267381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_267381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267381 prefixEnd_267381 := by exact prefixLift 267381
  have htrace : WordTrace (prefixWord ++ tailWord_267381) baseStart_267381 baseEnd_267381 := by
    simpa [prefixWord, tailWord_267381, baseEnd_267381] using wordTrace_append hprefix tailTrace_267381
  have hstable : (prefixWord ++ tailWord_267381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267381).length < 2 ^ (prefixWord ++ tailWord_267381).sum := by decide
  have hdescent : baseEnd_267381 < baseStart_267381 := by decide
  rcases family_descends (prefixWord ++ tailWord_267381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267452 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_267452 : Nat := 118140960795 + 267452 * 2 ^ 59
def prefixEnd_267452 : Nat := 4983230072969 + 3 ^ 40 * 267452 * 2
def baseEnd_267452 : Nat := 91554285337595217680011

theorem tailTrace_267452 : CollatzResearch.WordTrace tailWord_267452 prefixEnd_267452 91554285337595217680011 := by
  unfold tailWord_267452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4877387913537278005082305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6503183884716370673443073 4877387913537278005082305)
  ·
    refine ⟨3658040935152958503811729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4877387913537278005082305 3658040935152958503811729)
    ·
      refine ⟨2743530701364718877858797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3658040935152958503811729 2743530701364718877858797)
      ·
        refine ⟨1028824013011769579197049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2743530701364718877858797 1028824013011769579197049)
        ·
          refine ⟨771618009758827184397787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028824013011769579197049 771618009758827184397787)
          ·
            refine ⟨1157427014638240776596681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771618009758827184397787 1157427014638240776596681)
            ·
              refine ⟨868070260978680582447511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157427014638240776596681 868070260978680582447511)
              ·
                refine ⟨1302105391468020873671267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868070260978680582447511 1302105391468020873671267)
                ·
                  refine ⟨1953158087202031310506901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302105391468020873671267 1953158087202031310506901)
                  ·
                    refine ⟨91554285337595217680011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1953158087202031310506901 91554285337595217680011)
                    ·
                      rfl

theorem cell22_267452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_267452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267452 prefixEnd_267452 := by exact prefixLift 267452
  have htrace : WordTrace (prefixWord ++ tailWord_267452) baseStart_267452 baseEnd_267452 := by
    simpa [prefixWord, tailWord_267452, baseEnd_267452] using wordTrace_append hprefix tailTrace_267452
  have hstable : (prefixWord ++ tailWord_267452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267452).length < 2 ^ (prefixWord ++ tailWord_267452).sum := by decide
  have hdescent : baseEnd_267452 < baseStart_267452 := by decide
  rcases family_descends (prefixWord ++ tailWord_267452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267454 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_267454 : Nat := 118140960795 + 267454 * 2 ^ 59
def prefixEnd_267454 : Nat := 4983230072969 + 3 ^ 40 * 267454 * 2
def baseEnd_267454 : Nat := 91554969978467879130005

theorem tailTrace_267454 : CollatzResearch.WordTrace tailWord_267454 prefixEnd_267454 91554969978467879130005 := by
  unfold tailWord_267454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1219356096633413793967177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6503232515378206901158277 1219356096633413793967177)
  ·
    refine ⟨914517072475060345475383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1219356096633413793967177 914517072475060345475383)
    ·
      refine ⟨1371775608712590518213075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914517072475060345475383 1371775608712590518213075)
      ·
        refine ⟨2057663413068885777319613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1371775608712590518213075 2057663413068885777319613)
        ·
          refine ⟨771623779900832166494855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2057663413068885777319613 771623779900832166494855)
          ·
            refine ⟨1157435669851248249742283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771623779900832166494855 1157435669851248249742283)
            ·
              refine ⟨1736153504776872374613425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157435669851248249742283 1736153504776872374613425)
              ·
                refine ⟨1302115128582654280960069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736153504776872374613425 1302115128582654280960069)
                ·
                  refine ⟨244146586609247677680013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302115128582654280960069 244146586609247677680013)
                  ·
                    refine ⟨91554969978467879130005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244146586609247677680013 91554969978467879130005)
                    ·
                      rfl

theorem cell22_267454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_267454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267454 prefixEnd_267454 := by exact prefixLift 267454
  have htrace : WordTrace (prefixWord ++ tailWord_267454) baseStart_267454 baseEnd_267454 := by
    simpa [prefixWord, tailWord_267454, baseEnd_267454] using wordTrace_append hprefix tailTrace_267454
  have hstable : (prefixWord ++ tailWord_267454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267454).length < 2 ^ (prefixWord ++ tailWord_267454).sum := by decide
  have hdescent : baseEnd_267454 < baseStart_267454 := by decide
  rcases family_descends (prefixWord ++ tailWord_267454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267456 : List Nat := [2, 1, 1, 2, 6, 2, 1, 3, 4]
def baseStart_267456 : Nat := 118140960795 + 267456 * 2 ^ 59
def prefixEnd_267456 : Nat := 4983230072969 + 3 ^ 40 * 267456 * 2
def baseEnd_267456 : Nat := 30518551539780180193333

theorem tailTrace_267456 : CollatzResearch.WordTrace tailWord_267456 prefixEnd_267456 30518551539780180193333 := by
  unfold tailWord_267456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4877460859530032346655111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6503281146040043128873481 4877460859530032346655111)
  ·
    refine ⟨7316191289295048519982667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4877460859530032346655111 7316191289295048519982667)
    ·
      refine ⟨10974286933942572779974001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7316191289295048519982667 10974286933942572779974001)
      ·
        refine ⟨8230715200456929584980501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10974286933942572779974001 8230715200456929584980501)
        ·
          refine ⟨385814775021418574295961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8230715200456929584980501 385814775021418574295961)
          ·
            refine ⟨289361081266063930721971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385814775021418574295961 289361081266063930721971)
            ·
              refine ⟨434041621899095896082957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289361081266063930721971 434041621899095896082957)
              ·
                refine ⟨162765608212160961031109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434041621899095896082957 162765608212160961031109)
                ·
                  refine ⟨30518551539780180193333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162765608212160961031109 30518551539780180193333)
                  ·
                    rfl

theorem cell22_267456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 4].length) (baseStart_267456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267456 prefixEnd_267456 := by exact prefixLift 267456
  have htrace : WordTrace (prefixWord ++ tailWord_267456) baseStart_267456 baseEnd_267456 := by
    simpa [prefixWord, tailWord_267456, baseEnd_267456] using wordTrace_append hprefix tailTrace_267456
  have hstable : (prefixWord ++ tailWord_267456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267456).length < 2 ^ (prefixWord ++ tailWord_267456).sum := by decide
  have hdescent : baseEnd_267456 < baseStart_267456 := by decide
  rcases family_descends (prefixWord ++ tailWord_267456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267557 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 8]
def baseStart_267557 : Nat := 118140960795 + 267557 * 2 ^ 59
def prefixEnd_267557 : Nat := 4983230072969 + 3 ^ 40 * 267557 * 2
def baseEnd_267557 : Nat := 30530076327803314601563

theorem tailTrace_267557 : CollatzResearch.WordTrace tailWord_267557 prefixEnd_267557 30530076327803314601563 := by
  unfold tailWord_267557
  simp only [CollatzResearch.WordTrace]
  refine ⟨9758605491694158942736925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6505736994462772628491283 9758605491694158942736925)
  ·
    refine ⟨3659477059385309603526347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9758605491694158942736925 3659477059385309603526347)
    ·
      refine ⟨5489215589077964405289521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3659477059385309603526347 5489215589077964405289521)
      ·
        refine ⟨4116911691808473303967141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5489215589077964405289521 4116911691808473303967141)
        ·
          refine ⟨771920942214088744493839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4116911691808473303967141 771920942214088744493839)
          ·
            refine ⟨1157881413321133116740759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771920942214088744493839 1157881413321133116740759)
            ·
              refine ⟨1736822119981699675111139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157881413321133116740759 1736822119981699675111139)
              ·
                refine ⟨2605233179972549512666709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736822119981699675111139 2605233179972549512666709)
                ·
                  refine ⟨30530076327803314601563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2605233179972549512666709 30530076327803314601563)
                  ·
                    rfl

theorem cell22_267557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_267557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267557 prefixEnd_267557 := by exact prefixLift 267557
  have htrace : WordTrace (prefixWord ++ tailWord_267557) baseStart_267557 baseEnd_267557 := by
    simpa [prefixWord, tailWord_267557, baseEnd_267557] using wordTrace_append hprefix tailTrace_267557
  have hstable : (prefixWord ++ tailWord_267557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267557).length < 2 ^ (prefixWord ++ tailWord_267557).sum := by decide
  have hdescent : baseEnd_267557 < baseStart_267557 := by decide
  rcases family_descends (prefixWord ++ tailWord_267557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267587 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 4, 4]
def baseStart_267587 : Nat := 118140960795 + 267587 * 2 ^ 59
def prefixEnd_267587 : Nat := 4983230072969 + 3 ^ 40 * 267587 * 2
def baseEnd_267587 : Nat := 91600498596499865554597

theorem tailTrace_267587 : CollatzResearch.WordTrace tailWord_267587 prefixEnd_267587 91600498596499865554597 := by
  unfold tailWord_267587
  simp only [CollatzResearch.WordTrace]
  refine ⟨9759699681585474066329015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6506466454390316044219343 9759699681585474066329015)
  ·
    refine ⟨14639549522378211099493523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9759699681585474066329015 14639549522378211099493523)
    ·
      refine ⟨21959324283567316649240285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14639549522378211099493523 21959324283567316649240285)
      ·
        refine ⟨8234746606337743743465107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21959324283567316649240285 8234746606337743743465107)
        ·
          refine ⟨12352119909506615615197661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8234746606337743743465107 12352119909506615615197661)
          ·
            refine ⟨4632044966064980855699123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12352119909506615615197661 4632044966064980855699123)
            ·
              refine ⟨6948067449097471283548685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632044966064980855699123 6948067449097471283548685)
              ·
                refine ⟨2605525293411551731330757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6948067449097471283548685 2605525293411551731330757)
                ·
                  refine ⟨488535992514665949624517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2605525293411551731330757 488535992514665949624517)
                  ·
                    refine ⟨91600498596499865554597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 488535992514665949624517 91600498596499865554597)
                    ·
                      rfl

theorem cell22_267587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 4].length) (baseStart_267587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267587 prefixEnd_267587 := by exact prefixLift 267587
  have htrace : WordTrace (prefixWord ++ tailWord_267587) baseStart_267587 baseEnd_267587 := by
    simpa [prefixWord, tailWord_267587, baseEnd_267587] using wordTrace_append hprefix tailTrace_267587
  have hstable : (prefixWord ++ tailWord_267587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267587).length < 2 ^ (prefixWord ++ tailWord_267587).sum := by decide
  have hdescent : baseEnd_267587 < baseStart_267587 := by decide
  rcases family_descends (prefixWord ++ tailWord_267587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267602 : List Nat := [3, 2, 2, 1, 1, 1, 1, 11]
def baseStart_267602 : Nat := 118140960795 + 267602 * 2 ^ 59
def prefixEnd_267602 : Nat := 4983230072969 + 3 ^ 40 * 267602 * 2
def baseEnd_267602 : Nat := 10178403711449425158839

theorem tailTrace_267602 : CollatzResearch.WordTrace tailWord_267602 prefixEnd_267602 10178403711449425158839 := by
  unfold tailWord_267602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440061694132782907031265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6506831184354087752083373 2440061694132782907031265)
  ·
    refine ⟨1830046270599587180273449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2440061694132782907031265 1830046270599587180273449)
    ·
      refine ⟨1372534702949690385205087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1830046270599587180273449 1372534702949690385205087)
      ·
        refine ⟨2058802054424535577807631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372534702949690385205087 2058802054424535577807631)
        ·
          refine ⟨3088203081636803366711447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058802054424535577807631 3088203081636803366711447)
          ·
            refine ⟨4632304622455205050067171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088203081636803366711447 4632304622455205050067171)
            ·
              refine ⟨6948456933682807575100757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632304622455205050067171 6948456933682807575100757)
              ·
                refine ⟨10178403711449425158839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 6948456933682807575100757 10178403711449425158839)
                ·
                  rfl

theorem cell22_267602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_267602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267602 prefixEnd_267602 := by exact prefixLift 267602
  have htrace : WordTrace (prefixWord ++ tailWord_267602) baseStart_267602 baseEnd_267602 := by
    simpa [prefixWord, tailWord_267602, baseEnd_267602] using wordTrace_append hprefix tailTrace_267602
  have hstable : (prefixWord ++ tailWord_267602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267602).length < 2 ^ (prefixWord ++ tailWord_267602).sum := by decide
  have hdescent : baseEnd_267602 < baseStart_267602 := by decide
  rcases family_descends (prefixWord ++ tailWord_267602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267619 : List Nat := [1, 1, 1, 5, 2, 2, 4, 6]
def baseStart_267619 : Nat := 118140960795 + 267619 * 2 ^ 59
def prefixEnd_267619 : Nat := 4983230072969 + 3 ^ 40 * 267619 * 2
def baseEnd_267619 : Nat := 10179050316718049861611

theorem tailTrace_267619 : CollatzResearch.WordTrace tailWord_267619 prefixEnd_267619 10179050316718049861611 := by
  unfold tailWord_267619
  simp only [CollatzResearch.WordTrace]
  refine ⟨9760866817469543531493911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6507244544979695687662607 9760866817469543531493911)
  ·
    refine ⟨14641300226204315297240867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9760866817469543531493911 14641300226204315297240867)
    ·
      refine ⟨21961950339306472945861301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14641300226204315297240867 21961950339306472945861301)
      ·
        refine ⟨2058932844309981838674497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21961950339306472945861301 2058932844309981838674497)
        ·
          refine ⟨1544199633232486379005873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2058932844309981838674497 1544199633232486379005873)
          ·
            refine ⟨1158149724924364784254405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544199633232486379005873 1158149724924364784254405)
            ·
              refine ⟨217153073423318397047701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1158149724924364784254405 217153073423318397047701)
              ·
                refine ⟨10179050316718049861611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217153073423318397047701 10179050316718049861611)
                ·
                  rfl

theorem cell22_267619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 6].length) (baseStart_267619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267619 prefixEnd_267619 := by exact prefixLift 267619
  have htrace : WordTrace (prefixWord ++ tailWord_267619) baseStart_267619 baseEnd_267619 := by
    simpa [prefixWord, tailWord_267619, baseEnd_267619] using wordTrace_append hprefix tailTrace_267619
  have hstable : (prefixWord ++ tailWord_267619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267619).length < 2 ^ (prefixWord ++ tailWord_267619).sum := by decide
  have hdescent : baseEnd_267619 < baseStart_267619 := by decide
  rcases family_descends (prefixWord ++ tailWord_267619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267651 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 3, 3]
def baseStart_267651 : Nat := 118140960795 + 267651 * 2 ^ 59
def prefixEnd_267651 : Nat := 4983230072969 + 3 ^ 40 * 267651 * 2
def baseEnd_267651 : Nat := 91622407104425031954401

theorem tailTrace_267651 : CollatzResearch.WordTrace tailWord_267651 prefixEnd_267651 91622407104425031954401 := by
  unfold tailWord_267651
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762033953353612996658807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6508022635569075331105871 9762033953353612996658807)
  ·
    refine ⟨14643050930030419494988211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9762033953353612996658807 14643050930030419494988211)
    ·
      refine ⟨21964576395045629242482317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14643050930030419494988211 21964576395045629242482317)
      ·
        refine ⟨8236716148142110965930869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21964576395045629242482317 8236716148142110965930869)
        ·
          refine ⟨772192138888322903056019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8236716148142110965930869 772192138888322903056019)
          ·
            refine ⟨1158288208332484354584029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772192138888322903056019 1158288208332484354584029)
            ·
              refine ⟨434358078124681632969011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1158288208332484354584029 434358078124681632969011)
              ·
                refine ⟨651537117187022449453517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434358078124681632969011 651537117187022449453517)
                ·
                  refine ⟨244326418945133418545069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651537117187022449453517 244326418945133418545069)
                  ·
                    refine ⟨91622407104425031954401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244326418945133418545069 91622407104425031954401)
                    ·
                      rfl

theorem cell22_267651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 3].length) (baseStart_267651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267651 prefixEnd_267651 := by exact prefixLift 267651
  have htrace : WordTrace (prefixWord ++ tailWord_267651) baseStart_267651 baseEnd_267651 := by
    simpa [prefixWord, tailWord_267651, baseEnd_267651] using wordTrace_append hprefix tailTrace_267651
  have hstable : (prefixWord ++ tailWord_267651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267651).length < 2 ^ (prefixWord ++ tailWord_267651).sum := by decide
  have hdescent : baseEnd_267651 < baseStart_267651 := by decide
  rcases family_descends (prefixWord ++ tailWord_267651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267707 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 11]
def baseStart_267707 : Nat := 118140960795 + 267707 * 2 ^ 59
def prefixEnd_267707 : Nat := 4983230072969 + 3 ^ 40 * 267707 * 2
def baseEnd_267707 : Nat := 91641577048859552554229

theorem tailTrace_267707 : CollatzResearch.WordTrace tailWord_267707 prefixEnd_267707 91641577048859552554229 := by
  unfold tailWord_267707
  simp only [CollatzResearch.WordTrace]
  refine ⟨9764076441150734560697375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6509384294100489707131583 9764076441150734560697375)
  ·
    refine ⟨14646114661726101841046063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9764076441150734560697375 14646114661726101841046063)
    ·
      refine ⟨21969171992589152761569095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14646114661726101841046063 21969171992589152761569095)
      ·
        refine ⟨32953757988883729142353643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21969171992589152761569095 32953757988883729142353643)
        ·
          refine ⟨49430636983325593713530465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32953757988883729142353643 49430636983325593713530465)
          ·
            refine ⟨37072977737494195285147849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49430636983325593713530465 37072977737494195285147849)
            ·
              refine ⟨27804733303120646463860887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37072977737494195285147849 27804733303120646463860887)
              ·
                refine ⟨41707099954680969695791331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27804733303120646463860887 41707099954680969695791331)
                ·
                  refine ⟨62560649932021454543686997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41707099954680969695791331 62560649932021454543686997)
                  ·
                    refine ⟨91641577048859552554229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 62560649932021454543686997 91641577048859552554229)
                    ·
                      rfl

theorem cell22_267707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_267707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267707 prefixEnd_267707 := by exact prefixLift 267707
  have htrace : WordTrace (prefixWord ++ tailWord_267707) baseStart_267707 baseEnd_267707 := by
    simpa [prefixWord, tailWord_267707, baseEnd_267707] using wordTrace_append hprefix tailTrace_267707
  have hstable : (prefixWord ++ tailWord_267707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267707).length < 2 ^ (prefixWord ++ tailWord_267707).sum := by decide
  have hdescent : baseEnd_267707 < baseStart_267707 := by decide
  rcases family_descends (prefixWord ++ tailWord_267707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267709 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 6]
def baseStart_267709 : Nat := 118140960795 + 267709 * 2 ^ 59
def prefixEnd_267709 : Nat := 4983230072969 + 3 ^ 40 * 267709 * 2
def baseEnd_267709 : Nat := 30547420563244071334741

theorem tailTrace_267709 : CollatzResearch.WordTrace tailWord_267709 prefixEnd_267709 30547420563244071334741 := by
  unfold tailWord_267709
  simp only [CollatzResearch.WordTrace]
  refine ⟨9764149387143488902270181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6509432924762325934846787 9764149387143488902270181)
  ·
    refine ⟨1830778010089404169175659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9764149387143488902270181 1830778010089404169175659)
    ·
      refine ⟨2746167015134106253763489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830778010089404169175659 2746167015134106253763489)
      ·
        refine ⟨2059625261350579690322617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2746167015134106253763489 2059625261350579690322617)
        ·
          refine ⟨1544718946012934767741963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2059625261350579690322617 1544718946012934767741963)
          ·
            refine ⟨2317078419019402151612945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544718946012934767741963 2317078419019402151612945)
            ·
              refine ⟨1737808814264551613709709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317078419019402151612945 1737808814264551613709709)
              ·
                refine ⟨651678305349206855141141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1737808814264551613709709 651678305349206855141141)
                ·
                  refine ⟨30547420563244071334741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 651678305349206855141141 30547420563244071334741)
                  ·
                    rfl

theorem cell22_267709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_267709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267709 prefixEnd_267709 := by exact prefixLift 267709
  have htrace : WordTrace (prefixWord ++ tailWord_267709) baseStart_267709 baseEnd_267709 := by
    simpa [prefixWord, tailWord_267709, baseEnd_267709] using wordTrace_append hprefix tailTrace_267709
  have hstable : (prefixWord ++ tailWord_267709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267709).length < 2 ^ (prefixWord ++ tailWord_267709).sum := by decide
  have hdescent : baseEnd_267709 < baseStart_267709 := by decide
  rcases family_descends (prefixWord ++ tailWord_267709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267741 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_267741 : Nat := 118140960795 + 267741 * 2 ^ 59
def prefixEnd_267741 : Nat := 4983230072969 + 3 ^ 40 * 267741 * 2
def baseEnd_267741 : Nat := 91653215943694797204125

theorem tailTrace_267741 : CollatzResearch.WordTrace tailWord_267741 prefixEnd_267741 91653215943694797204125 := by
  unfold tailWord_267741
  simp only [CollatzResearch.WordTrace]
  refine ⟨9765316523027558367435077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6510211015351705578290051 9765316523027558367435077)
  ·
    refine ⟨1830996848067667193894077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9765316523027558367435077 1830996848067667193894077)
    ·
      refine ⟨686623818025375197710279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1830996848067667193894077 686623818025375197710279)
      ·
        refine ⟨1029935727038062796565419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686623818025375197710279 1029935727038062796565419)
        ·
          refine ⟨1544903590557094194848129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029935727038062796565419 1544903590557094194848129)
          ·
            refine ⟨1158677692917820646136097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544903590557094194848129 1158677692917820646136097)
            ·
              refine ⟨869008269688365484602073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158677692917820646136097 869008269688365484602073)
              ·
                refine ⟨651756202266274113451555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869008269688365484602073 651756202266274113451555)
                ·
                  refine ⟨977634303399411170177333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651756202266274113451555 977634303399411170177333)
                  ·
                    refine ⟨91653215943694797204125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 977634303399411170177333 91653215943694797204125)
                    ·
                      rfl

theorem cell22_267741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_267741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267741 prefixEnd_267741 := by exact prefixLift 267741
  have htrace : WordTrace (prefixWord ++ tailWord_267741) baseStart_267741 baseEnd_267741 := by
    simpa [prefixWord, tailWord_267741, baseEnd_267741] using wordTrace_append hprefix tailTrace_267741
  have hstable : (prefixWord ++ tailWord_267741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267741).length < 2 ^ (prefixWord ++ tailWord_267741).sum := by decide
  have hdescent : baseEnd_267741 < baseStart_267741 := by decide
  rcases family_descends (prefixWord ++ tailWord_267741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267784 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_267784 : Nat := 118140960795 + 267784 * 2 ^ 59
def prefixEnd_267784 : Nat := 4983230072969 + 3 ^ 40 * 267784 * 2
def baseEnd_267784 : Nat := 91667935722457018378993

theorem tailTrace_267784 : CollatzResearch.WordTrace tailWord_267784 prefixEnd_267784 91667935722457018378993 := by
  unfold tailWord_267784
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883442430935888355625203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6511256574581184474166937 4883442430935888355625203)
  ·
    refine ⟨7325163646403832533437805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4883442430935888355625203 7325163646403832533437805)
    ·
      refine ⟨2746936367401437200039177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7325163646403832533437805 2746936367401437200039177)
      ·
        refine ⟨2060202275551077900029383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2746936367401437200039177 2060202275551077900029383)
        ·
          refine ⟨3090303413326616850044075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060202275551077900029383 3090303413326616850044075)
          ·
            refine ⟨4635455119989925275066113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090303413326616850044075 4635455119989925275066113)
            ·
              refine ⟨3476591339992443956299585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4635455119989925275066113 3476591339992443956299585)
              ·
                refine ⟨2607443504994332967224689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3476591339992443956299585 2607443504994332967224689)
                ·
                  refine ⟨1955582628745749725418517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2607443504994332967224689 1955582628745749725418517)
                  ·
                    refine ⟨91667935722457018378993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1955582628745749725418517 91667935722457018378993)
                    ·
                      rfl

theorem cell22_267784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_267784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267784 prefixEnd_267784 := by exact prefixLift 267784
  have htrace : WordTrace (prefixWord ++ tailWord_267784) baseStart_267784 baseEnd_267784 := by
    simpa [prefixWord, tailWord_267784, baseEnd_267784] using wordTrace_append hprefix tailTrace_267784
  have hstable : (prefixWord ++ tailWord_267784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267784).length < 2 ^ (prefixWord ++ tailWord_267784).sum := by decide
  have hdescent : baseEnd_267784 < baseStart_267784 := by decide
  rcases family_descends (prefixWord ++ tailWord_267784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267788 : List Nat := [2, 2, 1, 2, 5, 2, 2, 6]
def baseStart_267788 : Nat := 118140960795 + 267788 * 2 ^ 59
def prefixEnd_267788 : Nat := 4983230072969 + 3 ^ 40 * 267788 * 2
def baseEnd_267788 : Nat := 10185478333800260142109

theorem tailTrace_267788 : CollatzResearch.WordTrace tailWord_267788 prefixEnd_267788 10185478333800260142109 := by
  unfold tailWord_267788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883515376928642697198009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6511353835904856929597345 4883515376928642697198009)
  ·
    refine ⟨3662636532696482022898507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4883515376928642697198009 3662636532696482022898507)
    ·
      refine ⟨5493954799044723034347761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3662636532696482022898507 5493954799044723034347761)
      ·
        refine ⟨4120466099283542275760821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5493954799044723034347761 4120466099283542275760821)
        ·
          refine ⟨386293696807832088352577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4120466099283542275760821 386293696807832088352577)
          ·
            refine ⟨289720272605874066264433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386293696807832088352577 289720272605874066264433)
            ·
              refine ⟨217290204454405549698325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289720272605874066264433 217290204454405549698325)
              ·
                refine ⟨10185478333800260142109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217290204454405549698325 10185478333800260142109)
                ·
                  rfl

theorem cell22_267788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 6].length) (baseStart_267788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267788 prefixEnd_267788 := by exact prefixLift 267788
  have htrace : WordTrace (prefixWord ++ tailWord_267788) baseStart_267788 baseEnd_267788 := by
    simpa [prefixWord, tailWord_267788, baseEnd_267788] using wordTrace_append hprefix tailTrace_267788
  have hstable : (prefixWord ++ tailWord_267788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267788).length < 2 ^ (prefixWord ++ tailWord_267788).sum := by decide
  have hdescent : baseEnd_267788 < baseStart_267788 := by decide
  rcases family_descends (prefixWord ++ tailWord_267788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267833 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 5]
def baseStart_267833 : Nat := 118140960795 + 267833 * 2 ^ 59
def prefixEnd_267833 : Nat := 4983230072969 + 3 ^ 40 * 267833 * 2
def baseEnd_267833 : Nat := 30561569807945741301281

theorem tailTrace_267833 : CollatzResearch.WordTrace tailWord_267833 prefixEnd_267833 30561569807945741301281 := by
  unfold tailWord_267833
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768672038694258079784153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6512448025796172053189435 9768672038694258079784153)
  ·
    refine ⟨7326504029020693559838115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9768672038694258079784153 7326504029020693559838115)
    ·
      refine ⟨10989756043531040339757173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7326504029020693559838115 10989756043531040339757173)
      ·
        refine ⟨1030289629081035031852235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10989756043531040339757173 1030289629081035031852235)
        ·
          refine ⟨1545434443621552547778353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030289629081035031852235 1545434443621552547778353)
          ·
            refine ⟨1159075832716164410833765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1545434443621552547778353 1159075832716164410833765)
            ·
              refine ⟨217326718634280827031331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1159075832716164410833765 217326718634280827031331)
              ·
                refine ⟨325990077951421240546997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217326718634280827031331 325990077951421240546997)
                ·
                  refine ⟨30561569807945741301281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325990077951421240546997 30561569807945741301281)
                  ·
                    rfl

theorem cell22_267833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_267833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267833 prefixEnd_267833 := by exact prefixLift 267833
  have htrace : WordTrace (prefixWord ++ tailWord_267833) baseStart_267833 baseEnd_267833 := by
    simpa [prefixWord, tailWord_267833, baseEnd_267833] using wordTrace_append hprefix tailTrace_267833
  have hstable : (prefixWord ++ tailWord_267833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267833).length < 2 ^ (prefixWord ++ tailWord_267833).sum := by decide
  have hdescent : baseEnd_267833 < baseStart_267833 := by decide
  rcases family_descends (prefixWord ++ tailWord_267833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267893 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_267893 : Nat := 118140960795 + 267893 * 2 ^ 59
def prefixEnd_267893 : Nat := 4983230072969 + 3 ^ 40 * 267893 * 2
def baseEnd_267893 : Nat := 91705248650017067403659

theorem tailTrace_267893 : CollatzResearch.WordTrace tailWord_267893 prefixEnd_267893 91705248650017067403659 := by
  unfold tailWord_267893
  simp only [CollatzResearch.WordTrace]
  refine ⟨9770860418476888326968333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6513906945651258884645555 9770860418476888326968333)
  ·
    refine ⟨3664072656928833122613125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9770860418476888326968333 3664072656928833122613125)
    ·
      refine ⟨687013623174156210489961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3664072656928833122613125 687013623174156210489961)
      ·
        refine ⟨515260217380617157867471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687013623174156210489961 515260217380617157867471)
        ·
          refine ⟨772890326070925736801207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515260217380617157867471 772890326070925736801207)
          ·
            refine ⟨1159335489106388605201811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772890326070925736801207 1159335489106388605201811)
            ·
              refine ⟨1739003233659582907802717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159335489106388605201811 1739003233659582907802717)
              ·
                refine ⟨652126212622343590426019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1739003233659582907802717 652126212622343590426019)
                ·
                  refine ⟨978189318933515385639029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652126212622343590426019 978189318933515385639029)
                  ·
                    refine ⟨91705248650017067403659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 978189318933515385639029 91705248650017067403659)
                    ·
                      rfl

theorem cell22_267893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_267893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267893 prefixEnd_267893 := by exact prefixLift 267893
  have htrace : WordTrace (prefixWord ++ tailWord_267893) baseStart_267893 baseEnd_267893 := by
    simpa [prefixWord, tailWord_267893, baseEnd_267893] using wordTrace_append hprefix tailTrace_267893
  have hstable : (prefixWord ++ tailWord_267893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267893).length < 2 ^ (prefixWord ++ tailWord_267893).sum := by decide
  have hdescent : baseEnd_267893 < baseStart_267893 := by decide
  rcases family_descends (prefixWord ++ tailWord_267893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267908 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_267908 : Nat := 118140960795 + 267908 * 2 ^ 59
def prefixEnd_267908 : Nat := 4983230072969 + 3 ^ 40 * 267908 * 2
def baseEnd_267908 : Nat := 91710383456562028278613

theorem tailTrace_267908 : CollatzResearch.WordTrace tailWord_267908 prefixEnd_267908 91710383456562028278613 := by
  unfold tailWord_267908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885703756711272944382189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6514271675615030592509585 4885703756711272944382189)
  ·
    refine ⟨1832138908766727354143321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4885703756711272944382189 1832138908766727354143321)
    ·
      refine ⟨1374104181575045515607491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1832138908766727354143321 1374104181575045515607491)
      ·
        refine ⟨2061156272362568273411237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374104181575045515607491 2061156272362568273411237)
        ·
          refine ⟨386466801067981551264607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2061156272362568273411237 386466801067981551264607)
          ·
            refine ⟨579700201601972326896911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386466801067981551264607 579700201601972326896911)
            ·
              refine ⟨869550302402958490345367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579700201601972326896911 869550302402958490345367)
              ·
                refine ⟨1304325453604437735518051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869550302402958490345367 1304325453604437735518051)
                ·
                  refine ⟨1956488180406656603277077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304325453604437735518051 1956488180406656603277077)
                  ·
                    refine ⟨91710383456562028278613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1956488180406656603277077 91710383456562028278613)
                    ·
                      rfl

theorem cell22_267908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_267908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267908 prefixEnd_267908 := by exact prefixLift 267908
  have htrace : WordTrace (prefixWord ++ tailWord_267908) baseStart_267908 baseEnd_267908 := by
    simpa [prefixWord, tailWord_267908, baseEnd_267908] using wordTrace_append hprefix tailTrace_267908
  have hstable : (prefixWord ++ tailWord_267908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267908).length < 2 ^ (prefixWord ++ tailWord_267908).sum := by decide
  have hdescent : baseEnd_267908 < baseStart_267908 := by decide
  rcases family_descends (prefixWord ++ tailWord_267908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267912 : List Nat := [2, 1, 3, 5, 1, 1, 2, 3, 4]
def baseStart_267912 : Nat := 118140960795 + 267912 * 2 ^ 59
def prefixEnd_267912 : Nat := 4983230072969 + 3 ^ 40 * 267912 * 2
def baseEnd_267912 : Nat := 30570584246102450392867

theorem tailTrace_267912 : CollatzResearch.WordTrace tailWord_267912 prefixEnd_267912 30570584246102450392867 := by
  unfold tailWord_267912
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885776702704027285954995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6514368936938703047939993 4885776702704027285954995)
  ·
    refine ⟨7328665054056040928932493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4885776702704027285954995 7328665054056040928932493)
    ·
      refine ⟨2748249395271015348349685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7328665054056040928932493 2748249395271015348349685)
      ·
        refine ⟨257648380806657688907783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2748249395271015348349685 257648380806657688907783)
        ·
          refine ⟨386472571209986533361675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257648380806657688907783 386472571209986533361675)
          ·
            refine ⟨579708856814979800042513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386472571209986533361675 579708856814979800042513)
            ·
              refine ⟨434781642611234850031885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579708856814979800042513 434781642611234850031885)
              ·
                refine ⟨163043115979213068761957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434781642611234850031885 163043115979213068761957)
                ·
                  refine ⟨30570584246102450392867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163043115979213068761957 30570584246102450392867)
                  ·
                    rfl

theorem cell22_267912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 4].length) (baseStart_267912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267912 prefixEnd_267912 := by exact prefixLift 267912
  have htrace : WordTrace (prefixWord ++ tailWord_267912) baseStart_267912 baseEnd_267912 := by
    simpa [prefixWord, tailWord_267912, baseEnd_267912] using wordTrace_append hprefix tailTrace_267912
  have hstable : (prefixWord ++ tailWord_267912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267912).length < 2 ^ (prefixWord ++ tailWord_267912).sum := by decide
  have hdescent : baseEnd_267912 < baseStart_267912 := by decide
  rcases family_descends (prefixWord ++ tailWord_267912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267944 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 1, 5]
def baseStart_267944 : Nat := 118140960795 + 267944 * 2 ^ 59
def prefixEnd_267944 : Nat := 4983230072969 + 3 ^ 40 * 267944 * 2
def baseEnd_267944 : Nat := 91722706992269934378503

theorem tailTrace_267944 : CollatzResearch.WordTrace tailWord_267944 prefixEnd_267944 91722706992269934378503 := by
  unfold tailWord_267944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886360270646062018537443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6515147027528082691383257 4886360270646062018537443)
  ·
    refine ⟨7329540405969093027806165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4886360270646062018537443 7329540405969093027806165)
    ·
      refine ⟨171786103264900617839207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7329540405969093027806165 171786103264900617839207)
      ·
        refine ⟨257679154897350926758811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171786103264900617839207 257679154897350926758811)
        ·
          refine ⟨386518732346026390138217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257679154897350926758811 386518732346026390138217)
          ·
            refine ⟨289889049259519792603663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386518732346026390138217 289889049259519792603663)
            ·
              refine ⟨434833573889279688905495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289889049259519792603663 434833573889279688905495)
              ·
                refine ⟨652250360833919533358243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434833573889279688905495 652250360833919533358243)
                ·
                  refine ⟨978375541250879300037365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652250360833919533358243 978375541250879300037365)
                  ·
                    refine ⟨91722706992269934378503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 978375541250879300037365 91722706992269934378503)
                    ·
                      rfl

theorem cell22_267944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_267944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267944 prefixEnd_267944 := by exact prefixLift 267944
  have htrace : WordTrace (prefixWord ++ tailWord_267944) baseStart_267944 baseEnd_267944 := by
    simpa [prefixWord, tailWord_267944, baseEnd_267944] using wordTrace_append hprefix tailTrace_267944
  have hstable : (prefixWord ++ tailWord_267944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267944).length < 2 ^ (prefixWord ++ tailWord_267944).sum := by decide
  have hdescent : baseEnd_267944 < baseStart_267944 := by decide
  rcases family_descends (prefixWord ++ tailWord_267944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267957 : List Nat := [1, 3, 3, 3, 3, 1, 2, 6]
def baseStart_267957 : Nat := 118140960795 + 267957 * 2 ^ 59
def prefixEnd_267957 : Nat := 4983230072969 + 3 ^ 40 * 267957 * 2
def baseEnd_267957 : Nat := 10191906350882470422607

theorem tailTrace_267957 : CollatzResearch.WordTrace tailWord_267957 prefixEnd_267957 10191906350882470422607 := by
  unfold tailWord_267957
  simp only [CollatzResearch.WordTrace]
  refine ⟨9773194690245027257298125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6515463126830018171532083 9773194690245027257298125)
  ·
    refine ⟨3664948008841885221486797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9773194690245027257298125 3664948008841885221486797)
    ·
      refine ⟨1374355503315706958057549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3664948008841885221486797 1374355503315706958057549)
      ·
        refine ⟨515383313743390109271581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1374355503315706958057549 515383313743390109271581)
        ·
          refine ⟨193268742653771290976843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515383313743390109271581 193268742653771290976843)
          ·
            refine ⟨289903113980656936465265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193268742653771290976843 289903113980656936465265)
            ·
              refine ⟨217427335485492702348949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289903113980656936465265 217427335485492702348949)
              ·
                refine ⟨10191906350882470422607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217427335485492702348949 10191906350882470422607)
                ·
                  rfl

theorem cell22_267957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 6].length) (baseStart_267957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_267957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_267957 prefixEnd_267957 := by exact prefixLift 267957
  have htrace : WordTrace (prefixWord ++ tailWord_267957) baseStart_267957 baseEnd_267957 := by
    simpa [prefixWord, tailWord_267957, baseEnd_267957] using wordTrace_append hprefix tailTrace_267957
  have hstable : (prefixWord ++ tailWord_267957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267957).length < 2 ^ (prefixWord ++ tailWord_267957).sum := by decide
  have hdescent : baseEnd_267957 < baseStart_267957 := by decide
  rcases family_descends (prefixWord ++ tailWord_267957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268028 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_268028 : Nat := 118140960795 + 268028 * 2 ^ 59
def prefixEnd_268028 : Nat := 4983230072969 + 3 ^ 40 * 268028 * 2
def baseEnd_268028 : Nat := 91751461908921715278245

theorem tailTrace_268028 : CollatzResearch.WordTrace tailWord_268028 prefixEnd_268028 91751461908921715278245 := by
  unfold tailWord_268028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4887892136493903191566369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6517189515325204255421825 4887892136493903191566369)
  ·
    refine ⟨3665919102370427393674777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4887892136493903191566369 3665919102370427393674777)
    ·
      refine ⟨2749439326777820545256083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3665919102370427393674777 2749439326777820545256083)
      ·
        refine ⟨4124158990166730817884125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2749439326777820545256083 4124158990166730817884125)
        ·
          refine ⟨1546559621312524056706547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4124158990166730817884125 1546559621312524056706547)
          ·
            refine ⟨2319839431968786085059821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546559621312524056706547 2319839431968786085059821)
            ·
              refine ⟨869939786988294781897433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2319839431968786085059821 869939786988294781897433)
              ·
                refine ⟨652454840241221086423075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869939786988294781897433 652454840241221086423075)
                ·
                  refine ⟨978682260361831629634613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652454840241221086423075 978682260361831629634613)
                  ·
                    refine ⟨91751461908921715278245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 978682260361831629634613 91751461908921715278245)
                    ·
                      rfl

theorem cell22_268028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_268028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268028 prefixEnd_268028 := by exact prefixLift 268028
  have htrace : WordTrace (prefixWord ++ tailWord_268028) baseStart_268028 baseEnd_268028 := by
    simpa [prefixWord, tailWord_268028, baseEnd_268028] using wordTrace_append hprefix tailTrace_268028
  have hstable : (prefixWord ++ tailWord_268028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268028).length < 2 ^ (prefixWord ++ tailWord_268028).sum := by decide
  have hdescent : baseEnd_268028 < baseStart_268028 := by decide
  rcases family_descends (prefixWord ++ tailWord_268028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268043 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 2, 4]
def baseStart_268043 : Nat := 118140960795 + 268043 * 2 ^ 59
def prefixEnd_268043 : Nat := 4983230072969 + 3 ^ 40 * 268043 * 2
def baseEnd_268043 : Nat := 91756596715466676153199

theorem tailTrace_268043 : CollatzResearch.WordTrace tailWord_268043 prefixEnd_268043 91756596715466676153199 := by
  unfold tailWord_268043
  simp only [CollatzResearch.WordTrace]
  refine ⟨9776331367933463944928783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6517554245288975963285855 9776331367933463944928783)
  ·
    refine ⟨14664497051900195917393175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9776331367933463944928783 14664497051900195917393175)
    ·
      refine ⟨21996745577850293876089763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14664497051900195917393175 21996745577850293876089763)
      ·
        refine ⟨32995118366775440814134645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21996745577850293876089763 32995118366775440814134645)
        ·
          refine ⟨3093292346885197576325123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32995118366775440814134645 3093292346885197576325123)
          ·
            refine ⟨4639938520327796364487685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093292346885197576325123 4639938520327796364487685)
            ·
              refine ⟨869988472561461818341441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4639938520327796364487685 869988472561461818341441)
              ·
                refine ⟨652491354421096363756081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869988472561461818341441 652491354421096363756081)
                ·
                  refine ⟨489368515815822272817061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652491354421096363756081 489368515815822272817061)
                  ·
                    refine ⟨91756596715466676153199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489368515815822272817061 91756596715466676153199)
                    ·
                      rfl

theorem cell22_268043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 4].length) (baseStart_268043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268043 prefixEnd_268043 := by exact prefixLift 268043
  have htrace : WordTrace (prefixWord ++ tailWord_268043) baseStart_268043 baseEnd_268043 := by
    simpa [prefixWord, tailWord_268043, baseEnd_268043] using wordTrace_append hprefix tailTrace_268043
  have hstable : (prefixWord ++ tailWord_268043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268043).length < 2 ^ (prefixWord ++ tailWord_268043).sum := by decide
  have hdescent : baseEnd_268043 < baseStart_268043 := by decide
  rcases family_descends (prefixWord ++ tailWord_268043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268058 : List Nat := [3, 1, 1, 3, 2, 2, 3, 7]
def baseStart_268058 : Nat := 118140960795 + 268058 * 2 ^ 59
def prefixEnd_268058 : Nat := 4983230072969 + 3 ^ 40 * 268058 * 2
def baseEnd_268058 : Nat := 10195747946890181892017

theorem tailTrace_268058 : CollatzResearch.WordTrace tailWord_268058 prefixEnd_268058 10195747946890181892017 := by
  unfold tailWord_268058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444219615719780376681207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6517918975252747671149885 2444219615719780376681207)
  ·
    refine ⟨3666329423579670565021811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2444219615719780376681207 3666329423579670565021811)
    ·
      refine ⟨5499494135369505847532717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3666329423579670565021811 5499494135369505847532717)
      ·
        refine ⟨2062310300763564692824769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5499494135369505847532717 2062310300763564692824769)
        ·
          refine ⟨1546732725572673519618577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2062310300763564692824769 1546732725572673519618577)
          ·
            refine ⟨1160049544179505139713933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1546732725572673519618577 1160049544179505139713933)
            ·
              refine ⟨435018579067314427392725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1160049544179505139713933 435018579067314427392725)
              ·
                refine ⟨10195747946890181892017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 435018579067314427392725 10195747946890181892017)
                ·
                  rfl

theorem cell22_268058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_268058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268058 prefixEnd_268058 := by exact prefixLift 268058
  have htrace : WordTrace (prefixWord ++ tailWord_268058) baseStart_268058 baseEnd_268058 := by
    simpa [prefixWord, tailWord_268058, baseEnd_268058] using wordTrace_append hprefix tailTrace_268058
  have hstable : (prefixWord ++ tailWord_268058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268058).length < 2 ^ (prefixWord ++ tailWord_268058).sum := by decide
  have hdescent : baseEnd_268058 < baseStart_268058 := by decide
  rcases family_descends (prefixWord ++ tailWord_268058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268158 : List Nat := [4, 2, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_268158 : Nat := 118140960795 + 268158 * 2 ^ 59
def prefixEnd_268158 : Nat := 4983230072969 + 3 ^ 40 * 268158 * 2
def baseEnd_268158 : Nat := 91795963565644709527847

theorem tailTrace_268158 : CollatzResearch.WordTrace tailWord_268158 prefixEnd_268158 91795963565644709527847 := by
  unfold tailWord_268158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222565720314604823170641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6520350508344559056910085 1222565720314604823170641)
  ·
    refine ⟨916924290235953617377981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1222565720314604823170641 916924290235953617377981)
    ·
      refine ⟨343846608838482606516743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 916924290235953617377981 343846608838482606516743)
      ·
        refine ⟨515769913257723909775115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343846608838482606516743 515769913257723909775115)
        ·
          refine ⟨773654869886585864662673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515769913257723909775115 773654869886585864662673)
          ·
            refine ⟨580241152414939398497005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 773654869886585864662673 580241152414939398497005)
            ·
              refine ⟨217590432155602274436377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580241152414939398497005 217590432155602274436377)
              ·
                refine ⟨163192824116701705827283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217590432155602274436377 163192824116701705827283)
                ·
                  refine ⟨244789236175052558740925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163192824116701705827283 244789236175052558740925)
                  ·
                    refine ⟨91795963565644709527847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244789236175052558740925 91795963565644709527847)
                    ·
                      rfl

theorem cell22_268158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_268158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268158 prefixEnd_268158 := by exact prefixLift 268158
  have htrace : WordTrace (prefixWord ++ tailWord_268158) baseStart_268158 baseEnd_268158 := by
    simpa [prefixWord, tailWord_268158, baseEnd_268158] using wordTrace_append hprefix tailTrace_268158
  have hstable : (prefixWord ++ tailWord_268158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268158).length < 2 ^ (prefixWord ++ tailWord_268158).sum := by decide
  have hdescent : baseEnd_268158 < baseStart_268158 := by decide
  rcases family_descends (prefixWord ++ tailWord_268158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268223 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 1, 8]
def baseStart_268223 : Nat := 118140960795 + 268223 * 2 ^ 59
def prefixEnd_268223 : Nat := 4983230072969 + 3 ^ 40 * 268223 * 2
def baseEnd_268223 : Nat := 91818214394006206652647

theorem tailTrace_268223 : CollatzResearch.WordTrace tailWord_268223 prefixEnd_268223 91818214394006206652647 := by
  unfold tailWord_268223
  simp only [CollatzResearch.WordTrace]
  refine ⟨9782896507281354686481323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6521931004854236457654215 9782896507281354686481323)
  ·
    refine ⟨14674344760922032029721985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9782896507281354686481323 14674344760922032029721985)
    ·
      refine ⟨11005758570691524022291489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14674344760922032029721985 11005758570691524022291489)
      ·
        refine ⟨8254318928018643016718617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11005758570691524022291489 8254318928018643016718617)
        ·
          refine ⟨6190739196013982262538963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8254318928018643016718617 6190739196013982262538963)
          ·
            refine ⟨9286108794020973393808445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6190739196013982262538963 9286108794020973393808445)
            ·
              refine ⟨3482290797757865022678167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9286108794020973393808445 3482290797757865022678167)
              ·
                refine ⟨5223436196636797534017251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482290797757865022678167 5223436196636797534017251)
                ·
                  refine ⟨7835154294955196301025877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5223436196636797534017251 7835154294955196301025877)
                  ·
                    refine ⟨91818214394006206652647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7835154294955196301025877 91818214394006206652647)
                    ·
                      rfl

theorem cell22_268223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_268223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268223 prefixEnd_268223 := by exact prefixLift 268223
  have htrace : WordTrace (prefixWord ++ tailWord_268223) baseStart_268223 baseEnd_268223 := by
    simpa [prefixWord, tailWord_268223, baseEnd_268223] using wordTrace_append hprefix tailTrace_268223
  have hstable : (prefixWord ++ tailWord_268223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268223).length < 2 ^ (prefixWord ++ tailWord_268223).sum := by decide
  have hdescent : baseEnd_268223 < baseStart_268223 := by decide
  rcases family_descends (prefixWord ++ tailWord_268223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268246 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_268246 : Nat := 118140960795 + 268246 * 2 ^ 59
def prefixEnd_268246 : Nat := 4983230072969 + 3 ^ 40 * 268246 * 2
def baseEnd_268246 : Nat := 91826087764041813327577

theorem tailTrace_268246 : CollatzResearch.WordTrace tailWord_268246 prefixEnd_268246 91826087764041813327577 := by
  unfold tailWord_268246
  simp only [CollatzResearch.WordTrace]
  refine ⟨611483461637376850910537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6522490257465353076379061 611483461637376850910537)
  ·
    refine ⟨458612596228032638182903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 611483461637376850910537 458612596228032638182903)
    ·
      refine ⟨687918894342048957274355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458612596228032638182903 687918894342048957274355)
      ·
        refine ⟨1031878341513073435911533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687918894342048957274355 1031878341513073435911533)
        ·
          refine ⟨386954378067402538466825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1031878341513073435911533 386954378067402538466825)
          ·
            refine ⟨290215783550551903850119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386954378067402538466825 290215783550551903850119)
            ·
              refine ⟨435323675325827855775179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290215783550551903850119 435323675325827855775179)
              ·
                refine ⟨652985512988741783662769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435323675325827855775179 652985512988741783662769)
                ·
                  refine ⟨489739134741556337747077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652985512988741783662769 489739134741556337747077)
                  ·
                    refine ⟨91826087764041813327577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489739134741556337747077 91826087764041813327577)
                    ·
                      rfl

theorem cell22_268246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_268246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268246 prefixEnd_268246 := by exact prefixLift 268246
  have htrace : WordTrace (prefixWord ++ tailWord_268246) baseStart_268246 baseEnd_268246 := by
    simpa [prefixWord, tailWord_268246, baseEnd_268246] using wordTrace_append hprefix tailTrace_268246
  have hstable : (prefixWord ++ tailWord_268246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268246).length < 2 ^ (prefixWord ++ tailWord_268246).sum := by decide
  have hdescent : baseEnd_268246 < baseStart_268246 := by decide
  rcases family_descends (prefixWord ++ tailWord_268246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268259 : List Nat := [1, 1, 1, 6, 1, 2, 1, 5, 1, 3]
def baseStart_268259 : Nat := 118140960795 + 268259 * 2 ^ 59
def prefixEnd_268259 : Nat := 4983230072969 + 3 ^ 40 * 268259 * 2
def baseEnd_268259 : Nat := 91830537929714112752537

theorem tailTrace_268259 : CollatzResearch.WordTrace tailWord_268259 prefixEnd_268259 91830537929714112752537 := by
  unfold tailWord_268259
  simp only [CollatzResearch.WordTrace]
  refine ⟨9784209535150932834791831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6522806356767288556527887 9784209535150932834791831)
  ·
    refine ⟨14676314302726399252187747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9784209535150932834791831 14676314302726399252187747)
    ·
      refine ⟨22014471454089598878281621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14676314302726399252187747 22014471454089598878281621)
      ·
        refine ⟨1031928349410449947419451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22014471454089598878281621 1031928349410449947419451)
        ·
          refine ⟨1547892524115674921129177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031928349410449947419451 1547892524115674921129177)
          ·
            refine ⟨1160919393086756190846883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1547892524115674921129177 1160919393086756190846883)
            ·
              refine ⟨1741379089630134286270325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160919393086756190846883 1741379089630134286270325)
              ·
                refine ⟨163254289652825089337843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1741379089630134286270325 163254289652825089337843)
                ·
                  refine ⟨244881434479237634006765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163254289652825089337843 244881434479237634006765)
                  ·
                    refine ⟨91830537929714112752537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244881434479237634006765 91830537929714112752537)
                    ·
                      rfl

theorem cell22_268259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 3].length) (baseStart_268259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268259 prefixEnd_268259 := by exact prefixLift 268259
  have htrace : WordTrace (prefixWord ++ tailWord_268259) baseStart_268259 baseEnd_268259 := by
    simpa [prefixWord, tailWord_268259, baseEnd_268259] using wordTrace_append hprefix tailTrace_268259
  have hstable : (prefixWord ++ tailWord_268259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268259).length < 2 ^ (prefixWord ++ tailWord_268259).sum := by decide
  have hdescent : baseEnd_268259 < baseStart_268259 := by decide
  rcases family_descends (prefixWord ++ tailWord_268259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268285 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_268285 : Nat := 118140960795 + 268285 * 2 ^ 59
def prefixEnd_268285 : Nat := 4983230072969 + 3 ^ 40 * 268285 * 2
def baseEnd_268285 : Nat := 91839438261058711602457

theorem tailTrace_268285 : CollatzResearch.WordTrace tailWord_268285 prefixEnd_268285 91839438261058711602457 := by
  unfold tailWord_268285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9785157833056739275238309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6523438555371159516825539 9785157833056739275238309)
  ·
    refine ⟨1834717093698138614107183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9785157833056739275238309 1834717093698138614107183)
    ·
      refine ⟨2752075640547207921160775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1834717093698138614107183 2752075640547207921160775)
      ·
        refine ⟨4128113460820811881741163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2752075640547207921160775 4128113460820811881741163)
        ·
          refine ⟨6192170191231217822611745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4128113460820811881741163 6192170191231217822611745)
          ·
            refine ⟨4644127643423413366958809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6192170191231217822611745 4644127643423413366958809)
            ·
              refine ⟨3483095732567560025219107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4644127643423413366958809 3483095732567560025219107)
              ·
                refine ⟨5224643598851340037828661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3483095732567560025219107 5224643598851340037828661)
                ·
                  refine ⟨489810337392313128546437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5224643598851340037828661 489810337392313128546437)
                  ·
                    refine ⟨91839438261058711602457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489810337392313128546437 91839438261058711602457)
                    ·
                      rfl

theorem cell22_268285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_268285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_268285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_268285 prefixEnd_268285 := by exact prefixLift 268285
  have htrace : WordTrace (prefixWord ++ tailWord_268285) baseStart_268285 baseEnd_268285 := by
    simpa [prefixWord, tailWord_268285, baseEnd_268285] using wordTrace_append hprefix tailTrace_268285
  have hstable : (prefixWord ++ tailWord_268285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268285).length < 2 ^ (prefixWord ++ tailWord_268285).sum := by decide
  have hdescent : baseEnd_268285 < baseStart_268285 := by decide
  rcases family_descends (prefixWord ++ tailWord_268285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
